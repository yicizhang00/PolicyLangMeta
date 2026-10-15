//! `policylang-codegen`（CR-4）— 有界量词展开（`ALG-1`/`ALG-2`）与 SMT-LIB2 生成。
//!
//! 管道位置：`02 §1.3` 的 ③ Grounder + ④ SMT-LIB2 Codegen。
//! 输入为 [`policylang_check::CheckedSpec`]（已过 `W1`–`W12`），输出为**一目标一查询**的
//! [`EmittedQuery`] 列表（`CO-4` / `DD-6.1`）。
//!
//! 关键顺序（不可交换）：
//! ```text
//! ① 展开 ground(φ)              → 无量词（INV-G）
//! ② 收集除零义务 ALG-2          → 必须在 ③ 之前（③ 会消去 `/`）
//! ③ 除法线性化 TH-4             → 目标查询不含除法 ⇒ 不降级逻辑档位
//! ```

pub mod division;
pub mod emit;
pub mod ground;
pub mod smt_value;

use std::collections::BTreeMap;

use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::{Expr, Formula};
use policylang_ast::spec::{LogicProfile, Spec};
use policylang_check::{CheckedSpec, SymbolTable};

pub use division::{collect_div_obligations, linearize_formula};
pub use emit::{EmittedQuery, Emitter, EnumEncoding, ExpectedVerdict, SymbolDecl};
pub use ground::{ground, Grounder};

/// 域规模查询（展开器所需的最小接口，避免展开器依赖整个符号表）。
pub trait SymbolLookup {
    fn domain_size(&self, domain: &str) -> Option<u64>;
}

/// 基于符号表的实现。
pub struct TableLookup<'a>(pub &'a SymbolTable);

impl SymbolLookup for TableLookup<'_> {
    fn domain_size(&self, domain: &str) -> Option<u64> {
        self.0.domains.get(domain).map(|d| d.size)
    }
}

/// 生成选项。
#[derive(Debug, Clone)]
pub struct CodegenOptions {
    /// 是否发射边界断言 `Bnd`（`06 §6.2.4`）。
    pub emit_bounds: bool,
    /// 展开硬上限（与检查期 `G_max` 对齐，作为内存安全的第二道闸门）。
    pub hard_cap: usize,
    /// 枚举编码方式（`DD-6.2`）。默认 `Int`；`Datatype` 为保留开关。
    pub enum_encoding: EnumEncoding,
}

impl Default for CodegenOptions {
    fn default() -> Self {
        CodegenOptions {
            emit_bounds: true,
            hard_cap: 4_000_000,
            enum_encoding: EnumEncoding::default(),
        }
    }
}

/// 生成结果。
#[derive(Debug, Clone)]
pub struct CodegenOutput {
    /// 全部待求解查询（保序：按 `verify` 声明序；`mutex` 按分支对序）。
    pub queries: Vec<EmittedQuery>,
    /// 每个策略的**除零义务**（已展开，供报告与诊断展示）。
    pub obligations: BTreeMap<String, Vec<Expr>>,
    /// 除法线性化发生次数。
    pub linearizations: usize,
    /// 生成期告警。
    pub warnings: Vec<Diagnostic>,
}

/// 某策略的展开后产物。
struct GroundedPolicy {
    /// 线性化后的规则（用于 consistency / invariant / safety / refines / mutex 的规则断言）
    rules: Vec<(String, Formula)>,
    /// 线性化后的分支
    branches: Vec<(String, Formula)>,
    /// 展开后的分母表达式（`ALG-2`，**线性化之前**收集）
    divisors: Vec<Expr>,
}

/// 生成全部查询。
///
/// `header` 为脚本头部注释（含 `spec_hash` / `codegen_hash` 等审计信息，由治理层计算）。
pub fn generate(
    checked: &CheckedSpec,
    header: &str,
    opts: &CodegenOptions,
) -> Result<CodegenOutput, Diagnostic> {
    let spec: &Spec = &checked.spec;
    let tab: &SymbolTable = &checked.symbols;
    let lookup = TableLookup(tab);
    let mut warnings: Vec<Diagnostic> = Vec::new();
    let mut linearizations = 0usize;

    // ── 展开 + 线性化（按策略缓存）──
    let mut grounded: BTreeMap<String, GroundedPolicy> = BTreeMap::new();
    let ground_one = |f: &Formula| -> Result<Formula, Diagnostic> {
        let mut g = Grounder::new(&lookup, opts.hard_cap);
        let raw = g.ground(f)?;
        debug_assert!(ground::assert_quantifier_free(&raw).is_ok());
        Ok(raw)
    };

    for p in &spec.policies {
        let mut rules = Vec::new();
        let mut divisors: Vec<Expr> = Vec::new();
        for r in &p.rules {
            // ① 展开
            let raw = ground_one(&r.formula)?;
            // ② 义务（线性化前）
            divisors.extend(collect_div_obligations(&raw));
            // ③ 线性化
            let (lin, n) = linearize_formula(&raw)?;
            linearizations += n;
            rules.push((r.name.clone(), lin));
        }
        let mut branches = Vec::new();
        for b in &p.branches {
            let raw = ground_one(&b.formula)?;
            divisors.extend(collect_div_obligations(&raw));
            let (lin, n) = linearize_formula(&raw)?;
            linearizations += n;
            branches.push((b.name.clone(), lin));
        }
        grounded.insert(
            p.name.clone(),
            GroundedPolicy {
                rules,
                branches,
                divisors,
            },
        );
    }

    // 不变量
    let mut grounded_invariants: BTreeMap<String, Formula> = BTreeMap::new();
    for i in &spec.invariants {
        let raw = ground_one(&i.formula)?;
        let (lin, _) = linearize_formula(&raw)?;
        grounded_invariants.insert(i.name.clone(), lin);
    }

    // ── 逐 verify 生成查询 ──
    let mut em = Emitter::new(spec, tab, header.to_string())
        .with_enum_encoding(opts.enum_encoding);
    em.emit_bounds = opts.emit_bounds;
    let mut queries: Vec<EmittedQuery> = Vec::new();
    let mut obligations: BTreeMap<String, Vec<Expr>> = BTreeMap::new();

    // ── 声明足迹（`06 §6.2.2`）────────────────────────────────────────────────
    // 发射器按固定顺序声明**全部**全局变量与域实例字段（规范不做符号剪枝），
    // 因此每个查询的逻辑档位必须覆盖**已声明符号的排序**，而不只是公式中出现的排序。
    //
    // 反例（真实缺陷）：`cloud-deployment.plm` 的 `refines` 查询只用到 `Int`/`Bool`，
    // 但其脚本仍声明了 `IPv4`（`(_ BitVec 32)`）与 `String` 字段；若按公式足迹推出
    // `QF_LIA`，就会产出 `(set-logic QF_LIA)` + 未知排序声明的**非法脚本**。
    // 实测 z3/cvc5 对未知排序报 `(error …)` 并**静默丢弃**该声明及其依赖断言，
    // 随后仍对残余断言给出 `unsat` ⇒ 可能产出**假证明**（正面违背 `G-4` / `G-8`）。
    let mut decl_profile = LogicProfile::default();
    for d in em.decls() {
        policylang_check::logic_profile::mark_sort(&mut decl_profile, &d.sort);
    }

    let logic_of = |checked: &CheckedSpec, names: &[&str]| -> String {
        let mut p = LogicProfile::default();
        // 先并入声明足迹，再并入公式足迹（两者取并集取最保守档位）
        p.merge_from(&decl_profile);
        for n in names {
            if let Some(x) = checked.policy_profiles.get(*n) {
                p.merge_from(x);
            }
            if let Some(x) = checked.invariant_profiles.get(*n) {
                p.merge_from(x);
            }
        }
        if opts.enum_encoding == EnumEncoding::Datatype && p.uses_enum {
            // datatype 编码使逻辑离开 `QF_*` 标准集（`DD-6.2` 已登记的代价）：
            // datatype 属 `QF_UFDT` / `ALL`，故直接给出 `ALL`。
            return "ALL".to_string();
        }
        p.candidate_logic().to_string()
    };

    for vd in &spec.verifies {
        use policylang_ast::spec::VerifyKind::*;
        match &vd.kind {
            Consistency { policy } => {
                let Some(g) = grounded.get(policy) else { continue };
                let logic = logic_of(checked, &[policy.as_str()]);
                queries.push(em.consistency(policy, &g.rules, &logic));
            }
            Invariant { invariant, policy } => {
                let (Some(g), Some(inv)) =
                    (grounded.get(policy), grounded_invariants.get(invariant))
                else {
                    continue;
                };
                let logic = logic_of(checked, &[policy.as_str(), invariant.as_str()]);
                queries.push(em.invariant(policy, invariant, &g.rules, inv, &logic));
            }
            Completeness { policy } => {
                let Some(g) = grounded.get(policy) else { continue };
                let logic = logic_of(checked, &[policy.as_str()]);
                queries.push(em.completeness(policy, &[], &g.branches, &logic));
            }
            Safety { policy } => {
                let Some(g) = grounded.get(policy) else { continue };
                let logic = logic_of(checked, &[policy.as_str()]);
                obligations.insert(policy.clone(), g.divisors.clone());
                queries.push(em.safety(policy, &g.rules, &g.divisors, &logic));
            }
            Mutex { policy } => {
                let Some(g) = grounded.get(policy) else { continue };
                let logic = logic_of(checked, &[policy.as_str()]);
                for i in 0..g.branches.len() {
                    for j in (i + 1)..g.branches.len() {
                        queries.push(em.mutex_pair(
                            policy,
                            i,
                            j,
                            &g.branches[i].1,
                            &g.branches[j].1,
                            &logic,
                        ));
                    }
                }
            }
            Refines {
                new_policy,
                old_policy,
            } => {
                let (Some(gn), Some(go)) =
                    (grounded.get(new_policy), grounded.get(old_policy))
                else {
                    continue;
                };
                let logic = logic_of(checked, &[new_policy.as_str(), old_policy.as_str()]);
                queries.push(em.refines_q1(
                    new_policy,
                    old_policy,
                    &gn.rules,
                    &go.rules,
                    &logic,
                ));
                queries.push(em.refines_q2(
                    new_policy,
                    old_policy,
                    &gn.rules,
                    &go.rules,
                    &logic,
                ));
            }
        }
    }

    // 未在任何 `verify` 中被引用的策略，其义务也登记（供 `--emit-ast`/诊断完整性）
    for (name, g) in &grounded {
        obligations.entry(name.clone()).or_insert_with(|| g.divisors.clone());
    }

    // `safety_vacuous` 告警（诚实性要求，06 §6.3.5）
    for (name, ds) in &obligations {
        if ds.is_empty() {
            warnings.push(Diagnostic::warning(
                policylang_ast::codes::W_SAFETY_VACUOUS,
                format!("策略 `{name}` 不含除法：`safety` 义务集为空，判定为 `Pass` 但标注 `safety_vacuous`"),
            ));
        }
    }

    Ok(CodegenOutput {
        queries,
        obligations,
        linearizations,
        warnings,
    })
}

/// `INV-G` 的全量断言：产物中每条查询的断言均不含 `forall`/`exists` 记号。
pub fn assert_no_quantifier_tokens(scripts: &[EmittedQuery]) -> Result<(), String> {
    for q in scripts {
        for tok in ["(forall", "(exists"] {
            if q.script.contains(tok) {
                return Err(format!("INV-G 违反：查询 `{}` 含 `{tok}`", q.goal_name));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod testutil {
    use super::*;

    /// 解析 `.plm` 片段（自动补 `#lang`）。
    pub fn spec_of(body: &str) -> Spec {
        let src = if body.trim_start().starts_with("#lang") {
            body.to_string()
        } else {
            format!("#lang policylang 2\n{body}")
        };
        policylang_parser::parse_spec(&src, None)
            .unwrap_or_else(|d| panic!("测试片段应可解析：{d:?}\n---\n{src}"))
    }

    /// 展开器测试用的最小 `SymbolLookup`。
    pub struct LookupStub {
        sizes: std::collections::BTreeMap<String, u64>,
    }

    impl LookupStub {
        pub fn new(spec: &Spec) -> Self {
            LookupStub {
                sizes: spec.domains.iter().map(|d| (d.name.clone(), d.size)).collect(),
            }
        }
    }

    impl SymbolLookup for LookupStub {
        fn domain_size(&self, domain: &str) -> Option<u64> {
            self.sizes.get(domain).copied()
        }
    }
}

#[cfg(test)]
mod integration_tests {
    use super::testutil::spec_of;
    use super::*;
    use policylang_check::{check, CheckOptions};

    fn codegen(src: &str) -> (CodegenOutput, CheckedSpec) {
        let spec = spec_of(src);
        let checked = check(&spec, &CheckOptions::default())
            .unwrap_or_else(|d| panic!("应通过检查：{d:?}"));
        let out = generate(&checked, "PLM-GENERATED v2.1 test", &CodegenOptions::default())
            .unwrap_or_else(|d| panic!("应可生成：{d:?}"));
        (out, checked)
    }

    #[test]
    fn consistency_script_shape() {
        let (out, _) = codegen(
            "entity E { a: Int [min: 1, max: 3] }\ndomain D: Set[E] [size: 2]\n\
             policy P { rule R: forall s in D: s.a >= 1 }\nverify consistency of P\n",
        );
        assert_eq!(out.queries.len(), 1);
        let q = &out.queries[0];
        assert!(q.script.contains("(set-logic QF_LIA)"));
        assert!(q.script.contains("(declare-fun PL_g_") || q.script.contains("(declare-fun PL_"));
        assert!(q.script.contains(":named PLR__P__R"));
        assert!(q.script.contains("(check-sat)"));
        assert!(q.script.contains("(get-model)"));
        assert!(q.script.contains("(get-unsat-core)"));
        assert!(q.script.ends_with('\n'));
        assert!(assert_no_quantifier_tokens(&out.queries).is_ok());
    }

    #[test]
    fn bounds_are_emitted_without_named() {
        let (out, _) = codegen(
            "entity E { a: Int [min: 1, max: 3] }\ndomain D: Set[E] [size: 1]\n\
             policy P { rule R: forall s in D: s.a >= 1 }\nverify consistency of P\n",
        );
        let s = &out.queries[0].script;
        // 每个字段实例一条 `(assert (and (<= 1 X) (<= X 3)))`，且**不带** :named
        let bounds: Vec<&str> = s
            .lines()
            .filter(|l| l.contains("<= 1 PL_D_0_a") && l.contains("<= PL_D_0_a 3"))
            .collect();
        assert_eq!(bounds.len(), 1, "脚本：\n{s}");
        assert!(!bounds[0].contains(":named"));
    }

    #[test]
    fn enum_bound_is_disjunction() {
        let (out, _) = codegen(
            "entity E { k: Enum { A, B, C } }\ndomain D: Set[E] [size: 1]\n\
             policy P { rule R: forall s in D: s.k == B }\nverify consistency of P\n",
        );
        let s = &out.queries[0].script;
        assert!(s.contains("(or (= PL_D_0_k 0) (= PL_D_0_k 1) (= PL_D_0_k 2))"), "{s}");
        // 枚举成员 `B` 映射为 1（DD-6.2）
        assert!(s.contains("(= PL_D_0_k 1)"));
    }

    #[test]
    fn invariant_negation_is_labeled() {
        let (out, _) = codegen(
            "entity E { i: IPv4 }\ndomain D: Set[E] [size: 1]\n\
             policy P { rule R: forall s in D: s.i == s.i }\n\
             invariant I { forall s in D: in_cidr(s.i, \"10.0.0.0/8\") }\n\
             verify invariant I under P\n",
        );
        let q = &out.queries[0];
        assert_eq!(q.expected, ExpectedVerdict::Unsat);
        assert_eq!(q.refutation_label.as_deref(), Some("PLI__I"));
        // TH-5：bvand + 掩码常量
        assert!(q.script.contains("bvand"));
        assert!(q.script.contains("(_ bv4278190080 32)"), "{}", q.script);
        assert!(q.script.contains(":named PLI__I"));
        // 规则断言不带 :named（不污染 Core）
        let rule_line = q
            .script
            .lines()
            .find(|l| l.starts_with("(assert (") && !l.contains(":named"))
            .unwrap();
        assert!(!rule_line.contains("PLR__"));
    }

    #[test]
    fn safety_query_has_no_division_and_reports_vacuous() {
        let (out, _) = codegen(
            "entity E { a: Int }\ndomain D: Set[E] [size: 1]\n\
             policy P { rule R: forall s in D: s.a >= 1 }\nverify safety of P\n",
        );
        let q = &out.queries[0];
        assert!(q.notes.iter().any(|n| n.contains("safety_vacuous")));
        assert!(!q.script.contains("(div "));
    }

    #[test]
    fn safety_with_division_collects_obligation() {
        let (out, _) = codegen(
            "var n: Int\nvar d: Int [min: 1, max: 10]\npolicy P { rule R: n / d > 1 }\n\
             verify safety of P\n",
        );
        let q = &out.queries[0];
        // 线性化后目标查询不含除法
        assert!(!q.script.contains("(/ "), "{}", q.script);
        // 义务查询单独断言 d = 0
        assert!(q.script.contains("(= PL_g_d 0)"), "{}", q.script);
        assert_eq!(out.obligations["P"].len(), 1);
        assert_eq!(out.linearizations, 1);
    }

    #[test]
    fn linearized_ratio_keeps_lia() {
        let (out, checked) = codegen(
            "var n: Int\nvar d: Int\npolicy P { rule R: n / d > 100 }\nverify consistency of P\n",
        );
        assert_eq!(checked.logic_of_policy("P"), "QF_LIA");
        let q = &out.queries[0];
        // 线性化产生析取：(d>0 ∧ n > 100d) ∨ (d<0 ∧ n < 100d)
        assert!(q.script.contains("(< 0 PL_g_d)"), "{}", q.script);
        assert!(q.script.contains("(or "), "{}", q.script);
        assert_eq!(q.logic, "QF_LIA");
    }

    #[test]
    fn enum_bound_assert_is_not_double_parenthesised() {
        // 回归（真实缺陷）：`join("or", …)` **自带外层括号**，若再包一层会产出
        // `(assert ((or (= x 0) …)))`。实测 z3 报 `invalid function application` 并
        // **丢弃该断言** ⇒ 枚举变量退化为无界 `Int`，可能产出**假证明**。
        let (out, _) = codegen(
            "entity E { k: Enum { A, B, C }, n: Int }\ndomain D: Set[E] [size: 1]\n\
             policy P { rule R: forall s in D: s.n >= 0 }\nverify consistency of P\n",
        );
        let q = &out.queries[0];
        // 枚举成员闭包必须被发射
        assert!(q.script.contains("(= PL_D_0_k 0)"), "{}", q.script);
        // 且**不得**出现双括号
        assert!(!q.script.contains("((or"), "出现双括号：{}", q.script);
        // 良构性：括号配平
        assert_eq!(
            q.script.matches('(').count(),
            q.script.matches(')').count(),
            "括号不配平：{}",
            q.script
        );
    }

    #[test]
    fn datatype_enum_encoding_emits_type_decls_and_ctors() {
        // `DD-6.2` 的保留开关：`declare-datatype` 代数数据类型编码
        let src = "entity E { k: Enum { A, B, C }, n: Int }\ndomain D: Set[E] [size: 1]\n\
                   policy P { rule R: forall s in D: s.n >= 0 }\nverify consistency of P\n";

        // ① 默认：有界整数编码 + 成员闭包断言
        let (out_int, _) = codegen(src);
        let qi = &out_int.queries[0];
        assert!(qi.script.contains("(declare-fun PL_D_0_k () Int)"), "{}", qi.script);
        assert!(qi.script.contains("(= PL_D_0_k 0)"), "{}", qi.script);
        assert!(!qi.script.contains("declare-datatype"), "{}", qi.script);
        assert_eq!(qi.logic, "QF_LIA");

        // ② datatype：类型 + 零元构造子，且**无**成员闭包断言
        let spec = spec_of(src);
        let checked = check(&spec, &CheckOptions::default()).unwrap();
        let opts = CodegenOptions {
            enum_encoding: EnumEncoding::Datatype,
            ..CodegenOptions::default()
        };
        let out = generate(&checked, "T", &opts).unwrap();
        let q = &out.queries[0];
        assert!(
            q.script
                .contains("(declare-datatype PL_T_A_B_C ((PL_M_A) (PL_M_B) (PL_M_C)))"),
            "{}",
            q.script
        );
        assert!(
            q.script.contains("(declare-fun PL_D_0_k () PL_T_A_B_C)"),
            "{}",
            q.script
        );
        // 闭集类型 ⇒ 不发射成员闭包
        assert!(!q.script.contains("(or (= PL_D_0_k 0)"), "{}", q.script);
        // datatype 属 `QF_UFDT`/`ALL` ⇒ 档位必须离开 `QF_*`
        assert_eq!(q.logic, "ALL", "{}", q.script);
        // 类型声明必须先于使用它的常量声明
        let dt = q.script.find("declare-datatype").expect("应有类型声明");
        let df = q.script.find("(declare-fun").expect("应有常量声明");
        assert!(dt < df, "declare-datatype 必须早于 declare-fun");
    }

    #[test]
    fn datatype_encoding_uses_ctor_names_for_members() {
        let src = "entity E { k: Enum { A, B } }\ndomain D: Set[E] [size: 1]\n\
                   policy P { rule R: forall s in D: s.k == B }\nverify consistency of P\n";
        let spec = spec_of(src);
        let checked = check(&spec, &CheckOptions::default()).unwrap();
        let opts = CodegenOptions {
            enum_encoding: EnumEncoding::Datatype,
            ..CodegenOptions::default()
        };
        let out = generate(&checked, "T", &opts).unwrap();
        let q = &out.queries[0];
        // 成员引用必须变成零元构造子，而非整数下标
        assert!(q.script.contains("PL_M_B"), "{}", q.script);
        assert!(!q.script.contains("PL_D_0_k 1)"), "{}", q.script);
    }

    #[test]
    fn query_logic_covers_all_declared_sorts() {
        // 回归（真实缺陷）：发射器按 `06 §6.2.2` 声明**全部**符号，因此查询档位必须覆盖
        // **已声明符号的排序**。早期只按公式足迹推导 ⇒ 产出
        // `(set-logic QF_LIA)` + `(_ BitVec 32)` / `String` 声明的**非法脚本**，
        // 实测 z3/cvc5 报 `unknown sort` 并**静默丢弃**声明与其依赖断言（假证明风险）。
        let (out, checked) = codegen(
            "entity E { ip: IPv4, name: String [length: 1..8], a: Int }\n\
             domain D: Set[E] [size: 1]\n\
             policy P { rule R: forall s in D: s.a >= 0 }\nverify consistency of P\n",
        );
        // 公式足迹本身只有 `Int` ⇒ 检查器给出的**策略**档位仍是 `QF_LIA`
        assert_eq!(checked.logic_of_policy("P"), "QF_LIA");
        // 但**查询**档位必须升级到能覆盖 `BV` + `String` + `Int` 的组合
        let q = &out.queries[0];
        assert_eq!(q.logic, "ALL", "{}", q.script);
        assert!(q.script.contains("(set-logic ALL)"), "{}", q.script);
        assert!(q.script.contains("(_ BitVec 32)"), "{}", q.script);
        assert!(q.script.contains("() String)"), "{}", q.script);
    }

    #[test]
    fn completeness_and_mutex_pairs() {
        let (out, _) = codegen(
            "var x: Int [min: 0, max: 10]\n\
             policy P { branch A: x < 5\n branch B: x >= 5\n mutex A, B\n rule R: x >= 0 }\n\
             verify completeness of P\nverify mutex of P\n",
        );
        assert_eq!(out.queries.len(), 2); // completeness + C(2,2)=1 mutex
        let c = &out.queries[0];
        assert!(c.script.contains(":named PLC__P"));
        let m = &out.queries[1];
        assert!(m.script.contains(":named PLM__P__0__1"));
        assert!(m.script.contains("(and "));
    }

    #[test]
    fn refines_emits_two_queries() {
        let (out, _) = codegen(
            "var p: Int [min: 0, max: 65535]\n\
             policy Old { rule R: p in [1024..65535] }\n\
             policy New { rule R: p in [80..65535] }\n\
             verify New refines Old\n",
        );
        assert_eq!(out.queries.len(), 2);
        assert!(out.queries[0].goal_name.ends_with("Q1"));
        assert!(out.queries[1].goal_name.ends_with("Q2"));
        // Q1 = R_new ∧ ¬R_old ⇒ 反证断言标签指向 **Old**（06 §6.3.3）
        assert!(out.queries[0].script.contains(":named PLR__Old__OLD_NEG"));
        assert!(out.queries[1].script.contains(":named PLR__New__OLD_NEG"));
        // `in [a..b]` 展开为 `a <= x ∧ x <= b`
        assert!(out.queries[0].script.contains("(<= 1024 PL_g_p)"));
    }

    #[test]
    fn matches_all_emits_re_inter() {
        let (out, _) = codegen(
            "var s: String [length: 8..32]\n\
             policy P { rule R: s matches_all [\".*[A-Z].*\", \".*[0-9].*\"] }\n\
             verify consistency of P\n",
        );
        let q = &out.queries[0];
        assert!(q.script.contains("(str.in_re PL_g_s (re.inter "), "{}", q.script);
        assert!(q.script.contains("(re.range \"A\" \"Z\")"));
    }

    #[test]
    fn all_example_files_generate() {
        for (name, src) in [
            ("cloud", include_str!("../../../examples/cloud-deployment.plm")),
            (
                "exchange",
                include_str!("../../../examples/exchange-compliance.plm"),
            ),
            (
                "coupon",
                include_str!("../../../examples/marketing-coupon.plm"),
            ),
        ] {
            let spec = policylang_parser::parse_spec(src, Some(name))
                .unwrap_or_else(|d| panic!("{name} 应可解析：{d:?}"));
            let checked = check(&spec, &CheckOptions::default())
                .unwrap_or_else(|d| panic!("{name} 应通过检查：{d:?}"));
            let out = generate(&checked, "PLM-GENERATED v2.1", &CodegenOptions::default())
                .unwrap_or_else(|d| panic!("{name} 应可生成：{d:?}"));
            assert!(!out.queries.is_empty(), "{name} 应至少产生一条查询");
            assert!(assert_no_quantifier_tokens(&out.queries).is_ok());
        }
    }
}
