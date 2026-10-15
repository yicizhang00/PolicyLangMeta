# 02 · 系统设计说明书（SDD）

| 项 | 值 |
|---|---|
| 文档角色 | 系统设计说明书（Software Design Document），定义架构、Crate 划分、模块、数据流、接口契约与设计决策 |
| 版本 | v2.1 |
| 状态 | 冻结 |
| 上游 | `00-术语表与编号规范.md`、`01-需求规格说明书-PRD.md`、`03-形式化语义与可判定性规范.md`、`05-编译管线工程规范.md`、`06-SMT编码与求解编排规范.md`、`07-诊断审计与治理规范.md` |
| 下游 | `08-需求设计追溯矩阵.md`、`10-验收标准与测试计划.md`、`spec/grammar.pest`、`spec/report.schema.json` |
| ID 前缀 | `CR-` `IF-` `DD-` `ALG-` `SM-` `E-*`（取值与语义见 `00 §0.2`） |

> **术语与编号纪律**：本文所有 crate 名、接口契约、设计决策编号、错误码、状态值、退出码均以 `00` 与 `03` 为准。数学记号使用 Unicode（∀ ∃ ⟹ ⋀ ⋁ ∈ ≤ ≥ ≠），`ground` / `scalar_symbol` 的命名与 `03 §3.6.2` 严格一致。DSL 源文件扩展名为 `.plm`（`00 §0.6`）。

---

## 1. 系统架构

### 1.1 四层与 Crate 映射

| 层 | Crate（CR-n） | 职责摘要 | 上游依赖（Cargo） |
|---|---|---|---|
| 语言层 | `CR-1` `policylang-parser` | Pest 解析、Span 映射 | `policylang-ast` |
| 语言层 | `CR-2` `policylang-ast` | 强类型 AST、IR、展平命名（`scalar_symbol`） | 无（叶子） |
| 编译层 | `CR-3` `policylang-check` | 符号表、类型检查、`W1`–`W12` 守卫、逻辑档位推导 | `policylang-ast` |
| 编译层 | `CR-4` `policylang-codegen` | `ALG-1 ground`、`ALG-2`、除零义务、SMT-LIB2 生成 | `policylang-ast` `policylang-check` |
| 求解层 | `CR-5` `policylang-solver` | 路由器、竞速编排、响应流解析、交叉验证 | `policylang-ast` |
| 诊断 | `CR-6` `policylang-diagnostics` | S-Expr 解析、模型还原、Unsat Core 归因 | `policylang-ast` |
| 治理层 | `CR-7` `policylang-governance` | 报告生成、`proof_hash`、SARIF、Waiver 状态机 | `policylang-ast` |
| 治理层 | `CR-8` `policylang-cli` | 命令行入口、退出码、门禁集成 | 全部上层 |

> **依赖单向性（`INV-L1`）**：`policylang-ast` 为唯一叶子；`check` 不得依赖 `codegen`；`solver` 不得依赖 `governance`；`cli` 为唯一聚合点。由 `cargo tree` 静态校验。

### 1.2 Rust Workspace 目录树

```
policylang-meta/
├── Cargo.toml                       # [workspace] resolver = "2"
├── policylang.toml                  # IF-4 项目配置
├── policylang.lock                  # IF-5 求解器版本锁
├── crates/
│   ├── policylang-ast/         # CR-2 强类型 AST 与展平命名（叶子）：src/{lib,spec,formula,naming,span}.rs
│   ├── policylang-parser/      # CR-1 Pest 解析与 Span 映射：src/{lib,parse,pair_map}.rs + grammar.pest
│   ├── policylang-check/       # CR-3 符号表/类型检查/可判定性守卫/Logic 探针：src/{symbol_table,typecheck,guardian,logic_profile,budget}.rs
│   ├── policylang-codegen/     # CR-4 Grounder 与 SMT-LIB2 生成器：src/{ground,division,emit,smt_value}.rs
│   ├── policylang-solver/      # CR-5 路由器/竞速编排/交叉验证：src/{router,orchestra,response,crossval,probe}.rs
│   ├── policylang-diagnostics/ # CR-6 S-Expr 解析/Model 还原/Core 归因：src/{sexpr,model,core,render}.rs
│   ├── policylang-governance/  # CR-7 报告/proof_hash/SARIF/Waiver：src/{report,hashing,sarif,waiver,gate}.rs
│   └── policylang-cli/         # CR-8 命令行工具与 CI 门禁入口：src/{main,cmd_verify,cmd_check,cmd_probe,exit}.rs
├── spec/{grammar.pest, report.schema.json}
├── lean/PolicylangProof/{Grounder,Division,Cidr,Regex,Encoding}.lean   # 核心算子 Lean 4 保序证明
├── tests/{integration/, benchmarks/}                                    # 端到端测试与 Criterion 基准
└── examples/{cloud-deployment,exchange-compliance,marketing-coupon}.plm # 三大领域验收案例
```

> **命名修正（`09 §9.2 B-22` / `00 §0.5`）**：上游 `policylang-Check` 修正为 `policylang-check`；示例扩展名由 `.pl` 修正为 `.plm`；`└──marketing-coupon.pl` 补空格为 `└── marketing-coupon.plm`。

### 1.3 端到端数据流

```
  .plm 源码 (UTF-8)  ┄ 可观测中间产物：Diagnostic[]（Line/Col）
      │
 ① Parser (CR-1)            IN: &str       OUT: Result<Spec, Vec<Diagnostic>>
      │  产物：ast.json（IF-2）；Untyped AST（含 Span）
 ② Type & Decidability Check (CR-3)
      │  IN: &Spec  OUT: Result<CheckedSpec, Vec<Diagnostic>>
      │  产物：LogicProfile（QF_BV/QF_SLIA/QF_LIA/…）、G(φ)、W 违例清单
 ③ Grounder (CR-4, ALG-1)   IN: &CheckedSpec   OUT: QfFormula
      │  产物：无量词 IR（INV-G）、除零义务集（ALG-2）、:named 副作用表
 ④ SMT-LIB2 Codegen (CR-4)  IN: &QfFormula  OUT: SmtScript
      │  产物：.smt2（set-logic、Bnd、:named、get-model/core）
 ⑤ Theory-Aware Orchestra (CR-5)  IN: SmtScript  OUT: SolverVerdict
      │  产物：胜出求解器名、耗时、原始 S-Expr（sat model / unsat core）
 ⑥ Diagnostics Translator (CR-6)  IN: SolverVerdict  OUT: Vec<CheckDiagnostic>
      │  产物：BusinessCounterexample / RuleConflictSpan[]
 ⑦ Governance & CI Gate (CR-7/CR-8)
         IN: CheckDiagnostic[]  OUT: VerificationReport + ExitCode
         产物：report.json（IF-3）、report.sarif、proof_hash、退出码 0–4
```

---

## 2. 模块设计
> **依赖关系**：各 crate 的 Cargo 依赖见 §1.1 表；本节仅列职责、公开 API 签名、关键数据结构与单元测试要点。
### 2.1 `policylang-ast`（CR-2，叶子 crate）

- **职责**：定义强类型 AST、逻辑档位枚举、展平命名函数；是全部 crate 的公共数据契约。
```rust
// src/naming.rs —— 单一命名实现（INV-L2，03 §3.6.2）
pub fn scalar_symbol(domain: &str, index: usize, field: &str) -> String;
pub fn domain_instance(domain: &str, index: usize) -> String;
fn escape(s: &str) -> String; // 非 [A-Za-z0-9_] 字符 → 后缀 _u 加四位十六进制

// src/spec.rs
pub use crate::spec::{Spec, EntityDecl, FieldDecl, DomainDecl, VarDecl,
                      PolicyDecl, RuleDecl, InvariantDecl, BranchDecl, VerifyDecl};
pub use crate::span::Span;
```
- **关键数据结构**：`Spec`（实体/域/变量/策略/不变量/分支/验证目标集合）、`Sort`（`Int|Real|Bool|Str|BV(u32)|Enum(Vec<String>)`）、`Formula`（含 `Forall{.. distinct: bool}` / `Exists{.. distinct: bool}`）、`VerifyDecl`（五式）、`LogicProfile`。
- **单元测试要点**：`scalar_symbol` 的**单射性**（含字段名下划线、保留字 `div`/`to_real` 的规避）；AST JSON 往返无损；`Sort` 相等判定。
### 2.2 `policylang-parser`（CR-1）

- **职责**：以 Pest 解析 `.plm`，产出 `Spec` 并携带 `Span`；把 Pest 的 `Error` 归一为 `Diagnostic`。
```rust
use std::path::Path;
use policylang_ast::{Spec, Span};

pub struct Diagnostic { pub code: String, pub message: String, pub span: Option<Span> }
pub fn parse_spec(src: &str) -> Result<Spec, Vec<Diagnostic>>;
pub fn parse_file(path: &Path) -> Result<Spec, Vec<Diagnostic>>;
```
- **关键数据结构**：`PairMap`（`Rule` 名 → AST 构造器，并填充 `Span`）。
- **单元测试要点**：`iff` 最低优先级解析（`03 §3.4.3` 补入 `f_iff`）；布尔原子 `bool_atom`（`T-BOOL-ATOM`）；`forall x̄ in D distinct:` 修饰解析；错误定位到行列。
### 2.3 `policylang-check`（CR-3）

- **职责**：符号表绑定、类型检查（`T-*` 规则）、`W1`–`W12` 可判定性守卫、`G(φ)` 静态预算、逻辑档位推导。
```rust
use policylang_ast::{Spec, Formula};

pub enum LogicId { QfLia, QfLra, QfBv, QfSlia, Combo(String), QfNra }
pub struct CheckOptions { pub max_groundings: u64, pub allow_nonlinear: bool }
pub struct CheckedSpec { pub spec: Spec, pub logic: LogicId, pub gf: u64, pub order: Vec<String> }

pub fn check(spec: &Spec, opts: &CheckOptions) -> Result<CheckedSpec, Vec<Diagnostic>>;
pub fn deduce_logic(fp: &TheoryFootprint) -> LogicId;
pub fn grounding_cost(f: &Formula, domains: &DomainTable) -> u64; // G(φ)，O(|φ|)，不展开
pub fn is_const(e: &Expr) -> bool;
pub fn lin_mul(a: &Expr, b: &Expr) -> bool;      // isConst(a) ∨ isConst(b)，03 §3.4.1
pub fn lin_side_cond_div(denom: &Expr) -> bool;  // 除/模要求常量除数
```
- **关键数据结构**：`SymbolTable`（`(BindVar ∪ GVar ∪ (BindVar × Field)) ⇀ Sort`）、`TheoryFootprint {uses_int, uses_real, uses_bv, uses_str, uses_reglan}`、`Diagnostic`。
- **单元测试要点**：`W8` **两独立侧条件**（乘 vs 除，修复上游漏检 `2 / x`）；`W11` 预算诊断 JSON 结构（`03 §3.9.2`）；`W9` 正则子语言判定；`N-4` 排序隐式提升拒绝。
### 2.4 `policylang-codegen`（CR-4）

- **职责**：`ALG-1 ground`（含 `DET-1`/`FOLD-1`/`FOLD-2`/`CSE-1`/`ALG-1-P`）、`ALG-2 collect_div_obligations`、`TH-4` 除法线性化、SMT-LIB2 文本生成与 `:named` 注入。
```rust
use policylang_ast::{Formula, Term};

pub struct GroundEnv { pub binds: std::collections::BTreeMap<String, (String, usize)> }
pub enum QfFormula { And(Vec<QfFormula>), Or(Vec<QfFormula>), Not(Box<QfFormula>),
                     Implies(Box<QfFormula>, Box<QfFormula>), Iff(Box<QfFormula>, Box<QfFormula>), Atom(Atom) }
pub struct SmtScript { pub logic: String, pub text: String, pub named: Vec<(String, String)> }

pub fn ground(f: &Formula, env: &GroundEnv, delta: &DomainTable) -> QfFormula;      // ALG-1
pub fn collect_div_obligations(p: &QfFormula) -> Vec<Term>;                          // ALG-2
pub fn linearize_division(a: &Term, b: &Term, c: &Term) -> Result<QfFormula, Diagnostic>; // TH-4
pub fn emit_query(logic: &str, spec: &CheckedSpec, goal: &VerifyDecl) -> SmtScript;
```
- **关键数据结构**：`QfFormula`（无量词 IR，`INV-G`）、`Atom`（含 CIDR/正则原子）、`SmtScript`（带 `named` 副作用表）。
- **单元测试要点**：`TH-1` 保序性质测试（随机 `φ` 上 `⟦ground(φ)⟧ = ⟦φ⟧`）；`DET-1` 字典序与 `query_hash` 复算稳定；`ALG-1-P` 部分出现剪枝；`FOLD-1` 影子记录保留。
### 2.5 `policylang-solver`（CR-5）

- **职责**：逻辑归档路由、能力探测（`ALG-3`）、进程级竞速编排、响应流解析、交叉验证。
```rust
use std::time::Duration;

pub struct SolverBackend { pub name: String, pub cmd: String, pub args: Vec<String>,
                           pub bin_sha256: String, pub version: String }
pub enum SolverVerdict {
    Sat { solver: String, model_sexpr: String, time_ms: u64 },
    Unsat { solver: String, core_sexpr: String, time_ms: u64 },
    Unknown { solver: String, reason: String, time_ms: u64 },
}

pub async fn probe_logic(backend: &SolverBackend, logic: &str) -> bool;   // ALG-3
pub async fn solve_race(pool: &[SolverBackend], logic: &str, script: &str,
                        timeout: Duration) -> SolverVerdict;
pub fn parse_response_stream(stdout: &str) -> Result<SolverVerdict, ParseError>;
pub fn cross_validate(model: &str, script: &str, ref_eval: &dyn ModelEvaluator) -> Result<(), CrossvalError>;
```
- **关键数据结构**：`CapabilityMatrix`（`logic × backend → {Native|UnknownRisk|Unsupported}`）、`Pool`（按逻辑档位筛出的后端列表）。
- **单元测试要点**：`parse_response_stream` 对多行 `sat`/`unsat`/`unknown`/`(error …)` 的**序列化**解析（非按行）；`cross_validate` 在模型篡改时必报 `CrossvalError`。
### 2.6 `policylang-diagnostics`（CR-6）

- **职责**：S-Expr 词法/语法解析、模型逆映射为业务视图、Unsat Core 归因、终端彩色渲染。
```rust
use std::collections::HashMap;

pub struct BusinessCounterexample {
    pub entity_snapshots: HashMap<String, HashMap<String, String>>,
    pub summary: String, pub remediation_suggestion: String,
}
pub struct RuleConflictSpan { pub rule_name: String, pub line: usize }

pub fn decompile_model(model: &str, naming: &NamingContext) -> BusinessCounterexample;
pub fn localize_core(core: &str, naming: &NamingContext) -> Vec<RuleConflictSpan>;
pub fn sexpr_parse(text: &str) -> Result<Sexpr, SexprError>;
```
- **关键数据结构**：`Sexpr`（`Atom` / `List`）、`NamingContext`（`scalar_symbol` 的逆解析表：`(domain, index, field)`）。
- **单元测试要点**：`BV(32)` → 点分十进制；`Enum` → 成员名；`Real` → `num/den` 精确有理数（**严禁** IEEE-754）；空核须报 `E-EMPTY-CARRIER`。
### 2.7 `policylang-governance`（CR-7）

- **职责**：报告装配、`proof_hash` / `attestation_hash` 计算、SARIF 输出、合并格 `overall_status`、Waiver 状态机。
```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CheckStatus { Pass, Fail, UnknownReviewRequired, Waived, Error }

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationReport {
    pub schema_version: String, pub timestamp: String, pub overall_status: CheckStatus,
    pub logic_used: String, pub checks: Vec<CheckDiagnostic>,
    pub proof_hash: String, pub attestation_hash: String,
}

pub fn overall_status(checks: &[CheckDiagnostic]) -> CheckStatus;   // 合并格 join
pub fn proof_hash(spec_bytes: &[u8], query: &str, verdict: &str) -> String;
pub fn to_sarif(report: &VerificationReport) -> SarifLog;
pub fn apply_waivers(checks: &mut [CheckDiagnostic], waivers: &[Waiver], now: &str);
pub fn exit_code(status: CheckStatus) -> u8;
```
- **关键数据结构**：`CheckDiagnostic`、`Waiver { owner, approver, expires_at, rule_name }`、`SarifLog`。
- **单元测试要点**：合并格全序（`Error ⊐ Fail ⊐ UnknownReviewRequired ⊐ Waived ⊐ Pass`）；`proof_hash` 复算一致（`TH-10`）；过期豁免失效。
### 2.8 `policylang-cli`（CR-8）

- **职责**：命令行解析、子命令编排、退出码映射、CI 集成。
```rust
use std::process::ExitCode;
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "policylang", version)]
struct Cli { #[command(subcommand)] cmd: Cmd }

#[derive(Subcommand)]
enum Cmd {
    Verify { spec: Vec<String>, timeout_ms: u64, max_groundings: u64, output: Option<String>, sarif: bool },
    Check  { spec: Vec<String> },
    Probe,
    Explain { spec: String },
}

fn main() -> ExitCode;
fn run(cli: Cli) -> u8;   // 返回 0–4
```
- **关键数据结构**：`Cmd` 子命令枚举；`exit::map_status_to_code`。
- **单元测试要点**：五码制映射（`AC-4`=3、`AC-6`=2）；`--max-groundings` 与 `--timeout` 默认值。

---

## 3. 语言层设计

> **不重复文法**：完整文法见 `spec/grammar.pest` 与 `04-DSL语言参考手册.md`；数学定义见 `03 §3.2`–§3.5。此处仅给 AST 概要。

```rust
use policylang_ast::Span;
pub struct Spec {
    pub entities: Vec<EntityDecl>, pub domains: Vec<DomainDecl>, pub variables: Vec<VarDecl>,
    pub policies: Vec<PolicyDecl>, pub invariants: Vec<InvariantDecl>,
    pub branches: Vec<BranchDecl>,      // FR-15：completeness 目标的输入
    pub verifications: Vec<VerifyDecl>, // FR-3：五式
}
pub enum Sort { Int, Real, Bool, Str, BV(u32), Enum(Vec<String>) }
pub enum RangeConstraint { Numeric { min: i128, max: i128 }, Length { min: usize, max: usize } }
pub enum Formula {
    Predicate { left: Expr, op: CmpOp, right: Expr },
    MatchesAll { expr: Expr, patterns: Vec<String> },   // FR-14
    InCidr { expr: Expr, cidr: String },                // TH-5
    Unique { domain: String, field: String },           // FR-15
    BoolAtom(Expr),                                     // T-BOOL-ATOM
    And(Vec<Formula>), Or(Vec<Formula>), Not(Box<Formula>),
    Implies(Box<Formula>, Box<Formula>), Iff(Box<Formula>, Box<Formula>),
    Forall { vars: Vec<String>, domain: String, distinct: bool, body: Box<Formula> },
    Exists { vars: Vec<String>, domain: String, distinct: bool, body: Box<Formula> },
}
pub enum VerifyDecl {
    Consistency { policy: String, span: Span },
    Invariant { invariant: String, policy: String, span: Span },
    Refines { new_policy: String, old_policy: String, span: Span },
    Completeness { policy: String, branches: Vec<String>, span: Span },
    Safety { policy: String, span: Span },
}
```

> **AST 纪律**：`Real` 常量以 `i128` 的 `num/den` 对存储（`03 §3.2.3 N-1`）；`Forall`/`Exists` 携带 `distinct` 标志，`distinct` 语义**必须显式声明**，编译器不得自动插入（`03 §3.5.2`）；`BoolAtom` 的存在使 `s1.uses_db and s2.uses_db` 可上升为公式（修复上游文法自相矛盾）。

### 3.4 语义模型元素（`SM-1` ~ `SM-5`）

> 本小节把 `03` 数学内核中反复出现的语义概念**编号化**为 `SM-n` 语义模型元素（前缀声明见 `00 §0.2.2`），供跨文档稳定引用。

| ID | 名称 | 定义 | 权威出处 |
|---|---|---|---|
| `SM-1` | 展平符号命名 | `scalar_symbol(D,i,f) = "PL_" + escape(D) + "_" + dec(i) + "_" + escape(f)`，`escape` 把非 `[A-Za-z0-9_]` 字符替换为 `_uXXXX`；保证单射 | `03 §3.2.4` |
| `SM-2` | 边界断言 `Bnd` | 全部受限载体之特征谓词的全合取；**不带 `:named` 标签**（`DD-3.1`） | `03 §3.2.6`、`06 §6.2.4` |
| `SM-3` | 状态空间 `M` | 全部展平标量与全局变量的取值之笛卡尔积 `∏ D_{σ,c}` | `03 §3.2.5` |
| `SM-4` | 有界量词语义 | `AX-Q-INDEP`：默认全笛卡尔积（含对角项）；`distinct` 修饰切换为单射枚举 `Inj` | `03 §3.5.2` |
| `SM-5` | 除法全域性义务 | `obl(P) = ⟨b₁,…,b_k⟩`，由 `ALG-2` 从 AST 前序遍历收集全部除/模节点的分母 | `03 §3.11.2` |

---

## 4. 编译层设计

### 4.1 `ALG-1 ground`（有界量词单态化展开）

```rust
use policylang_ast::{Formula, GroundEnv, Term, Expr};

/// 03 §3.6 ALG-1：输出不含 Forall/Exists（不变量 INV-G，由 TH-2 保证）。
pub fn ground(f: &Formula, env: &GroundEnv, delta: &DomainTable) -> QfFormula {
    match f {
        Formula::Forall { vars, domain, distinct, body } => {
            let n = delta.size(domain);                 // W3 保证 n ≥ 1
            let occ = occurring_vars(body, vars);       // ALG-1-P 部分出现剪枝
            if occ.is_empty() { return ground(body, env, delta); } // 死变量剪枝
            let tuples = if *distinct { injective_tuples(n, occ.len()) }   // Inj(idx(D),k)，N!/(N-k)!
                         else { lexicographic_tuples(n, occ.len()) };       // DET-1：Fin N 字典序
            let mut acc: Vec<QfFormula> = Vec::new();
            for idx in tuples {
                acc.push(ground(body, &env.bind_all(vars, domain, &idx), delta));
            }
            QfFormula::And(fold_constants(acc))         // FOLD-1 + FOLD-2；⋀∅ ≡ ⊤
        }
        Formula::Exists { vars, domain, distinct, body } =>
            ground_exists(vars, domain, *distinct, body, env, delta),      // 同形返回 Or(..)；⋁∅ ≡ ⊥
        Formula::And(l) => QfFormula::And(l.iter().map(|x| ground(x, env, delta)).collect()),
        Formula::Or(l)  => QfFormula::Or (l.iter().map(|x| ground(x, env, delta)).collect()),
        Formula::Not(x) => QfFormula::Not(Box::new(ground(x, env, delta))),
        Formula::Implies(a, b) => QfFormula::Implies(bx(ground(a, env, delta)), bx(ground(b, env, delta))),
        Formula::Iff(a, b)     => QfFormula::Iff(bx(ground(a, env, delta)), bx(ground(b, env, delta))),
        Formula::Predicate { .. } | Formula::MatchesAll { .. } | Formula::InCidr { .. }
        | Formula::Unique { .. } | Formula::BoolAtom(..) => QfFormula::Atom(atom_of(f, env)),
    }
}

fn bx(f: QfFormula) -> Box<QfFormula> { Box::new(f) }
fn bx_term(t: Term) -> Box<Term> { Box::new(t) }

/// 03 §3.6.2：项层重命名，严格复用 policylang-ast::scalar_symbol（INV-L2）。
fn rename_expr(e: &Expr, env: &GroundEnv) -> Term {
    match e {
        Expr::FieldAccess { instance, field } => {
            let (d, i) = env.lookup(instance); Term::Sym(policylang_ast::scalar_symbol(d, i, field))
        }
        Expr::Binary { left, op, right } =>
            Term::Bin(bx_term(rename_expr(left, env)), op.clone(), bx_term(rename_expr(right, env))),
        other => Term::from(other),
    }
}
```

> **优化清单（与上游 v2.0 的差异）**：`DET-1`（字典序、纯函数、`query_hash` 可复算）、`FOLD-1`（常量折叠 + `false` 短路保留 `:named` 影子记录）、`FOLD-2`（α-等价去重，`∀s₁,s₂` 由 N² 降为 N(N+1)/2）、`CSE-1`（`str.in_re` 项提取为 `(let …)`）、`ALG-1-P`（部分出现剪枝）。上游 `ground_formula` 五项皆缺（`09 §9.2 B-8`）。

### 4.2 `ALG-2 collect_div_obligations`（除零义务生成）

```rust
/// 03 §3.11.2 ALG-2：前序遍历 ground(P) 收集每个 Div/Mod 的分母子式（顺序确定性）。
pub fn collect_div_obligations(p: &QfFormula) -> Vec<Term> {
    let mut out: Vec<Term> = Vec::new();
    walk_preorder(p, &mut |node| {
        if let QfFormula::Atom(Atom::Bin { op: Arith::Div | Arith::Mod, right, .. }) = node {
            out.push(right.clone());   // b_j：分母/模数
        }
    });
    out   // k = 0 ⇒ ⋀∅ ≡ ⊤ ⇒ 报告标注 safety_vacuous: true（03 §3.5.3）
}
// safety 查询本身不含除法（03 §3.11.5），故不因除法而降级：
//   (assert Bnd) (assert R_P) (assert (or (= b₁ 0) … (= b_k 0))) (check-sat)   ; UNSAT ⇒ PASS
```

### 4.3 逻辑档位推导

```rust
pub fn deduce_logic(fp: &TheoryFootprint) -> LogicId {
    match (fp.uses_str, fp.uses_bv, fp.uses_int, fp.uses_real) {
        (true,  false, true,  false) => LogicId::QfSlia,
        (false, true,  false, false) => LogicId::QfBv,
        (false, false, true,  false) => LogicId::QfLia,
        (false, false, false, true)  => LogicId::QfLra,
        (false, true,  true,  false) => LogicId::Combo("QF_BVLIA".into()), // TH-3a：须探测
        (false, false, true,  true)  => LogicId::Combo("QF_LIRA".into()),
        _ => LogicId::Combo("ALL".into()),
    }
}
```

> **诚实边界（`TH-3a` / `DD-3.2`）**：`Combo(..)` 档位**不宣称**可判定（`03 §3.10.3`）。硬编码组合逻辑名在 SMT-LIB 中的收录与求解器支持存在版本差异，故 `Combo` 必须经 `ALG-3 probe_logic` 实测：探测通过视为「本环境可判定」，探测失败标记 `UNKNOWN_RISK`，门禁在该目标上**只接受 `UnknownReviewRequired`**。

### 4.4 非线性守卫（两独立侧条件）

```rust
/// 03 §3.4.1：乘法侧条件 LinMul(a,b) ≜ isConst(a) ∨ isConst(b)；
/// 除法/取模侧条件独立：要求除数为常量且 ⟦b⟧ ≠ 0。
pub fn guard_arith(e: &Expr, allow_nonlinear: bool, diags: &mut Vec<Diagnostic>) {
    if let Expr::Binary { left, op, right } = e {
        match op {
            Op::Mul if !is_const(left) && !is_const(right) =>
                diags.push(Diagnostic::error("E-NONLINEAR",
                    "非线性算术（两个非常量操作数相乘）落入 QF_NIA，禁止", None)),
            // 修复上游漏检 2 / x（左侧常量、右侧变量）
            Op::Div | Op::Mod if !is_const(right) =>
                diags.push(Diagnostic::error("E-NONLINEAR",
                    "除数必须为常量（floor 除法不可线性化，命题 3.11.1）", None)),
            Op::Div if allow_nonlinear => { /* 仅 --allow-nonlinear 放行，降为 QF_NRA */ }
            _ => {}
        }
    }
}
```

### 4.5 声明拓扑排序

```rust
use std::collections::HashMap;

/// 03 §3.3.1 D-1：域依赖实体（D→E）、验证目标依赖策略/不变量（V→{S,V}）。
/// 存在环 ⇒ E-CYCLIC-DECL。声明书写顺序不受约束，允许前向引用。
pub fn topo_order(decls: &[Decl]) -> Result<Vec<String>, Diagnostic> {
    let (mut indeg, mut adj): (HashMap<String, usize>, HashMap<String, Vec<String>>)
        = (HashMap::new(), HashMap::new());
    for d in decls {
        indeg.entry(d.name().into()).or_insert(0);
        for dep in d.deps() {
            adj.entry(dep).or_default().push(d.name().into());
            *indeg.entry(d.name().into()).or_insert(0) += 1;
        }
    }
    let mut queue: Vec<String> = indeg.iter().filter(|(_, &n)| n == 0).map(|(k, _)| k.clone()).collect();
    let mut order = Vec::new();
    while let Some(n) = queue.pop() {
        order.push(n.clone());
        for m in adj.get(&n).into_iter().flatten() {
            let e = indeg.get_mut(m).unwrap(); *e -= 1; if *e == 0 { queue.push(m.clone()); }
        }
    }
    if order.len() != indeg.len() { return Err(Diagnostic::error("E-CYCLIC-DECL", "声明依赖存在环", None)); }
    Ok(order)
}
```

### 4.6 预算守卫与退化语义

- `G(φ)` 由 `grounding_cost` 在 `O(|φ|)` 内静态算出（不展开），判定 `G(φ) > G_max` ⇒ `E-GROUNDING-BUDGET`（`W11`）。
- 诊断 JSON 含「量词嵌套路径 → 各层 `N` 与 `k'` → 乘性贡献 → 建议」，`distinct` 修饰以 `"distinct": true` 标注（`03 §3.9.2`）。
- 退化语义按 `03 §3.5.3`：`⋀∅ ≡ ⊤`、`⋁∅ ≡ ⊥`、`matches_all []` 恒真、`safety` 无除法时 `safety_vacuous: true`、`N = 0` 与空载体一律 `E-EMPTY-CARRIER`。

---

## 5. 求解层设计

### 5.1 理论感知路由器（`router.rs`）

- 输入 `LogicId` 与 `CapabilityMatrix`，输出**可用后端列表**（`Pool`）。
- 规则：`QfSlia` → {Z3, CVC5}（屏蔽 Bitwuzla）；`QfBv` → {Bitwuzla, Z3, CVC5} 且 Bitwuzla 优先；`Combo(..)` 且探测失败 → 空池 ⇒ `E-SOLVER-MISSING`（退出码 4），或降级为「只接受 `UnknownReviewRequired`」。

### 5.2 竞速编排（`orchestra.rs`，首胜即止）

```rust
use tokio::{io::AsyncWriteExt, process::Command, task::JoinSet};
use std::{process::Stdio, time::{Duration, Instant}};

pub async fn solve_race(pool: &[SolverBackend], _logic: &str, script: &str,
                        timeout: Duration) -> SolverVerdict {
    let start = Instant::now();
    let mut joinset: JoinSet<(String, String)> = JoinSet::new();
    for b in pool {
        let (cmd, args, q) = (b.cmd.clone(), b.args.clone(), script.to_string());
        joinset.spawn(async move {
            let mut child = Command::new(&cmd).args(&args)
                .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null())
                .kill_on_drop(true)              // 兜底：任务被 drop 时强杀子进程
                .spawn().expect("spawn solver");
            if let Some(mut stdin) = child.stdin.take() { let _ = stdin.write_all(q.as_bytes()).await; }
            let out = child.wait_with_output().await.expect("wait solver");
            (cmd, String::from_utf8_lossy(&out.stdout).to_string())
        });
    }
    let raced = async {
        while let Some(Ok((_name, stdout))) = joinset.join_next().await {
            if let Ok(v) = parse_response_stream(&stdout) {
                if matches!(v, SolverVerdict::Sat { .. } | SolverVerdict::Unsat { .. }) {
                    return with_time(v, start.elapsed());   // 首胜
                }
            }
        }
        SolverVerdict::Unknown { solver: "all".into(), reason: "all unknown/failed".into(), time_ms: 0 }
    };
    // 关键：AC-5 要求「P99 ≤ 50ms 回收」，须用 shutdown().await 等待子进程退出（tokio ≥ 1.40）
    let verdict = match tokio::time::timeout(timeout, raced).await {
        Ok(v) => v,
        Err(_) => SolverVerdict::Unknown { solver: "timeout".into(),
                     reason: format!("exceeded {timeout:?}"), time_ms: timeout.as_millis() as u64 },
    };
    joinset.shutdown().await;   // 中止全部任务并等待其完成回收（不遗留 OS 子进程）
    verdict
}
```

### 5.3 响应流解析（`response.rs`）

- **不按行**，而按 SMT-LIB 响应**序列**解析：跳过 `success`/`unsupported` 与注释，捕获首个 `sat`/`unsat`/`unknown`，并累积其后 `( ( … ) )` / `( … )` 模型或核块，直到括号平衡。
- `(error "…")` 必须与 `unknown` 区分：`(error "unsupported logic")` 触发能力矩阵降级（`UNKNOWN_RISK`）。

```rust
pub fn parse_response_stream(stdout: &str) -> Result<SolverVerdict, ParseError> {
    let (mut kind, mut buf): (Option<&str>, String) = (None, String::new());
    for tok in tokenize_smt(stdout) {          // tokenize_smt 跳过 success/comment 并处理括号平衡
        match tok.as_str() {
            "sat" | "unsat" | "unknown" if kind.is_none() => kind = Some(tok.as_str().leak()),
            _ => if kind.is_some() { buf.push_str(&tok); buf.push(' '); }
        }
    }
    match kind {                               // (error "…") 不匹配任一分支，落入 NoVerdict 由上层区分
        Some("sat")     => Ok(SolverVerdict::Sat     { solver: String::new(), model_sexpr: buf, time_ms: 0 }),
        Some("unsat")   => Ok(SolverVerdict::Unsat   { solver: String::new(), core_sexpr:  buf, time_ms: 0 }),
        Some("unknown") => Ok(SolverVerdict::Unknown { solver: String::new(), reason: buf, time_ms: 0 }),
        _ => Err(ParseError::NoVerdict),
    }
}
```

### 5.4 交叉验证（`crossval.rs`）

- SAT 时把模型代入**独立参考求值器**（`ModelEvaluator`，逐位按精确算术重算全部断言）或次优求解器复核；不一致 ⇒ `E-CROSSVAL-MISMATCH`（退出码 4）。
- 禁用 IEEE-754 参与重放（`03 §3.2.3 N-1`）：`Real` 一律以 `num/den` 精确有理数比较。

### 5.5 核心最小化（`core.rs`，可选）

- `(get-unsat-core)` 返回的核**不保证最小**。`--minimize-core` 时执行 deletion-based 最小化：逐一移除 `:named` 断言并重查 UNSAT，复杂度 `O(A)` 次求解（`03 §3.10.4`），受独立预算约束。
- `Bnd(S)` 不带 `:named`（`DD-3.1`），故核不被建模假设污染；若核为空而查询 UNSAT，报告 `E-EMPTY-CARRIER`（`03 §3.2.6`）。

---

## 6. 治理层设计

### 6.1 报告装配与合并格

- `overall_status = join{ status(c) | c ∈ checks }`，偏序 `Error ⊐ Fail ⊐ UnknownReviewRequired ⊐ Waived ⊐ Pass`（`00 §0.4.2`）。
- 报告字段遵循 `spec/report.schema.json`（IF-3），`schema_version: "1.0"`，只增字段。

### 6.2 `proof_hash` 与 `attestation_hash`

```rust
use sha2::{Digest, Sha256};

/// 03 §3.14 / 07 §7.5 TH-10：proof_hash = SHA-256(规范哈希 ‖ 查询哈希 ‖ 判定结果)
pub fn proof_hash(spec_bytes: &[u8], query: &str, verdict: &str) -> String {
    let mut h = Sha256::new();
    h.update(Sha256::digest(spec_bytes));           // 规范哈希：源码字节
    h.update(Sha256::digest(query.as_bytes()));     // 查询哈希：SMT-LIB2 文本（DET-1 保证可复算）
    h.update(verdict.as_bytes());
    hex::encode(h.finalize())
}
```

- `attestation_hash` 额外覆盖胜出求解器名、耗时、宿主信息（`00 §0.3.2`）。

### 6.3 退出码映射（五码制）

| `overall_status` | CLI 退出码 | 名称 |
|---|---|---|
| `Pass` / `Waived` | `0` | PASS |
| `Fail` | `1` | VERIFICATION_FAILED |
| `UnknownReviewRequired` | `2` | UNKNOWN_REVIEW_REQUIRED |
| `Error`（编译/守卫阻断，`E-UNVERIFIABLE` 家族） | `3` | COMPILE_ERROR |
| `Error`（求解器缺失/版本不符、IO、交叉验证不一致） | `4` | INTERNAL_ERROR |

> **注意**：`3` 与 `4` 同为 `Error` 状态，须由 `Diagnostic.code` 区分（`W*`/`E-NONLINEAR`/`E-GROUNDING-BUDGET`/`E-REGEX-*`/`E-CIDR-*`/`E-PARSE` 等 → 3；`E-SOLVER-*`/`E-CROSSVAL-MISMATCH`/`E-REPORT-IO` → 4）。

### 6.4 Waiver 与人工评审状态机

```
Fail ──(有效豁免: owner/approver/expires_at)──► Waived ──(到期)──► Fail
  │
  ├─(无豁免)─► 人工评审 ─(通过并记 Waiver)─► Waived ；─(拒绝)─► Fail
  └─ UnknownReviewRequired（全求解器超时/unknown）──► ExitCode = 2（严禁视为 Pass）
```

- `Waiver` 必含 `owner` / `approver` / `expires_at`；过期即失效，不参与合并格。
- 豁免与评审结论写入报告并纳入 `proof_hash` 存证链（`FR-18` / `FR-13`）。

---

## 7. 接口契约

### IF-1 CLI 命令行

```
policylang verify <spec...> [--timeout 3000ms] [--max-groundings 1000000]
                  [--output report.json] [--sarif] [--minimize-core] [--allow-nonlinear]
policylang check  <spec...>
policylang probe
policylang explain <spec>
```

- 退出码 `0`–`4`（§6.3）。`--allow-nonlinear` 仅将档位降为 `QF_NRA`，该目标强制 `UnknownReviewRequired`（不承诺可判定）。

### IF-2 AST JSON（`ast_schema_version: "1.0"`）

```json
{
  "ast_schema_version": "1.0",
  "entities": [{ "name": "Service", "span": {"start_line":3,"start_col":1,"end_line":10,"end_col":2},
                 "fields": [{ "name": "port", "sort": {"Int": {"min": 1, "max": 65535}} }] }],
  "domains": [{ "name": "Services", "entity": "Service", "size": 4 }],
  "verifications": [{ "kind": "safety", "policy": "RiskRatioPolicy" }]
}
```

- 只增字段，不移除/不改语义（`00 §0.6`）。

### IF-3 报告 JSON（`schema_version: "1.0"`，`spec/report.schema.json`）

```json
{
  "schema_version": "1.0",
  "overall_status": "Fail",
  "logic_used": "QF_SLIA",
  "checks": [{
    "check_name": "NoPortConflict", "target_type": "invariant",
    "status": "Fail", "winning_solver": "cvc5", "time_ms": 214,
    "counterexample": { "entity_snapshots": { "Services": { "0": {"host_ip":"10.0.1.5","port":"8080"} } },
                        "summary": "Services[0] 与 Services[2] 同主机端口冲突",
                        "remediation_suggestion": "将 Services[2].port 调整为 8081" },
    "conflicting_rules": []
  }],
  "proof_hash": "9f2c…", "attestation_hash": "ab41…"
}
```

- 消费方必须容忍未知字段；`overall_status` 全 5 分支由 CI 显式覆盖（`00 §0.4.4`）。

### IF-4 配置 `policylang.toml`
```toml
[verify]
timeout_ms = 3000           # 绑定 NFR-1
max_groundings = 1000000    # G_max（W11 预算）
minimize_core = false
allow_nonlinear = false
max_inflight = 8            # NFR-3 / NFR-4 并发上限
[report]
format = ["json", "sarif"]
output = "report.json"
[[waiver]]                  # 限时豁免，过期即失效（FR-18）
rule = "LegacyPortRule"
owner = "platform-team"
approver = "arch-board"
expires_at = "2026-12-31"
```

### IF-5 锁文件 `policylang.lock`
```toml
[[solver]]                  # 名称 / 版本 / 二进制 SHA-256 三重锁定
name = "z3"
version = "4.13.0"
bin_sha256 = "3a5f…"
logics = ["QF_LIA", "QF_LRA", "QF_BV", "QF_SLIA"]
[[solver]]
name = "cvc5"
version = "1.2.0"
bin_sha256 = "77c1…"
logics = ["QF_LIA", "QF_LRA", "QF_BV", "QF_SLIA"]
```
- 名称/版本/哈希任一不符 ⇒ `E-SOLVER-VERSION`（退出码 4），不静默降级（`00 §0.6`）。

### IF-6 CI 集成
```yaml
# .github/workflows/policylang-gate.yml
name: Formal Policy Verification Gate
on: [pull_request]
jobs:
  formal-verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install solvers & CLI
        run: sudo apt-get update && sudo apt-get install -y z3 cvc5 && cargo install --path crates/policylang-cli
      - name: Verify
        continue-on-error: true
        run: policylang verify --spec policies/*.plm --timeout 3000ms --output report.json --sarif
      - name: Enforce gate (5 分支)
        run: |
          case "$(jq -r '.overall_status' report.json)" in
            Pass|Waived) exit 0 ;;
            Fail) echo "反例/死锁冲突，阻断合并"; exit 1 ;;
            UnknownReviewRequired) echo "UNKNOWN，转交人工评审"; exit 2 ;;
            Error) echo "编译/内部错误"; exit 3 ;;
            *) echo "未知状态"; exit 4 ;;
          esac
```

---

## 8. 关键设计决策（DD-1 ~ DD-12）

| ID | 决策 | 选择 | 理由 | 被否方案 | 风险 |
|---|---|---|---|---|---|
| `DD-1` | 量词处理 | 有界展开消除量词（`ALG-1`） | `03 §3.7` `TH-1`/`TH-2`：编译期消除量词，产出无量词 `QF_*` 查询，杜绝量词实例化退化 | 依赖求解器原生量词（EMatching） | `G(φ)` 组合爆炸，须 `W11` 预算守卫 |
| `DD-2` | 编码范式 | 反证法 `Γ ∧ ¬φ` + `:named` 标签 | 违例可出模型（`TH-7 (ii)`），冲突可提核 | 正向断言 | 核非最小，须可选最小化 |
| `DD-3` | 边界断言与逻辑档位处理 | 见 `DD-3.1` / `DD-3.2` | 分割「建模假设」与「可判定性声明」 | — | — |
| `DD-3.1` | `Bnd(S)` 标签 | `Bnd(S)` **不带 `:named`**（`03 §3.2.6` 预留） | 范围约束是建模假设，不应污染 Unsat Core | 全量 `:named` | `Bnd` 不可满足时核为空，须报 `E-EMPTY-CARRIER` |
| `DD-3.2` | 组合逻辑处理 | 能力探测替代硬编码逻辑名（`03 §3.10.3` 预留） | `QF_BVLIA` 等名称收录/支持度存在版本差异；以运行期实测构建能力矩阵 | 硬编码 `deduce_smt_logic` 名前缀 | 探测失败的档位只接受 `UnknownReviewRequired` |
| `DD-4` | 多求解器调度 | 进程级竞速 + `kill_on_drop` + `JoinSet::shutdown().await` | 首胜即止；`shutdown` 等待子进程退出，满足 `AC-5` 的 `P99 ≤ 50 ms` 回收 | 线程内调用求解器库 | 依赖 tokio ≥ 1.40 的 `JoinSet::shutdown` |
| `DD-5` | 结果可信度 | 交叉验证 / 模型重放 | 杜绝求解器底层 Bug 误报（`FR-9`） | 单一求解器采信 | 重放须精确算术，禁用浮点 |
| `DD-6` | UNKNOWN 处置 | 诚实报告 + 退出码 2 转人工 | `TH-7 (iii)`；绝不把超时伪装成 PASS | 超时当作 PASS/FAIL | 可能降低自动化通过率（诚实优先） |
| `DD-7` | 源文件扩展名 | `.plm` | 避免 `.pl` 与 Perl 冲突（`09 §9.2 B-22`） | 沿用 `.pl` | 需编辑器语法高亮适配 |
| `DD-8` | crate 命名 | 全部 kebab-case | Rust 生态惯例；修正 `policylang-Check` | 混合大小写 | 无 |
| `DD-9` | 展平命名实现 | `scalar_symbol` 单一实现（`INV-L2`） | 消除两处命名漂移（`09 §9.1 A-7`、`09 §9.2 B-8`） | 各 crate 各写一份 | 需强制静态检查 |
| `DD-10` | 除法处理 | `TH-4` 线性化 + 独立 `safety` 义务 | 保持 `QF_LIA` 可判定性同时支持比率策略 | 一律拒绝变量分母 | `LinDiv` 不成立时仍须阻断 |
| `DD-11` | 字符串与正则 | `matches_all` → `R_sub` 转译为 `RegLan`（`TH-6`） | 规避不可判定 PCRE 构造，严格对齐自动机正则 | 全量 PCRE | 拒绝清单须维护（`E-REGEX-*`） |
| `DD-12` | 治理出口 | 5 码制 + `proof_hash` + SARIF + Waiver 状态机 | 满足 `G-7`/`G-8` 与 CI 全分支覆盖 | 3 码制（v2.0） | 消费脚本须升级覆盖 5 分支 |

---

## 9. 部署与运维

### 9.1 构建与依赖版本

| 项 | 要求 |
|---|---|
| 工具链 | Rust stable（Edition 2021），`resolver = "2"` |
| 关键依赖 | `pest` / `pest_derive`、`tokio`（features: `process`/`rt-multi-thread`/`time`，**≥ 1.40** 以提供 `JoinSet::shutdown`）、`clap`、`serde`/`serde_json`、`sha2`、`hex`、`criterion`（dev） |
| 构建 | `cargo build --release`；工作区统一版本由根 `Cargo.toml` 声明 |
| 求解器 | Z3、CVC5、Bitwuzla 由 `policylang.lock` 锁定名称/版本/二进制 SHA-256 |

### 9.2 跨平台

Linux x86_64（CI 主目标）、macOS arm64/x86_64、Windows x86_64 **均完全支持**；求解器经包管理器安装；Windows 下子进程强杀以 `kill_on_drop` 与 `shutdown()` 语义统一，路径一律 `/`。

> **可复算性**：`Real` 一律 `num/den`，**严禁** IEEE-754 参与模型重放（`03 §3.2.3 N-1`），保证跨平台 `proof_hash` 一致。

### 9.3 资源限制

| 资源 | 限制 | 实现 |
|---|---|---|
| 单次验证峰值内存 | `< 512 MB` | `NFR-3`；展开分块 + 惰性 `String` 拼接（`05 §5.7`） |
| 求解超时 | `--timeout`（默认 `3000ms`） | 超时全员回收 → `UnknownReviewRequired` |
| 展开预算 | `--max-groundings`（默认 `10⁶`） | `W11` 静态判定 |
| 并发度 | `--max-inflight`（默认 8） | 受内存预算约束，`NFR-4` |
| 子进程残留 | `= 0` | `kill_on_drop(true)` + `JoinSet::shutdown().await` |

### 9.4 监控指标

- **判定分布**（`Pass`/`Fail`/`Unknown`/`Error`）← 报告 `overall_status`：用于 `NFR-5` UNKNOWN 率统计（`< 1%`）。
- **求解 P50/P99 耗时** ← 竞速编排：`NFR-1`（`< 3 s` @ 500 断言）；**展开规模 `G(φ)` 分布** ← `grounding_cost`：容量规划（`03 §3.9.3`）。
- **子进程残留数** ← 进程树监控：`= 0`（`NFR-3`）；**存活求解器能力矩阵** ← `ALG-3 probe_logic`：启动期刷新，变化即告警。

> **运维纪律**：求解器能力矩阵变化属**架构敏感事件**——若某逻辑档位由 `Native` 退化为 `UnknownRisk`，门禁行为随之变化，须记入运维变更并复核 `policylang.lock`。
