//! 符号表与声明依赖（`05 §4`：D-1 拓扑排序、D-2 作用域）。
//!
//! `D-1`：声明须按依赖拓扑序解析；环即 `E-CYCLIC-DECL`。
//! `D-2`：量词绑定变量的作用域限于其体；字段访问必须落在**该变量所绑定的域**上；
//!        跨域字段引用即 `E-CROSS-DOMAIN-REF`；量化变量遮蔽全局变量即 `W-SHADOW`。

use std::collections::{BTreeMap, BTreeSet};

use policylang_ast::codes::*;
use policylang_ast::diag::Diagnostic;
use policylang_ast::spec::{DeclKind, EntityDecl, InvariantDecl, PolicyDecl, Spec, VarDecl};
use policylang_ast::Span;

/// 域声明（含其绑定的实体）。
#[derive(Debug, Clone)]
pub struct DomainInfo {
    pub name: String,
    pub entity: String,
    pub size: u64,
    pub span: Span,
}

/// 全部声明的索引视图。
#[derive(Debug, Default, Clone)]
pub struct SymbolTable {
    pub entities: BTreeMap<String, EntityDecl>,
    pub domains: BTreeMap<String, DomainInfo>,
    pub vars: BTreeMap<String, VarDecl>,
    pub policies: BTreeMap<String, PolicyDecl>,
    pub invariants: BTreeMap<String, InvariantDecl>,
    /// 依赖拓扑序（`D-1` 的产物）：`(kind, name)`。
    pub topo_order: Vec<(DeclKind, String)>,
}

impl SymbolTable {
    /// 构建符号表并做 `D-1` 校验（重复名、未知实体、环）。
    pub fn build(spec: &Spec) -> Result<SymbolTable, Vec<Diagnostic>> {
        let mut diags: Vec<Diagnostic> = Vec::new();
        let mut tab = SymbolTable::default();

        // ── 实体 ──
        for e in &spec.entities {
            if tab.entities.contains_key(&e.name) {
                diags.push(dup(&e.name, "实体", e.span));
            } else {
                tab.entities.insert(e.name.clone(), e.clone());
            }
        }
        // ── 域 ──
        for d in &spec.domains {
            if tab.domains.contains_key(&d.name) {
                diags.push(dup(&d.name, "域", d.span));
                continue;
            }
            if !tab.entities.contains_key(&d.entity) {
                diags.push(
                    Diagnostic::error(
                        E_UNKNOWN_REF,
                        format!(
                            "域 `{}` 引用了未声明的实体 `{}`（04 §3.2：域须绑定已声明实体）",
                            d.name, d.entity
                        ),
                    )
                    .with_span(d.span),
                );
                continue;
            }
            tab.domains.insert(
                d.name.clone(),
                DomainInfo {
                    name: d.name.clone(),
                    entity: d.entity.clone(),
                    size: d.size,
                    span: d.span,
                },
            );
        }
        // ── 全局变量 ──
        for v in &spec.vars {
            if tab.vars.contains_key(&v.name) {
                diags.push(dup(&v.name, "全局变量", v.span));
            } else {
                tab.vars.insert(v.name.clone(), v.clone());
            }
        }
        // 跨类命名空间冲突（实体/域/变量同名会让字段解析歧义）→ `E-DUP-NAME`
        for (n, d) in &tab.domains {
            if tab.entities.contains_key(n) {
                diags.push(dup(n, "实体与域同名", d.span));
            }
            if tab.vars.contains_key(n) {
                diags.push(dup(n, "域与全局变量同名", d.span));
            }
        }
        // ── 策略 ──
        for p in &spec.policies {
            if tab.policies.contains_key(&p.name) {
                diags.push(dup(&p.name, "策略", p.span));
            } else {
                tab.policies.insert(p.name.clone(), p.clone());
            }
        }
        // ── 不变量 ──
        for i in &spec.invariants {
            if tab.invariants.contains_key(&i.name) {
                diags.push(dup(&i.name, "不变量", i.span));
            } else {
                tab.invariants.insert(i.name.clone(), i.clone());
            }
        }
        // ── 策略与不变量同名会令 `verify` 歧义 ──
        for (n, i) in &tab.invariants {
            if tab.policies.contains_key(n) {
                diags.push(dup(n, "策略与不变量同名", i.span));
            }
        }

        // ── `D-1` 拓扑排序 ──
        match topo_sort(spec, &tab) {
            Ok(order) => tab.topo_order = order,
            Err(mut ds) => diags.append(&mut ds),
        }

        if diags.iter().any(Diagnostic::is_error) {
            Err(diags)
        } else {
            Ok(tab)
        }
    }

    pub fn entity_of_domain(&self, domain: &str) -> Option<&EntityDecl> {
        let d = self.domains.get(domain)?;
        self.entities.get(&d.entity)
    }

    /// 某实体是否存在给定字段。
    pub fn field_exists(&self, entity: &str, field: &str) -> bool {
        self.entities
            .get(entity)
            .map(|e| e.fields.iter().any(|f| f.name == field))
            .unwrap_or(false)
    }

    /// 在全部实体中查找字段所属实体（用于跨域引用的精确报错）。
    pub fn find_field_owner(&self, field: &str) -> Option<&str> {
        self.entities
            .values()
            .find(|e| e.fields.iter().any(|f| f.name == field))
            .map(|e| e.name.as_str())
    }
}

fn dup(name: &str, what: &str, span: Span) -> Diagnostic {
    Diagnostic::error(
        E_DUP_NAME,
        format!("{what}名 `{name}` 重复声明（W1：同一命名空间内名称必须唯一）"),
    )
    .with_span(span)
}

/// `D-1`：对「域 → 实体」依赖做拓扑排序并检测环。
///
/// 当前语言只有一条依赖边类型（域依赖其绑定实体），但实现为**通用 Kahn 算法**，
/// 以便后续新增依赖（如域依赖域、不变量依赖实体）时无需改动。
fn topo_sort(spec: &Spec, tab: &SymbolTable) -> Result<Vec<(DeclKind, String)>, Vec<Diagnostic>> {
    let mut diags = Vec::new();
    // 节点：仅域具有入边（来自实体）。实体、变量、策略、不变量为无依赖节点。
    let mut indeg: BTreeMap<String, usize> = BTreeMap::new();
    let mut edges: BTreeMap<String, Vec<String>> = BTreeMap::new(); // entity -> domains depending on it

    for name in tab.entities.keys() {
        indeg.entry(name.clone()).or_insert(0);
        edges.entry(name.clone()).or_default();
    }
    for (dname, d) in &tab.domains {
        indeg.entry(dname.clone()).or_insert(0);
        edges.entry(dname.clone()).or_default();
        if tab.entities.contains_key(&d.entity) {
            edges
                .entry(d.entity.clone())
                .or_default()
                .push(dname.clone());
            *indeg.entry(dname.clone()).or_insert(0) += 1;
        }
    }

    let mut queue: Vec<String> = indeg
        .iter()
        .filter(|(_, v)| **v == 0)
        .map(|(k, _)| k.clone())
        .collect();
    queue.sort(); // 确定性
    let mut ordered: Vec<String> = Vec::new();
    while let Some(n) = queue.pop() {
        ordered.push(n.clone());
        let mut next: Vec<String> = edges.get(&n).cloned().unwrap_or_default();
        next.sort();
        for m in next {
            if let Some(e) = indeg.get_mut(&m) {
                *e = e.saturating_sub(1);
                if *e == 0 {
                    queue.push(m);
                }
            }
        }
    }
    if ordered.len() != indeg.len() {
        let cyclic: Vec<&String> = indeg
            .iter()
            .filter(|(k, _)| !ordered.contains(k))
            .map(|(k, _)| k)
            .collect();
        diags.push(Diagnostic::error(
            E_CYCLIC_DECL,
            format!("声明依赖存在环：{}（D-1）", cyclic.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")),
        ));
        return Err(diags);
    }

    // 输出顺序：拓扑序的声明在前，其余按源码序（保证确定性）
    let mut out: Vec<(DeclKind, String)> = Vec::new();
    for n in &ordered {
        if tab.entities.contains_key(n) {
            out.push((DeclKind::Entity, n.clone()));
        } else if tab.domains.contains_key(n) {
            out.push((DeclKind::Domain, n.clone()));
        }
    }
    for v in &spec.vars {
        out.push((DeclKind::Var, v.name.clone()));
    }
    for p in &spec.policies {
        out.push((DeclKind::Policy, p.name.clone()));
    }
    for i in &spec.invariants {
        out.push((DeclKind::Invariant, i.name.clone()));
    }
    Ok(out)
}

/// `D-2` 作用域：量化变量的绑定帧栈。
#[derive(Debug, Default, Clone)]
pub struct Scope {
    frames: Vec<BTreeMap<String, Binding>>,
}

/// 量化变量的绑定：变量名 → (域名, 实体名)。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub domain: String,
    pub entity: String,
    pub span: Span,
}

impl Scope {
    pub fn new() -> Self {
        Scope { frames: Vec::new() }
    }

    pub fn push(&mut self) {
        self.frames.push(BTreeMap::new());
    }

    pub fn pop(&mut self) {
        self.frames.pop();
    }

    pub fn bind(&mut self, name: String, b: Binding) {
        if let Some(f) = self.frames.last_mut() {
            f.insert(name, b);
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&Binding> {
        self.frames.iter().rev().find_map(|f| f.get(name))
    }

    /// 当前帧内已绑定的名字（用于同量词内重复变量的检测）。
    pub fn current_frame(&self) -> Option<&BTreeMap<String, Binding>> {
        self.frames.last()
    }

    pub fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }

    /// 全部可见的绑定（用于跨域引用的精确报错）。
    pub fn visible(&self) -> impl Iterator<Item = (&String, &Binding)> {
        self.frames.iter().flat_map(|f| f.iter())
    }
}

/// `D-2` 跨域引用的判定：若字段不在绑定实体上，但在**同一作用域内另一个**绑定实体的
/// 实体上存在，则判定为跨域引用（给出更精确的 `E-CROSS-DOMAIN-REF`）。
pub fn cross_domain_hint(scope: &Scope, tab: &SymbolTable, field: &str) -> Option<String> {
    for (_, b) in scope.visible() {
        if let Some(e) = tab.entities.get(&b.entity) {
            if e.fields.iter().any(|f| f.name == field) {
                return Some(b.domain.clone());
            }
        }
    }
    if let Some(owner) = tab.find_field_owner(field) {
        return Some(owner.to_string());
    }
    None
}

/// 保留字表（与 `spec/grammar.pest` 的 `reserved` 同源，供新增语法的前置校验使用）。
pub fn reserved_keywords() -> BTreeSet<&'static str> {
    [
        "entity", "domain", "var", "policy", "rule", "branch", "mutex", "invariant", "verify",
        "waiver", "require", "forall", "exists", "distinct", "in", "matches_all", "in_cidr",
        "in_range", "unique", "and", "or", "not", "implies", "iff", "Int", "Real", "Bool",
        "String", "IPv4", "IPv6", "BitVec", "Enum", "Set", "true", "false", "min", "max",
        "length", "size", "div", "mod", "consistency", "refines", "completeness", "safety",
        "under", "of", "to_real", "int2bv", "bv2int", "str.len",
    ]
    .into_iter()
    .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::spec_of;

    #[test]
    fn builds_and_orders() {
        let spec = spec_of(
            "entity E { a: Int }\ndomain D: Set[E] [size: 2]\nvar v: Int\npolicy P { rule R: true }\n",
        );
        let tab = SymbolTable::build(&spec).unwrap();
        assert!(tab.domains.contains_key("D"));
        assert!(tab.topo_order.iter().any(|(k, n)| *k == DeclKind::Domain && n == "D"));
    }

    #[test]
    fn unknown_entity_is_error() {
        let spec = spec_of("domain D: Set[Missing] [size: 2]\n");
        let e = SymbolTable::build(&spec).unwrap_err();
        assert!(e.iter().any(|d| d.code == E_UNKNOWN_REF));
    }

    #[test]
    fn duplicate_names_are_errors() {
        let spec = spec_of("entity E { a: Int }\nentity E { b: Int }\n");
        let e = SymbolTable::build(&spec).unwrap_err();
        assert!(e.iter().any(|d| d.code == E_DUP_NAME));
    }
}
