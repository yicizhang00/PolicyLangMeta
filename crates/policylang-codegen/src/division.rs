//! 除法线性化 `TH-4` 与除零义务 `ALG-2`（`03 §3.11`，修正 `A-11`/`A-12`）。
//!
//! ## 为什么必须线性化
//! SMT-LIB 中 `/`、`div`、`mod` 是**全函数**，除数为 0 时**取值未指定**（`unspecified`），
//! 因此含除法比较的 `unsat`（即 PASS）可能是**假证明**（`A-12`，P0）。
//! 消除手段有两层：
//! 1. **义务**（`ALG-2`）：把「分母 ≠ 0」显式提为 `safety` 目标（本模块的 `collect_div_obligations`）；
//! 2. **重写**（`TH-4`）：把 `/` 交叉相乘消去，使查询**不含除法**（本模块的 `linearize_formula`）。
//!
//! ## `TH-4` 的六条重写规则（`03 §3.11.3`）
//! 记 `q = n / d`，比较 `q ⋈ c`：
//!
//! | 编号 | 条件 | 重写 |
//! |---|---|---|
//! | `D1` | `⋈ ∈ {==, !=}`，`d` 任意非零 | `n ⋈ c·d`（两侧同乘 `d`，等/不等不变） |
//! | `D2` | `d` 为**正**常量 | `n ⋈ c·d` |
//! | `D3` | `d` 为**负**常量 | `n ⋈⁻¹ c·d`（**不等号反转**） |
//! | `D4` | `d` 非常量、比较另一侧为常量 `c` | `(d > 0 ∧ n ⋈ c·d) ∨ (d < 0 ∧ n ⋈⁻¹ c·d)` |
//! | `D5` | 除法在**右侧** | 两侧互换后按 `D1`–`D4` 处理（`⋈` 取反向） |
//! | `D6` | `d` 非常量**且**另一侧非常量 | **不可线性化** ⇒ `E-NONLINEAR` |
//!
//! 由 `D4` 可见：因 `c·d` 中 `c` 为常量、`d` 线性，乘积仍线性，故**不离开** `QF_LIA`/`QF_LRA`。

use policylang_ast::codes::{E_DIV_ZERO_CONST, E_NONLINEAR};
use policylang_ast::diag::Diagnostic;
use policylang_ast::formula::{ArithOp, Atom, CmpOp, Expr, ExprKind, Formula, FormulaKind, Rational};
use policylang_ast::Span;

/// `ALG-2`：收集全部**分母**表达式（应在**展开后、线性化前**调用）。
pub fn collect_div_obligations(f: &Formula) -> Vec<Expr> {
    let mut out = Vec::new();
    f.collect_divisors(&mut out);
    out
}

/// 把 `(n, d)` 识别为形如 `n/d` 的比值（`- n/d` 视为 `(-n)/d`）。
fn split_ratio(e: &Expr) -> Option<(Expr, Expr)> {
    match &e.kind {
        ExprKind::Arith {
            op: ArithOp::RealDiv,
            lhs,
            rhs,
        } => Some(((**lhs).clone(), (**rhs).clone())),
        ExprKind::Neg(a) => split_ratio(a).map(|(n, d)| {
            (
                Expr::new(ExprKind::Neg(Box::new(n)), a.span),
                d,
            )
        }),
        _ => None,
    }
}

/// 常量乘：`c · e`（`c` 为字面量 ⇒ 保持线性），并做 `FOLD-1`。
fn mul_const(c: &Rational, e: &Expr, span: Span) -> Expr {
    let lit = if c.is_integer() {
        Expr::new(ExprKind::IntLit(c.num), span)
    } else {
        Expr::new(ExprKind::RealLit(*c), span)
    };
    crate::ground::fold_expr(&Expr::new(
        ExprKind::Arith {
            op: ArithOp::Mul,
            lhs: Box::new(lit),
            rhs: Box::new(e.clone()),
        },
        span,
    ))
}

fn cmp(lhs: Expr, op: CmpOp, rhs: Expr, span: Span) -> Formula {
    Formula::new(FormulaKind::Atom(Atom::Cmp { lhs, op, rhs }), span)
}

fn gt_zero(d: &Expr, span: Span) -> Formula {
    cmp(
        d.clone(),
        CmpOp::Gt,
        Expr::new(ExprKind::IntLit(0), span),
        span,
    )
}

fn lt_zero(d: &Expr, span: Span) -> Formula {
    cmp(
        d.clone(),
        CmpOp::Lt,
        Expr::new(ExprKind::IntLit(0), span),
        span,
    )
}

/// 线性化一个**已展开**公式。返回重写后的公式与重写次数。
pub fn linearize_formula(f: &Formula) -> Result<(Formula, usize), Diagnostic> {
    let mut n = 0usize;
    let out = walk(f, &mut n)?;
    Ok((out, n))
}

fn walk(f: &Formula, n: &mut usize) -> Result<Formula, Diagnostic> {
    let span = f.span;
    match &f.kind {
        FormulaKind::True | FormulaKind::False => Ok(f.clone()),
        FormulaKind::Atom(Atom::Bool(e)) => Ok(Formula::new(
            FormulaKind::Atom(Atom::Bool(e.clone())),
            span,
        )),
        FormulaKind::Atom(Atom::Cmp { lhs, op, rhs }) => {
            let r = linearize_cmp(lhs, *op, rhs, span)?;
            if r.is_some() {
                *n += 1;
            }
            Ok(r.unwrap_or_else(|| f.clone()))
        }
        FormulaKind::Not(x) => Ok(Formula::new(
            FormulaKind::Not(Box::new(walk(x, n)?)),
            span,
        )),
        FormulaKind::And(v) => {
            let mut items = Vec::with_capacity(v.len());
            for x in v {
                items.push(walk(x, n)?);
            }
            Ok(crate::ground::mk_and(items, span))
        }
        FormulaKind::Or(v) => {
            let mut items = Vec::with_capacity(v.len());
            for x in v {
                items.push(walk(x, n)?);
            }
            Ok(crate::ground::mk_or(items, span))
        }
        FormulaKind::Implies(a, b) => Ok(Formula::new(
            FormulaKind::Implies(Box::new(walk(a, n)?), Box::new(walk(b, n)?)),
            span,
        )),
        FormulaKind::Iff(a, b) => Ok(Formula::new(
            FormulaKind::Iff(Box::new(walk(a, n)?), Box::new(walk(b, n)?)),
            span,
        )),
        // 展开器保证不含量词；保留分支以求稳健
        FormulaKind::Forall { body, .. } | FormulaKind::Exists { body, .. } => walk(body, n),
        other => Ok(Formula::new(other.clone(), span)),
    }
}

/// 对**单条比较**做除法线性化。返回 `None` 表示该比较不含可线性化的除法（保持原样）。
fn linearize_cmp(
    lhs: &Expr,
    op: CmpOp,
    rhs: &Expr,
    span: Span,
) -> Result<Option<Formula>, Diagnostic> {
    // D5：除法在右侧 ⇒ 互换后按左侧处理（比较符取反向）
    if split_ratio(rhs).is_some() && split_ratio(lhs).is_none() {
        return linearize_cmp(rhs, op.reverse(), lhs, span);
    }

    let Some((num, den)) = split_ratio(lhs) else {
        return Ok(None);
    };

    // D1/D2/D3：除数为常量
    if let Some(dv) = den.as_num_lit() {
        if dv.is_zero() {
            return Err(Diagnostic::error(
                E_DIV_ZERO_CONST,
                "除数为字面量 0：取值未指定，编译期拒绝（A-12）",
            )
            .with_span(span));
        }
        let Ok(cv) = const_side(rhs, span) else {
            // 另一侧非常量 ⇒ 无法用常量乘消去（D6）
            return Err(nonlinear(span, "除数为常量但另一侧非常量，重写后引入非线性乘积"));
        };
        let cd = mul_const(&cv, &den, span);
        let op2 = if dv.is_negative() { op.flip() } else { op };
        return Ok(Some(cmp(num, op2, cd, span)));
    }

    // D4/D6：除数为非常量
    let Ok(cv) = const_side(rhs, span) else {
        return Err(nonlinear(
            span,
            "除数非常量且比较另一侧亦非常量：`c·d` 成为变量乘积（LinDiv 不成立，D6）",
        ));
    };
    let cd = mul_const(&cv, &den, span);

    // `⋈ ∈ {==, !=}` 无需符号分裂（D1）
    if matches!(op, CmpOp::Eq | CmpOp::Ne) {
        return Ok(Some(cmp(num, op, cd, span)));
    }
    let pos = Formula::and(vec![gt_zero(&den, span), cmp(num.clone(), op, cd.clone(), span)], span);
    let neg = Formula::and(
        vec![lt_zero(&den, span), cmp(num, op.flip(), cd, span)],
        span,
    );
    Ok(Some(crate::ground::mk_or(vec![pos, neg], span)))
}

fn nonlinear(span: Span, why: &str) -> Diagnostic {
    Diagnostic::error(
        E_NONLINEAR,
        format!("除法线性化失败：{why}（TH-4 D6；03 §3.11.3）"),
    )
    .with_span(span)
}

/// 取比较另一侧作为**常量**（仅接受字面量，必要时先折叠）。
fn const_side(e: &Expr, span: Span) -> Result<Rational, Diagnostic> {
    let folded = crate::ground::fold_expr(e);
    folded.as_num_lit().ok_or_else(|| {
        Diagnostic::error(
            E_NONLINEAR,
            "除法线性化要求比较另一侧为常量（TH-4 LinDiv 侧条件）",
        )
        .with_span(span)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::spec_of;

    fn lin(src: &str) -> (Formula, usize) {
        let spec = spec_of(src);
        let f = spec.requires[0].formula.clone();
        linearize_formula(&f).unwrap()
    }

    #[test]
    fn const_divisor_positive_no_flip() {
        // x / 2 > 3  ==>  x > 3*2 = 6
        let (f, n) = lin("var x: Int\nrequire R: x / 2 > 3\n");
        assert_eq!(n, 1);
        match &f.kind {
            FormulaKind::Atom(Atom::Cmp { op, rhs, .. }) => {
                assert_eq!(*op, CmpOp::Gt);
                assert_eq!(rhs.as_int_lit(), Some(6));
            }
            other => panic!("期望单条比较，实际 {other:?}"),
        }
    }

    #[test]
    fn const_divisor_negative_flips() {
        // x / -2 > 3  ==>  x < -6
        let (f, _) = lin("var x: Int\nrequire R: x / -2 > 3\n");
        match &f.kind {
            FormulaKind::Atom(Atom::Cmp { op, rhs, .. }) => {
                assert_eq!(*op, CmpOp::Lt);
                assert_eq!(rhs.as_int_lit(), Some(-6));
            }
            other => panic!("期望单条比较，实际 {other:?}"),
        }
    }

    #[test]
    fn variable_divisor_yields_disjunction() {
        // n / d > 100  ==>  (d>0 ∧ n > 100d) ∨ (d<0 ∧ n < 100d)
        let (f, n) = lin("var n: Int\nvar d: Int\nrequire R: n / d > 100\n");
        assert_eq!(n, 1);
        match &f.kind {
            FormulaKind::Or(v) => assert_eq!(v.len(), 2),
            other => panic!("期望 Or，实际 {other:?}"),
        }
    }

    #[test]
    fn equality_does_not_split() {
        // n / d == 5  ==>  n == 5d（D1：不需符号分裂）
        let (f, _) = lin("var n: Int\nvar d: Int\nrequire R: n / d == 5\n");
        assert!(matches!(f.kind, FormulaKind::Atom(_)));
    }

    #[test]
    fn nonconstant_other_side_is_error() {
        let spec = spec_of("var n: Int\nvar d: Int\nvar c: Int\nrequire R: n / d > c\n");
        let e = linearize_formula(&spec.requires[0].formula).unwrap_err();
        assert_eq!(e.code, E_NONLINEAR);
    }

    #[test]
    fn zero_constant_divisor_is_error() {
        let spec = spec_of("var x: Int\nrequire R: x / 0 > 1\n");
        let e = linearize_formula(&spec.requires[0].formula).unwrap_err();
        assert_eq!(e.code, E_DIV_ZERO_CONST);
    }

    #[test]
    fn quotient_on_right_hand_side() {
        // 100 < n / d  ==>  换向后同 D4
        let (f, n) = lin("var n: Int\nvar d: Int\nrequire R: 100 < n / d\n");
        assert_eq!(n, 1);
        assert!(matches!(f.kind, FormulaKind::Or(_)));
    }

    #[test]
    fn obligations_are_collected() {
        let spec = spec_of("var n: Int\nvar d: Int\nrequire R: n / d > 1\n");
        let obs = collect_div_obligations(&spec.requires[0].formula);
        assert_eq!(obs.len(), 1);
        assert!(matches!(obs[0].kind, ExprKind::Var(ref s) if s == "d"));
    }
}
