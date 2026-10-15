# 04 · DSL 语言参考手册

> **文档角色**：PolicyLang Meta 策略 DSL 的**使用者手册与文法规范**。定义全部可写构造、排序系统、表达式与公式原语、量词语义、验证目标、SMT-LIB2 映射、正则子语言 `R_sub`、CIDR 手册与完整错误码表。
>
> **上游**：`需求文档与开发文档.txt` v2.0 §4.1（语言层原语与验证目标表）
> **下游**：`05`（编译实现）、`06`（SMT 编码）、`spec/grammar.pest`（机器可读文法）
> **版本**：v2.1　|　**状态**：冻结　|　**最后更新**：2026-10-14
>
> **术语与编号**：严格遵循 `00`（排序 / 标量符号 / 逻辑档位 / 退出码 / `.plm` 扩展名）。
> **数学内核**：语义引用 `03`；本文只做「语法 ↔ 语义 ↔ SMT」落地对照。
> **修正声明**：本文为 `spec/grammar.pest` 的规范描述，已修正上游 v2.0 §2.1 的四处缺陷（`B-1 … B-4`，见 `09 §9.2`）。

---

## 1. 语言导览

### 1.1 完整可运行示例

下列 `.plm` 可被 `spec/grammar.pest` 完整解析，并经 P1–P6 生成无量词 SMT-LIB2（`G = 4²+4²+4 = 36 ≤ G_max`）。

```policylang
#lang policylang 2

entity Service {
    id: Int [min: 1, max: 100],
    host_ip: IPv4,
    port: Int [min: 1, max: 65535],
    uses_db: Bool,
    db_host: String [length: 1..64],
    db_port: Int [min: 1, max: 65535],
    db_password: String [length: 12..32]
}

domain Services: Set[Service] [size: 4]

var is_production: Bool
var global_max_connections: Int [min: 10, max: 10000]

policy ServiceDeploymentPolicy {
    rule SameDatabase:
        forall s1, s2 in Services:
            (s1.uses_db and s2.uses_db) implies
                (s1.db_host == s2.db_host and s1.db_port == s2.db_port)

    rule NoPortConflict:
        forall s1, s2 in Services:
            (s1.id != s2.id and s1.host_ip == s2.host_ip) implies
                (s1.port != s2.port)

    rule PasswordComplexity:
        forall s in Services:
            s.uses_db implies
                s.db_password matches_all [".*[A-Z].*", ".*[0-9].*"]
}

invariant PaymentSubnetIsolation {
    forall s in Services:
        s.uses_db implies in_cidr(s.host_ip, "10.0.1.0/24")
}

verify consistency of ServiceDeploymentPolicy
verify invariant PaymentSubnetIsolation under ServiceDeploymentPolicy
verify safety of ServiceDeploymentPolicy
```

### 1.2 逐段解说

| 段 | 构造 | 语义锚点 |
|---|---|---|
| `#lang policylang 2` | 源文件头 | 主版本声明（`00 §0.6`）；缺失/不符即 `E-PARSE-LANG-HEADER` |
| `entity Service { … }` | 实体（记录模式） | 定义 `Schema(Service)`（`03 §3.2.4` 定义 3.2.1）；`IPv4 ≡ BitVec(32)`（§4.2） |
| `Int [min:…, max:…]` | 范围约束 | 受限载体与边界断言（`03 §3.2.2`/§3.2.6）；缺失即 `E-MISSING-RANGE`（W2） |
| `domain … [size: 4]` | 实例域 | 索引集 `idx = Fin 4`（`03 §3.2.4`）；`N ≥ 1`（W3） |
| `var …` | 全局变量 | 加入 `GVar`，全域可见（`03 §3.3.1` D-2） |
| `policy … { rule … }` | 策略与规则 | `R_P ≜ ⋀{ ⟦ground(r)⟧ }` |
| `forall s1, s2 in Services:` | 有界全称量词 | **全笛卡尔积**（AX-Q-INDEP，`03 §3.5.2`）⇒ 需显式 `s1.id != s2.id` |
| `… implies …` | 蕴含 | 右结合，优先级见 `03 §3.4.3` |
| `matches_all [r₁, r₂]` | 正则交集 | `(str.in_re e (re.inter τ(r₁) τ(r₂)))`（`03 §3.13`） |
| `in_cidr(e, "10.0.1.0/24")` | CIDR 成员 | `(= (bvand e mask) net)`（TH-5，`03 §3.12.2`） |
| `verify consistency of P` | 验证目标 | `Bnd ∧ R_P`，`sat ⇒ PASS`（§7.1） |
| `verify invariant I under P` | 验证目标 | `Bnd ∧ R_P ∧ ¬I`，`unsat ⇒ PASS`（§7.2） |
| `verify safety of P` | 验证目标 | 除以零义务反证（§7.6） |

---

## 2. 完整文法

### 2.1 规范 EBNF

```
spec_file ::= lang_header decl*            lang_header ::= "#lang" "policylang" DIGIT+
decl      ::= entity_decl | domain_decl | var_decl | policy_decl
            | invariant_decl | verify_decl | waiver_decl | require_decl

entity_decl ::= "entity" ident "{" (field_decl ("," field_decl)* ","?)? "}"
field_decl  ::= ident ":" type_expr ("[" range_constraint "]")?
domain_decl ::= "domain" ident ":" "Set" "[" ident "]" "[" "size" ":" INT "]"
var_decl    ::= "var" ident ":" type_expr ("[" range_constraint "]")?
type_expr   ::= "Int"|"Real"|"Bool"|"String"|"IPv4"|"IPv6"|"BitVec" "(" INT ")"
              | "Enum" "{" ident ("," ident)* "}"
range_constraint ::= "min" ":" number "," "max" ":" number | "length" ":" INT ".." INT

policy_decl ::= "policy" ident "{" policy_item* "}"
policy_item ::= rule_decl | branch_decl | mutex_decl
rule_decl   ::= "rule" ident ":" formula      branch_decl ::= "branch" ident ":" formula
mutex_decl  ::= "mutex" ident ("," ident)+    invariant_decl ::= "invariant" ident "{" formula "}"
require_decl ::= "require" ident ":" formula
waiver_decl  ::= "waiver" ident "{" (waiver_key ":" (string_lit|ident))+ "}"
verify_decl ::= "verify" "consistency" "of" ident | "verify" "invariant" ident "under" ident
              | "verify" ident "refines" ident   | "verify" "completeness" "of" ident
              | "verify" "safety" "of" ident      | "verify" "mutex" "of" ident

formula ::= f_iff
f_iff     ::= f_implies ("iff" f_implies)*        (* 右结合，最低优先级 *)
f_implies ::= f_or ("implies" f_or)?              (* 右结合 *)
f_or      ::= f_and ("or" f_and)*                 (* 左结合 *)
f_and     ::= f_not ("and" f_not)*                (* 左结合 *)
f_not     ::= "not" f_not | f_primary
f_primary ::= quantifier | in_cidr | in_range | unique | interval | matches_all
            | predicate | bool_atom | "(" formula ")"
quantifier  ::= ("forall"|"exists") ident_list "in" ident ("distinct")? ":" formula
interval    ::= expr "in" "[" expr ".." expr "]"
matches_all ::= expr "matches_all" "[" string_lit ("," string_lit)* "]"
in_cidr     ::= "in_cidr"  "(" expr "," string_lit ")"
in_range    ::= "in_range" "(" expr "," string_lit "," string_lit ")"
unique      ::= "unique" "(" ident "," ident ")"
predicate   ::= expr cmp_op expr
cmp_op      ::= "=="|"!="|">="|"<="|">"|"<"|"str.<"|"str.<="
bool_atom   ::= expr

expr ::= term (add_op term)*        term ::= factor (mul_op factor)*
factor ::= "str.len" "(" expr ")" | cast_expr | bv_call | field_access
         | number | bool_lit | string_lit | ident | "(" expr ")" | "-" factor
field_access ::= ident "." ident
cast_expr ::= "to_real" "(" expr ")" | "int2bv" "(" INT "," expr ")" | "bv2int" "(" expr ")"
number ::= "-"? DIGIT+ ("." DIGIT+)?
```

### 2.2 Pest 规则 ↔ EBNF ↔ 文档章节（对应 `spec/grammar.pest`）

| Pest 规则 | EBNF 构造 | 语义章节 | 关键修正 |
|---|---|---|---|
| `spec_file`/`lang_header` | 源文件头 | `00 §0.6` | 新增 `#lang policylang 2` |
| `entity_decl`/`field_decl` | 实体/字段 | `03 §3.2.4` 定义 3.2.1 | — |
| `domain_decl` | 实例域 | `03 §3.2.4` 定义 3.2.2 | — |
| `var_decl` | 全局变量 | `03 §3.2.4` 定义 3.2.4 | — |
| `type_expr` | 排序表达式 | `03 §3.2.1`、§4 | 新增 `IPv4`/`IPv6` |
| `range_constraint` | 范围约束 | `03 §3.2.2` | — |
| `policy_decl`/`rule_decl` | 策略/规则 | `03 §3.4.2` | — |
| `branch_decl` | 分支 | §7.4 | **新增** |
| `mutex_decl` | 互斥声明 | §7.5 | **新增** |
| `invariant_decl` | 不变量 | §7.2 | — |
| `require_decl` | 强制义务 | §3.9 | **新增** |
| `waiver_decl` | 限时豁免 | `00 §0.3.2` | **新增** |
| `verify_decl` | 验证目标 | §7 | 新增 `mutex` |
| `f_iff` | 等价 | `03 §3.4.3` | **补 `iff`（B-3）** |
| `f_implies`/`f_or`/`f_and`/`f_not` | 逻辑联结词 | `03 §3.4.3` | 优先级一致 |
| `quantifier_expr` | 有界量词 | `03 §3.5.2` | **补 `distinct`** |
| `interval_expr` | `x in [a..b]` | `03 §3.4.2` T-INRANGE | **补（B-4）** |
| `matches_all_expr` | 正则交集 | `03 §3.13` | — |
| `in_cidr_expr`/`in_range_expr` | 网段成员 | `03 §3.12.3` | 新增 `in_range` |
| `unique_expr` | `unique(D, f)` | `03 §3.4.2` T-UNIQUE | **补（B-1）** |
| `bool_atom` | 布尔原子 | `03 §3.4.2` T-BOOL-ATOM | **补（B-2）** |
| `expr`/`term`/`factor` | 算术表达式 | `03 §3.4.1` | 新增 `div`/`mod`/`str.len`/cast |
| `escape_seq` | 字符串转义 | §2.4 | **新增** |
| `reserved`/`ident` | 保留字与标识符 | §2.3 | **新增保留字表** |

### 2.3 保留字表

下列词为关键字，**不得**用作实体名/域变量名/字段名/规则名/分支名（Pest `reserved` 用零宽词边界兜底，保证 `index`、`variable`、`order` 等前缀形标识符仍合法）。

| 类别 | 保留字 |
|---|---|
| 声明引导 | `entity` `domain` `var` `policy` `rule` `branch` `mutex` `invariant` `verify` `waiver` `require` |
| 量词与修饰 | `forall` `exists` `distinct` `in` |
| 原语 | `matches_all` `in_cidr` `in_range` `unique` |
| 逻辑联结词 | `and` `or` `not` `implies` `iff` |
| 排序 | `Int` `Real` `Bool` `String` `IPv4` `IPv6` `BitVec` `Enum` `Set` |
| 字面量 / 约束键 / 算术 / 目标词 | `true` `false` `min` `max` `length` `size` `div` `mod` `consistency` `refines` `completeness` `safety` `under` `of` |

> **函数名不保留**：`str.len`、`to_real`、`int2bv`、`bv2int`、`bvand` 等为内建函数而非保留字；语法按「先函数、后标识符」消解。

### 2.4 字符串转义

字符串由双引号界定，仅支持下列转义；其余反斜杠序列触发 `E-PARSE-ESCAPE`。

| 转义 | 含义 | 码点 | 转义 | 含义 | 码点 |
|---|---|---|---|---|---|
| `\\` | 反斜杠 | U+005C | `\r` | 回车 | U+000D |
| `\"` | 双引号 | U+0022 | `\xHH` | 两位十六进制码点 | U+00HH |
| `\n` | 换行 | U+000A | `\uHHHH` | 四位十六进制码点 | U+HHHH |
| `\t` | 制表 | U+0009 | | | |

---

## 3. 声明

### 3.1 声明清单与作用域

| 声明 | 语法骨架 | 引入符号 | 可见性 |
|---|---|---|---|
| `entity` | `entity E { f: σ [c], … }` | 记录模式 `Schema(E)` | 全局 |
| `domain` | `domain D: Set[E] [size: N]` | 实例域 `D`、索引集 `Fin N` | 全局 |
| `var` | `var v: σ [c]` | 全局常量 `v ∈ GVar` | 全部规则/不变量/分支 |
| `policy` | `policy P { rule … }` | 策略名 `P`、规则集 | 全局 |
| `rule` | `rule r: φ` | 规则名 | 其所属策略 |
| `branch` | `branch b: φ` | 分支名 | 其所属策略 |
| `mutex` | `mutex b₁, b₂, …` | 互斥约束 | 其所属策略 |
| `invariant` | `invariant I { φ }` | 不变量名 `I` | 全局 |
| `require` | `require r: φ` | 强制义务名 | 全局（不可豁免） |
| `waiver` | `waiver w { … }` | 豁免记录 | 全局 |
| `verify` | `verify …` | 验证目标 | 全局 |

> **声明顺序无关**：编译器对声明集合做拓扑排序（`03 §3.3.1` D-1），允许前向引用；成环即 `E-CYCLIC-DECL`。

### 3.2 `entity` 与 `domain`

- `entity E { … }`：每字段须声明**完整排序**；`BitVec` 须给位宽 `n ≥ 1`，`Enum` 须给 `k ≥ 1` 个互异成员（W1，`E-BAD-SORT`）；`Int`/`Real` 须有 `[min,max]`，`String` 须有 `[length]`（W2，`E-MISSING-RANGE`）。
- `domain D: Set[E] [size: N]`：`E` 须已声明（W4，`E-UNKNOWN-ENTITY`）；`D` 不得重复（`E-DUP-SYMBOL`）；`N ≥ 1`（W3，`E-EMPTY-CARRIER`）。需要「可选实体」时用 `Bool` 字段 + 守卫表达（`03 §3.5.3`）。

### 3.3 `var` / `policy` / `rule`

`var v: σ [c]`（`Bool` 无范围约束）。`policy P { rule r: φ … }` 定义规则集，`R_P ≜ ⋀{ ⟦ground(r)⟧ ∣ r ∈ rules(P) }`。

### 3.4 `branch`（分支）

`branch b: φ` 刻画输入域的一个子集，供 `completeness` 使用；记其特征谓词为 `B_b(m)`。

### 3.5 `mutex`（互斥声明）

`mutex b₁, b₂, …`：语义 `∀m. ⋀_{A≠B} ¬(B_A(m) ∧ B_B(m))`，由 `verify mutex of P` 反证（§7.5）。

### 3.6 `invariant` 与 `require`

`invariant I { φ }`：要求 `∀m ∈ M. R_P(m) ⟹ I(m)`。`require r: φ` 语义等价于**不可豁免的 invariant**：`invariant` 失败可被有效 `waiver` 覆盖为 `Waived`，`require` 失败**永远**是 `Fail`（治理层差异）。

### 3.7 `waiver`（限时豁免）

```policylang
waiver w {
    target:   NoPortConflict      // 被豁免的检查名（规则/不变量/目标）
    owner:    "alice"             // 责任人
    approver: "bob"               // 审批人
    expires:  "2027-01-01"        // 到期日（ISO-8601）
    reason:   "legacy migration"  // 理由
}
```

`target` 须指向已声明检查名，否则 `E-UNKNOWN-TARGET`；五键缺任一即 `E-WAIVER-MALFORMED`。到期前被覆盖的 `Fail` 记 `Waived`（退出码贡献 0）；到期后回退 `Fail` 并给 `W-WAIVER-EXPIRED`（`00 §0.4.1`）。

### 3.8 词法遮蔽

量化绑定变量可遮蔽同名全局变量（`03 §3.3.1` D-2），编译期给出 `W-SHADOW` 警告（非错误）。

---

## 4. 排序系统

### 4.1 排序总表

| 排序 `σ` | 全域载体 `D_σ` | 范围约束形态 | SMT-LIB2 排序 | 有界性来源 |
|---|---|---|---|---|
| `Int` | `ℤ` | `[min: a, max: b]`，`a,b ∈ ℤ` | `Int` | 显式区间 |
| `Real` | `ℚ`（精确有理数，N-1） | `[min: a, max: b]`，`a,b ∈ ℚ` | `Real` | 显式区间 |
| `Bool` | `𝔹` | 无（天然有界） | `Bool` | 天然 |
| `String` | `Σ*` | `[length: l..u]`，`0 ≤ l ≤ u` | `String` | 长度区间 |
| `BitVec(n)` | `{0, …, 2ⁿ−1}` | 无（位宽即界） | `(_ BitVec n)` | 位宽 |
| `Enum(E)` | `E = {e₁, …, e_k}` | 无（枚举即界） | `Int` + 成员闭包 | 枚举 |

### 4.2 别名

| 别名 | 实际排序 | 用途 | 编码 |
|---|---|---|---|
| `IPv4` | `BitVec(32)` | `in_cidr`/`in_range` 的 IPv4 网段 | `(_ bvN 32)` |
| `IPv6` | `BitVec(128)` | `in_cidr` 的 IPv6 网段 | `(_ bvN 128)` |

> **`Enum` 是排序不是实体类型**（`03 §3.2.1` 术语纪律）：载体 `E = {…}`，编码为 `Int` + 成员闭包 `(or (= x e₁) …)`（`bound_{Enum}`，`03 §3.2.6`）。

### 4.3 范围约束的语义

| 排序 | 边界断言 `bound_{σ,c}` | 自洽要求 | 违反 |
|---|---|---|---|
| `Int [a,b]` | `(and (>= x a) (<= x b))` | `a ≤ b` | `E-EMPTY-CARRIER` |
| `Real [a,b]` | 同形（精确有理数，N-1） | `a ≤ b`；端点须有理数，禁 IEEE-754 | `E-EMPTY-CARRIER` |
| `String [l..u]` | `(and (>= (str.len x) l) (<= (str.len x) u))` | `0 ≤ l ≤ u`；长度按**码点**计（N-2） | `E-EMPTY-CARRIER` |
| `Bool` / `BitVec(n)` / `Enum(E)` | `true` / 成员闭包 | 天然有界 | — |

> **关键设计决策 DD-3.1**：边界断言 `Bnd(S)` **不带 `:named`**，不污染 Unsat Core（`03 §3.2.6`）。

### 4.4 显式提升规则（禁止隐式提升）

> **N-4（强制）**：**严禁排序隐式提升**（`03 §3.2.3`）。

| 混用场景 | 是否允许 | 所需显式转换 | 错误码 |
|---|---|---|---|
| `Int ⊕ Real` | 允许 | 对 `Int` 侧显式 `to_real(e)` | `E-SORT-MISMATCH` |
| `BV(n) ⊕ Int` | **禁止** | `int2bv(n, e)` 或 `bv2int(e)` | `E-SORT-MISMATCH` |
| `bv2int(e)` | **编译期拒绝** | — | `E-NONLINEAR`（落入非线性片段） |
| `Enum(E)` 与其它排序比较 | **禁止** | — | `E-SORT-MISMATCH` |
| `String` 与 `Int` 混用 | **禁止** | `str.len(e)` 取长度后方可入算术 | `E-SORT-MISMATCH` |

---

## 5. 表达式与公式

### 5.1 算术运算符

| 语法 | 排序 | 线性性侧条件 | SMT-LIB2 |
|---|---|---|---|
| `a + b` / `a - b` | `Int`/`Real`（同排序） | — | `(+ a b)` / `(- a b)` |
| `- a` | 同 `a` | — | `(- a)` |
| `a * b` | `Int`/`Real` | `isConst(a) ∨ isConst(b)`（`LinMul`） | `(* a b)` |
| `a / b` | `Real` | `isConst(b) ∧ b ≠ 0`，或 TH-4 线性化 | `(/ a b)` |
| `div a b` / `mod a b` | `Int` | `isConst(b) ∧ b ≠ 0` | `(div a b)` / `(mod a b)` |
| `bvand(a,b)` … | `BitVec(n)` | — | `(bvand a b)` … |
| `to_real(a)` / `int2bv(n,a)` | `Real` / `BitVec(n)` | `a ∈ [0, 2ⁿ−1]` | `(to_real a)` / `((_ int2bv n) a)` |
| `str.len(e)` | `Int` | — | `(str.len e)` |

> **非线性守卫精确准则**（`03 §3.4.1`，修正上游 `C-5`）：`nonlinear(e) ⟺ (含 `*` 且两侧皆非常量) ∨ (含 `/`/`div`/`mod` 且除数非常量且 TH-4 线性化侧条件不成立)`。实现见 `05 §5.5`。

### 5.2 比较运算符

| 语法 | 排序 | SMT-LIB2 |
|---|---|---|
| `==` / `!=` | `Int`/`Real`/`BV(n)`/`String`/`Enum` | `(= a b)` / `(not (= a b))` |
| `<` `<=` `>` `>=` | `Int`/`Real` | `<` `<=` `>` `>=` |
| `<` …（`BV(n)`） | `BitVec(n)` | **无符号** `bvult` `bvule` `bvugt` `bvuge`（N-3） |
| `str.<` / `str.<=` | `String` | `(str.< a b)` / `(str.<= a b)`（字典序） |

### 5.3 逻辑联结词（优先级与 `03 §3.4.3` 一致）

| 语法 | 结合性 | 优先级（低→高） | SMT-LIB2 |
|---|---|---|---|
| `φ iff ψ` | 右 | 1 | `(= φ ψ)`（`Bool` 等值） |
| `φ implies ψ` | 右 | 2 | `(=> φ ψ)` |
| `φ or ψ` | 左 | 3 | `(or φ ψ)` |
| `φ and ψ` | 左 | 4 | `(and φ ψ)` |
| `not φ` | 前缀 | 5 | `(not φ)` |
| `(φ)` | — | 6 | 分组 |

### 5.4 领域原语

| 语法 | 数学语义 | SMT-LIB2 编码 |
|---|---|---|
| `x in [a..b]` | `a ≤ x ≤ b` | `(and (<= a x) (<= x b))` |
| `unique(D, f)` | `⋀_{i<j ∈ idx(D)} f_i ≠ f_j` | `(distinct f₀ …)` / 两两 `(not (= …))` |
| `e matches_all [r̄]` | `⟦e⟧ ∈ ⋂ L(r)` | `(str.in_re e (re.inter τ(r₁) …))` |
| `in_cidr(e, c)` | `(e & mask(c)) = net(c)` | `(= (bvand e (_ bvMASK n)) (_ bvNET n))` |
| `in_range(e, "lo", "hi")` | `lo ≤ e ≤ hi`（无符号） | `(and (bvule lo e) (bvule e hi))` |

> **退化边界**（`03 §3.5.3`）：`unique(D, f)` 且 `N = 1` ⇒ `⋀∅ = ⊤`（恒真）；`matches_all []` ⇒ `⋂∅ = Σ*`（恒真）。

---

## 6. 量词

### 6.1 语法与 AX-Q-INDEP

```
forall x̄ in D: φ          forall x̄ in D distinct: φ
exists x̄ in D: φ          exists x̄ in D distinct: φ
```

> **公理 AX-Q-INDEP**（`03 §3.5.2`）：`⟦∀x̄∈D. φ⟧ρ = ⋀{ ⟦φ⟧ρ[x̄↦ī] ∣ ī ∈ idx(D)^k }`（`∃` 为 `⋁`）。即 `forall x₁, x₂` **允许同一索引**（对角项被枚举）。

因此「两两不同」约束必须**显式写守卫**（如 `s1.id != s2.id`），这正是示例 `NoPortConflict` 的写法。

### 6.2 `distinct` 修饰

`⟦∀x̄∈D distinct: φ⟧ρ = ⋀{ ⟦φ⟧ρ[x̄↦ī] ∣ ī ∈ Inj(idx(D), k) }`，其中 `Inj(S,k) = {ī ∈ S^k ∣ 两两互异}`，基数 `N·(N−1)···(N−k+1)`。

- `distinct` 版本**更强**（枚举更少），且**必须显式声明**，编译器**不得**自动插入（`03 §3.5.2`）。
- 展开因子由 `N^k` 降为 `N!/(N−k)!`，是规避 `E-GROUNDING-BUDGET` 的主要手段（§12.1）。

### 6.3 退化边界语义表

| 情形 | 语义 |
|---|---|
| `size: N = 1`，`forall x ∈ D: φ` | `⟦φ⟧ρ[x↦0]`（单合取项） |
| `forall x̄ ∈ D distinct`，`k > N` | `Inj = ∅` ⇒ `⋀∅ = ⊤`（**恒真**） |
| `exists x̄ ∈ D distinct`，`k > N` | `⋁∅ = ⊥`（**恒假**） |
| `unique(D, f)`，`N = 1` | `⋀∅ = ⊤`（**恒真**） |
| `matches_all []` | `⋂∅ = Σ*` ⇒ **恒真** |
| 无除法节点的 `safety` | 义务集空 ⇒ `⋀∅ = ⊤` ⇒ **恒真**（标 `safety_vacuous: true`） |
| 被验证策略 **0 条规则** | W12 阻断（`E-EMPTYPOLICY`） |
| 实体声明但**无对应域** | 允许；给 `W-UNUSED-ENTITY`（实体实际不可用） |

---

## 7. 验证目标

六目标统一采用**反证法编码**：断言 `Bnd ∧ ¬π`，`UNSAT ⇒ π` 成立（TH-7，`03 §3.14`）。

| 目标 | 语法 | 数学命题 `π` | SMT 编码要点 | PASS / FAIL | 诊断输出 |
|---|---|---|---|---|---|
| `consistency` | `verify consistency of P` | `∃m ∈ M. R_P(m)` | `(assert Bnd)`；`(assert (! φ_r :named Rule_r))…`；`(check-sat)`；`(get-unsat-core)` | `sat ⇒ PASS`；`unsat ⇒ FAIL` | Unsat Core 规则名 + 源码行号 |
| `invariant` | `verify invariant I under P` | `∀m. R_P(m) ⟹ I(m)` | `(assert Bnd)`；`(assert R_P)`；`(assert (not I))`；`(check-sat)` | `unsat ⇒ PASS`；`sat ⇒ FAIL` | 反例模型（业务视图 + 修复建议） |
| `refines` | `verify P_new refines P_old` | `∀m. R_new(m) ⟹ R_old(m)` | `(assert Bnd)`；`(assert R_new)`；`(assert (not R_old))`（双查询见 `06 §6.3.3`） | `unsat ⇒ PASS`；`sat ⇒ FAIL` | 被意外放行的边界反例（如 `port = 80`） |
| `completeness` | `verify completeness of P` | `∀m ∈ D. ⋁_{i} B_i(m)` | `(assert Bnd)`；`(assert (and (not B₁) … (not Bₙ)))` | `unsat ⇒ PASS`；`sat ⇒ FAIL` | 死区反例 `{"var":"order_amount","lo":100,"hi":199}` |
| `mutex` | `verify mutex of P` | `∀m. ⋀_{(A,B)} ¬(B_A(m) ∧ B_B(m))` | `(assert Bnd)`；对每对 `(assert (and B_A B_B))` | `unsat ⇒ PASS`；`sat ⇒ FAIL` | 同时命中两支的反例模型 |
| `safety` | `verify safety of P` | `∀m. R_P(m) ⟹ ⋀_j (b_j(m) ≠ 0)` | `(assert Bnd)`；`(assert R_P)`；`(assert (or (= b₁ 0) …))`（查询本身不含除法） | `unsat ⇒ PASS`；`sat ⇒ FAIL` | 触发除零的参数模型 |

- **`consistency` 是全框架唯一「`sat = PASS`」的目标**；其余五目标均为 `unsat = PASS`。
- **`safety` 义务**：`⟨b_j⟩ = ALG-2 collect_div_obligations(P)`（`03 §3.11.2`）；`k = 0` 时恒真并标 `safety_vacuous: true`。存在理由（`03 §3.11.1`）：SMT 的 `/`、`div`、`mod` 是**全函数**，分母为 0 时取值未指定，故基于除法比较的 PASS 可能是**假证明**。
- **术语纪律**：`completeness` 验证目标（`FR-3`）与「变换完备性」（TH-2 侧）无关（`00 §0.3.1`）。

---

## 8. SMT 映射总表

### 8.1 排序 ↔ SMT-LIB2 排序

| DSL 排序 | SMT-LIB2 | 备注 |
|---|---|---|
| `Int` | `Int` | 配 `(>= x a) (<= x b)` |
| `Real` | `Real` | 精确有理数（N-1）；字面量 `(/ num den)` 或 `to_real` |
| `Bool` | `Bool` | — |
| `String` | `String` | 配 `(str.len x)` 界 |
| `BitVec(n)` | `(_ BitVec n)` | 无符号（N-3） |
| `Enum(E)` | `Int` | + 成员闭包 `(or (= x e₁) …)`；成员两两 `distinct` |

### 8.2 原语 ↔ SMT-LIB2 表达式

| DSL 原语 | SMT-LIB2 | DSL 原语 | SMT-LIB2 |
|---|---|---|---|
| `a + b` / `a - b` / `a * b` | `(+ a b)` / `(- a b)` / `(* a b)` | `unique(D, f)` | `(distinct f₀ f₁ …)` |
| `a / b` | `(/ a b)`（`b ≠ 0` 义务） | `e matches_all [r̄]` | `(str.in_re e (re.inter τ(r₁) …))` |
| `div a b` / `mod a b` | `(div a b)` / `(mod a b)` | `in_cidr(e, c)` | `(= (bvand e (_ bvMASK n)) (_ bvNET n))` |
| `- a` | `(- a)` | `in_range(e,"lo","hi")` | `(and (bvule lo e) (bvule e hi))` |
| `a == b` / `a != b` | `(= a b)` / `(not (= a b))` | `str.len(e)` | `(str.len e)` |
| `<` `<=` `>` `>=`（数值） | `<` `<=` `>` `>=` | `to_real(a)` | `(to_real a)` |
| `<` …（`BV(n)`） | `bmvult`（`bvule` `bvugt` `bvuge`） | `int2bv(n, a)` | `((_ int2bv n) a)` |
| `and`/`or`/`not`/`implies`/`iff` | `and`/`or`/`not`/`=>`/`=` | `bvand bvor bvxor bvnot` | `bvand` `bvor` `bvxor` `bvnot` |
| `x in [a..b]` | `(and (<= a x) (<= x b))` | `bvadd bvsub bvmul bvshl bvlshr` | `bvadd` `bvsub` `bvmul` `bvshl` `bvlshr` |

### 8.3 正则构造 ↔ `RegLan` 与位向量字面量

| 正则片段 | SMT-LIB2 | 正则片段 | SMT-LIB2 |
|---|---|---|---|
| 字面字符 `c` | `(str.to_re "c")` | `r₁ r₂`（连接） | `(re.concat τ(r₁) τ(r₂))` |
| `.` | `re.allchar` | `r₁\|r₂` | `(re.union τ(r₁) τ(r₂))` |
| `[a-z]` | `(re.range "a" "z")` | `r*` / `r+` / `r?` | `(re.* …)` / `(re.+ …)` / `(re.opt …)` |
| `[abc]` | `(re.union (str.to_re "a") …)` | `r₁ ∩ r₂` | `(re.inter τ(r₁) τ(r₂))` |
| `[^abc]` | `(re.comp (re.union …))` | | |

| 字面量形态 | 规范写法 | 说明 |
|---|---|---|
| `N` 位无符号常量 | `(_ bvN W)` | **优先**，规避 `#x` 宽度截断差异（`03 §3.12.3`） |
| 掩码 / 网络地址 | `(_ bvMASK n)` / `(_ bvNET n)` | `mask(p) = 2ⁿ − 2^{n−p}`（`p=0 ⇒ 0`） |
| 实数常量 | `(/ num den)` / `to_real` | 精确有理数，禁浮点（N-1） |
| 负整数 | `(- 5)` | SMT-LIB 负数写作 `(- n)`，`(- 5)` ≠ 字面量 `-5` |

---

## 9. 正则子语言 `R_sub`

`matches_all` 的模式必须落在正则子语言 `R_sub`（`03 §3.13.1`），保证可自动机化（TH-6）。

### 9.1 允许清单与转译 `τ`

| PCRE 片段 | 语义 | `τ` 转译 |
|---|---|---|
| 字面字符 `c` | `{c}` | `(str.to_re "c")` |
| `.` | `Σ` | `re.allchar` |
| `[abc]` / `[^abc]` | `{a}∪{b}∪{c}` / `Σ ∖ {a,b,c}` | `(re.union …)` / `(re.comp (re.union …))` |
| `[a-z]` | `{c ∣ a ≤ c ≤ z}` | `(re.range "a" "z")` |
| `\d` / `\w` / `\s` | `[0-9]` / `[A-Za-z0-9_]` / `[ \t\n\r\f\v]` | `re.range` / 三段 `re.union` / 枚举 `re.union` |
| `r₁ r₂` / `r₁\|r₂` | 连接 / 并 | `(re.concat τ(r₁) τ(r₂))` / `(re.union τ(r₁) τ(r₂))` |
| `r*` / `r+` / `r?` | 闭包 | `(re.* …)` / `(re.+ …)` / `(re.opt …)` |
| `r{n}`，`1 ≤ n ≤ 64` | `L(r)ⁿ` | `n` 份 `τ(r)` 的 `re.concat` 展开 |
| `r{n,}` / `r{n,m}`，`n ≤ m ≤ 64` | `L(r)ⁿ·L(r)*` / `⋃_{i=n..m}L(r)ⁱ` | `(re.concat τ(r)ⁿ (re.* τ(r)))` / `re.union` 展开 |
| `^r$` | 全串匹配 | `τ(r)`（**冗余**：`str.in_re` 天然全串） |
| `\.` `\*` `\+` `\?` `\|` … | 转义字面字符 | `(str.to_re "<c>")` |
| `\xHH` / `\uHHHH` | 码点 | `(str.to_re "<码点>")` |

### 9.2 拒绝清单

| 构造 | 错误码 | 理由 |
|---|---|---|
| 反向引用 `\1`…`\9`、`\k<name>` | `E-REGEX-NONREGULAR` | 非正则语言 |
| 前瞻 `(?=` `(?!`、后顾 `(?<=` `(?<!` | `E-REGEX-NONREGULAR` | 不可判定 |
| 词边界 `\b` `\B` | `E-REGEX-NONREGULAR` | 依赖上下文 |
| 递归/子程序 `(?R)` `(?1)` `(?&name)` | `E-REGEX-NONREGULAR` | 图灵完备，违反 `NG-1` |
| 占有量词 `*+` `++` `?+` `{n,m}+`、原子组 `(?>…)` | `E-REGEX-NONREGULAR` | 依赖回溯顺序 |
| 条件 `(?(cond)yes\|no)` | `E-REGEX-NONREGULAR` | 图灵完备 |
| POSIX 字符类 `[[:alpha:]]`、Unicode 属性类 `\p{L}` | `E-REGEX-UNSUPPORTED` | 是正则，但 `RegLan` 无对应语法（**可建议改写**） |
| `r{n,m}` 且 `n·\|τ(r)\| > 4096` | `E-REGEX-BUDGET` | 嵌套量词展开超预算 |

> **可移植性约定**：一律显式使用 `str.to_re "c"`，不依赖求解器对裸字符串的隐式强制转换（`03 §3.13.3` 注）。

---

## 10. CIDR 手册

### 10.1 定义

```
block(n₀, p) ≜ { ip ∈ {0..2ⁿ−1} ∣ ⌊ip / 2^(n−p)⌋ = ⌊n₀ / 2^(n−p)⌋ }
mask(p)     ≜ 2ⁿ − 2^(n−p)   (1 ≤ p ≤ n)     mask(0) ≜ 0
net(n₀, p)  ≜ n₀ & mask(p)
```

`n` 为地址位宽（IPv4 `n = 32`，IPv6 `n = 128`）。掩码等价性由 **TH-5** 保证（`03 §3.12.2`）：`(ip & mask(p)) = net(n₀,p) ⟺ ip ∈ block(n₀,p)`。

### 10.2 字面量与校验

| 项 | 规范 |
|---|---|
| IPv4 字面量 | `in_cidr(e, "A.B.C.D/p")`：4 段十进制 `0..255`，无前导零（`0` 除外） |
| IPv6 字面量 | `in_cidr(e, "2001:db8::/32")`：含 `:` 者判为 v6；RFC 4291 压缩形式；**禁** zone-id（`%eth0`）；**禁** IPv4-mapped 混写（`::ffff:1.2.3.4`） |
| 前缀范围 | IPv4 `p ∈ [0,32]`；IPv6 `p ∈ [0,128]`；越界 `E-CIDR-SYNTAX` |
| 排序匹配 | `e : BV(32)` 配 IPv4；`e : BV(128)` 配 IPv6；否则 `E-CIDR-WIDTH` |
| 常量性 / 非法字面量 | 字面量**必须**是字面量（不许变量/拼接）；非法即 `E-CIDR-SYNTAX` |

### 10.3 编码形式

```
in_cidr(e, "10.0.1.0/24")   ⇒ (= (bvand <e> (_ bv4294967040 32)) (_ bv167772416 32))
in_cidr(e, "2001:db8::/32")  ⇒ (= (bvand <e> (_ bv340282366841710300949110269838224261120 128))
                                    (_ bv42540488161975842760550356425300246528 128))
in_range(e, "10.0.0.0", "10.0.0.255") ⇒ (and (bvule (_ bv167772160 32) <e>) (bvule <e> (_ bv167772415 32)))
```

- `_ bvN W` 使用**十进制**而非 `#x`（规避求解器对十六进制宽度的隐式截断差异）。
- `in_range` 要求 `bvule(lo, hi)`，否则 `E-CIDR-SYNTAX`；全部使用**无符号**算子（N-3）。

---

## 11. 错误码总表

**严重级**：`阻断` = 编译期停止（退出码 3）；`失败` = 验证失败（退出码 1）；`未知` = 转人工（2）；`内部` = 环境/内部错误（4）；`警告`/`信息` = 不阻断。

### 11.1 编译期错误（退出码 3）

| 码 | 触发条件 | 诊断消息模板 | 修复建议 |
|---|---|---|---|
| `E-PARSE-SYNTAX` | Pest 解析失败 | `语法错误 @ {line}:{col}：期望 {expected}，实际 "{found}"` | 按 §2 检查文法 |
| `E-PARSE-LANG-HEADER` | 缺/非法 `#lang` 头 | `缺少或非法的源文件头：需 "#lang policylang 2"` | 首行补 `#lang policylang 2` |
| `E-PARSE-ESCAPE` | 非法字符串转义 | `非法转义序列 "\{seq}" @ {line}:{col}` | 改用 §2.4 允许的转义 |
| `E-BAD-SORT`（W1） | 排序声明不完整（`BitVec` 缺位宽 / `Enum` 成员重复或空） | `排序 "{sort}" 声明不完整：{detail}` | 补位宽或修正 `Enum` 成员 |
| `E-MISSING-RANGE`（W2） | `Int`/`Real` 缺 `[min,max]`，`String` 缺 `[length]` | `{sort} 字段/变量 "{name}" 缺少范围约束` | 补 `[min: a, max: b]` / `[length: l..u]` |
| `E-EMPTY-CARRIER`（W3） | 范围自洽性破坏（`a > b`、`u < l`、`size < 1`） | `受限载体为空：{name} 的 {a} > {b} / size 须 ≥ 1` | 修正端点或 `size` |
| `E-UNKNOWN-ENTITY`（W4） | `domain` 引用未声明实体 | `未知实体 "{E}" @ {line}:{col}` | 先声明 `entity {E}` |
| `E-DUP-SYMBOL`（W4） | 同名声明重复（域/实体/规则等） | `符号 "{name}" 重复声明（先前位于 {line}:{col}）` | 重命名或删除重复项 |
| `E-UNBOUND-INSTANCE`（W5） | `x.f` 的 `x` 非当前量化绑定变量 | `未绑定的实例变量 "{x}" @ {line}:{col}` | 在量词中引入 `x` |
| `E-UNKNOWN-FIELD`（W5） | `x.f` 的 `f` 不在实体字段集 | `实体 "{E}" 无字段 "{f}"` | 修正字段名或实体声明 |
| `E-UNBOUND-VAR`（W6） | 裸标识符含自由变量 | `未声明变量 "{v}" @ {line}:{col}` | 声明 `var {v}` 或用量词绑定 |
| `E-SORT-MISMATCH`（W7） | 两侧排序不同（含隐式提升） | `排序不匹配：左侧 {σ₁}，右侧 {σ₂}（禁止隐式提升，见 N-4）` | 显式 `to_real`/`int2bv`/`str.len` 对齐 |
| `E-NONLINEAR`（W8） | `*` 两侧非常量；或 `/`/`div`/`mod` 除数非常量且线性化不成立 | `检测到非线性算术：{detail}（undecidable / forbidden）` | 固化常数为除数，或分段枚举 |
| `E-REGEX-NONREGULAR`（W9） | 正则含非正则构造（§9.2） | `正则 "{r}" 非正则：{reason}` | 改写为 `R_sub` 子集 |
| `E-REGEX-UNSUPPORTED`（W9） | 正则合法但 `RegLan` 无对应语法 | `正则 "{r}" 不被 RegLan 支持：{reason}` | 改写为显式 `re.range` 枚举 |
| `E-REGEX-BUDGET`（W9） | `r{n,m}` 展开超 `n·\|τ(r)\| > 4096` | `正则展开超预算：n·|τ(r)| = {n} > 4096` | 降低重复次数或拆分模式 |
| `E-CIDR-SYNTAX`（W10） | CIDR 字面量非法（段越界/前导零/前缀越界/zone-id） | `非法 CIDR 字面量 "{lit}"：{reason}` | 按 §10.2 修正 |
| `E-CIDR-WIDTH`（W10） | 地址族与表达式位宽不匹配 | `CIDR 地址族与表达式位宽不符：{fam} vs BV({n})` | 匹配属性（IPv4↔BV(32)/IPv6↔BV(128)） |
| `E-GROUNDING-BUDGET`（W11） | `G(φ) > G_max` | `展开规模 {G} 超预算 {G_max}；量词路径见诊断 JSON` | 降低 `size` 或改用 `distinct`（§12.1） |
| `E-UNKNOWN-TARGET`（W12） | `verify`/`waiver` 引用符号未声明 | `未知验证目标 "{t}" @ {line}:{col}` | 声明对应符号 |
| `E-EMPTYPOLICY`（W12） | 被验证策略 0 条规则 | `策略 "{P}" 无规则，语义退化` | 补充规则 |
| `E-CYCLIC-DECL` | 声明依赖图成环 | `声明依赖成环：{a} → {b} → … → {a}` | 打破环 |
| `E-CROSS-DOMAIN-REF` | 量化体内引用另一域实例 | `跨域实例引用 "{x}.{f}"：请通过域声明解耦` | 改为同域访问或声明桥接域 |
| `E-WAIVER-MALFORMED` | `waiver` 缺键或 `expires` 非 ISO-8601 | `waiver 结构非法：缺少 {key} / expires 非法` | 补齐五键并修正日期 |
| `E-UNVERIFIABLE` | 可判定性守卫家族总码（上述 `E-NONLINEAR`/`E-GROUNDING-BUDGET`/`E-REGEX-*` 聚合） | `Unverifiable: {detail}` | 依具体子码处理 |
| `E-DUP-LABEL` | `:named` 标签重复（`NM-3` 标签生成冲突，编译期校验标签唯一性，`06 §6.1.4`） | `标签 "{label}" 重复：{a} 与 {b} 映射冲突` | 重命名规则/分支/不变量使标签唯一 |
| `E-NO-BRANCHES` | `verify completeness` 但策略无 `branch` 声明（或分支数 `k = 0`，`FR-15`，`06 §6.3.4`） | `策略 "{P}" 无分支声明，completeness 目标无输入` | 为策略补充 `branches { … }` 声明 |
| `E-MUTEX-BUDGET` | `mutex` 分支对数 > `--mutex-max-pairs`（默认 64，`06 §6.3.6`） | `mutex 分支对数 {n} 超预算 {max}：请先合并分支` | 合并/减少分支，或提高 `--mutex-max-pairs` |

### 11.2 运行期错误（退出码 4）与警告

| 码 | 触发条件 | 严重级 | 诊断消息模板 | 修复建议 |
|---|---|---|---|---|
| `E-IO` | 源文件读写/临时文件失败 | 内部 | `I/O 失败：{path}（{errno}）` | 检查权限与路径 |
| `E-SOLVER-MISSING` | 求解器可执行文件缺失 | 内部 | `求解器 "{name}" 不可用（未安装或不在 PATH）` | 安装或修正 `policylang.lock` |
| `E-SOLVER-VERSION` | 版本与 `policylang.lock` 不符 | 内部 | `求解器 "{name}" 版本 {got} ≠ 期望 {want}` | 对齐版本 |
| `E-LOGIC-UNSUPPORTED` | 无任何后端注册支持该逻辑档位 | 内部 | `无可路由后端支持逻辑 "{logic}"` | 安装支持该理论的求解器 |
| `E-XVALIDATE-MISMATCH` | 交叉验证不一致 | 内部 | `交叉验证不一致：{a} 判 {sa}，{b} 判 {sb}` | 上报求解器缺陷，禁用该后端 |
| `E-REPORT-WRITE` | 审计报告落盘失败 | 内部 | `报告落盘失败：{path}` | 检查输出目录 |
| `E-INTERNAL` | 未分类内部错误 | 内部 | `内部错误：{detail}（请附栈回溯）` | 上报 issue |
| `W-SHADOW` | 绑定变量遮蔽同名全局变量 | 警告 | `绑定变量 "{v}" 遮蔽同名全局变量 @ {line}:{col}` | 无（继续） |
| `W-UNUSED-ENTITY` | 实体声明但无对应域 | 警告 | `实体 "{E}" 无对应域，实例不可用` | 无 |
| `W-WAIVER-EXPIRED` | 有效期中 `waiver` 已过期 | 警告 | `豁免 "{w}" 已过期（{expires}），回退为 Fail` | 使 `Waived` 回退 `Fail` |
| `W-SAFETY-VACUOUS` | `safety` 目标无除法义务 | 信息 | `safety 义务为空（safety_vacuous: true）` | 无（恒真） |
| `E-SOLVER-PROTOCOL` | 求解器响应流协议错误（其它 `(error "…")` / 无 `Verdict` 且进程正常退出 / `Verdict` 数少于 `check-sat` 数 / stdout > 64 MiB，`06 §6.8.3`） | 内部 | `求解器协议错误：{detail}` | 检查求解器版本与 `policylang.lock`，上报 issue |
| `W-UNSUPPORTED-CMD` | 求解器返回 `unsupported`（非关键命令） | 警告 | `求解器不支持命令 "{cmd}"` | 无（若涉及关键命令 `get-model` 则降级为 `Error`） |
| `W-NONUTF8` | 求解器 stdout 非 UTF-8（`from_utf8_lossy` 容错） | 警告 | `求解器输出含非 UTF-8 字节，已容错` | 无（检查求解器版本） |
| `W-SOLVER-STDERR` | 求解器 stderr 非空但 stdout 完整 | 警告 | `求解器 "{name}" stderr 非空（{n} 字节）` | 无（`--verbose` 时采集） |
| `W-SOLVER-DRIFT` | `--allow-version-drift` 下降级：求解器版本与锁文件不符 | 警告 | `求解器 "{name}" 版本漂移：{got} ≠ {want}（--allow-version-drift）` | 对齐 `policylang.lock` 或移除该开关 |
| `W-LOGIC-FALLBACK` | 组合逻辑档位无标准名 ⇒ 回落 `ALL`（`06 §6.4.2`） | 警告 | `逻辑档位回落 ALL：{combination}` | 无（或拆分查询以避免组合档位） |
| `W-SINGLE-BACKEND` | 胜任后端集合仅 1 个（单后端模式，无竞速收益，`06 §6.4.4`） | 警告 | `单后端模式：仅 {name} 支持逻辑 "{logic}"` | 无（报告标注 `race_degraded: true`，`--timeout` ×2） |
| `W-SLOW-GOAL` | 单目标求解耗时 > 3 s（`06 §6.10`） | 警告 | `目标 "{goal}" 求解耗时 {t} ms 超阈值` | 无（回归定位用） |
| `W-PROOF-UNAVAILABLE` | 证明器不可用，UNSAT 检查降级为 `two-of-n`（`06 §6.7.2`） | 警告 | `证明器不可用，降级为 two-of-n` | 安装 `carcara` 以启用证明检查 |
| `W-VACUOUS-INVARIANT` | `invariant` 的 Unsat Core 不含 `PLI__*`（前提 `R_P` 不可满足，空真，`06 §6.3.7`） | 警告 | `invariant 空真：R_P 不可满足（Core 缺 PLI__*）` | 补跑 `verify consistency of P` |
| `W-VACUOUS-REFINES` | `refines` 的 `Q1` Core 不含 `PLR__*_OLD_NEG`（`R_new` 不可满足，空真，`06 §6.3.7`） | 警告 | `refines 空真：R_new 不可满足（Core 缺 *_OLD_NEG）` | 对新旧策略各补跑 `verify consistency` |
| `W-VACUOUS-SAFETY` | `safety` 的 Unsat Core 不含 `PLS__*`（`R_P` 不可满足，空真，`06 §6.3.7`） | 警告 | `safety 空真：R_P 不可满足（Core 缺 PLS__*）` | 补跑 `verify consistency of P` |
| `W-SOLVER-MISSING` | `required = false` 的后端缺失（从竞速集 `S` 中剔除，`06 §6.5.2`） | 警告 | `求解器 "{name}" 缺失（非必需）` | 无（或安装该后端） |
| `W-WAIVER-MALFORMED` | `waiver` 的 `owner = approver`（非法豁免，忽略并保持 `Fail`，`07 §7.9.4`） | 警告 | `豁免 "{w}" 非法：owner 与 approver 相同` | 修正豁免责任人与审批人 |
| `W-REVIEW-EXPIRED` | 评审超 `deadline_at` 且 `proof_hash` 仍复现（自动迁移 `→ Escalated`，保持退出码 `2`，`07 §7.8.5`） | 警告 | `评审 "{review}" 超时，已升级 Escalated` | 重新指派审批人 |
| `W-REVIEW-STALE` | 评审 `spec_hash` 与当前不符（规范漂移，自动迁移 `→ Superseded`，`07 §7.8.5`） | 警告 | `评审 "{review}" 因规范漂移失效，待重建` | 以新 `proof_hash` 重建评审 |

### 11.3 退出码与合并格

```
Error ⊐ Fail ⊐ UnknownReviewRequired ⊐ Waived ⊐ Pass
overall_status = join{ status(c) | c ∈ checks }（取偏序最大者）
```

| 退出码 | 名称 | 触发条件 |
|---|---|---|
| `0` | PASS | `overall_status ∈ {Pass, Waived}` |
| `1` | VERIFICATION_FAILED | `overall_status = Fail` |
| `2` | UNKNOWN_REVIEW_REQUIRED | `overall_status = UnknownReviewRequired` |
| `3` | COMPILE_ERROR | 解析/合式性/可判定性守卫阻断（含 `E-UNVERIFIABLE` 家族） |
| `4` | INTERNAL_ERROR | 求解器缺失或版本不符 / IO 失败 / 交叉验证不一致 / 报告落盘失败 |

---

## 12. 最佳实践与反模式

### 12.1 如何避免 Grounding 预算超限

| 反模式 | 问题 | 推荐写法 |
|---|---|---|
| `forall s1, s2, s3 in Services:`（`size: 100`） | `N^k = 10⁶`，触 `E-GROUNDING-BUDGET` | 改用 `distinct`（`100·99·98`）或分解为二元规则 |
| 对无关变量做全称量化 | 死变量放大因子 | 删除未使用绑定变量（`ALG-1-P` 部分出现剪枝） |
| 用标量拼装「域」语义 | 跳过实例域，丢失有界性 | 用 `domain` + 量词，让编译器静态计算 `G` |

> **预算口径**：`G(φ)` 是**展开后**断言规模上界，可在不展开前提下静态算出（`O(|φ|)`，`03 §3.9.1`）。`G_max` 默认 `10⁶`（`--max-groundings` 可调）；`distinct` 把因子从 `N^k` 降为 `N!/(N−k)!`。

### 12.2 `distinct` 的正确用法

| 场景 | 写法 |
|---|---|
| 需要「两两不同」 | `forall s1, s2 in Services distinct: φ`（单射枚举，语义更强，不含对角项） |
| 需要包含对角项（自反约束） | `forall s1, s2 in Services: φ`（全笛卡尔积，AX-Q-INDEP） |
| 两两不同 + 显式守卫 | 二选一，**不要同时**写 `distinct` 与 `s1.id != s2.id`（冗余守卫无害但增加规模） |

> **反模式**：把 `distinct` 当性能优化自动插入。它是**语义选择**，编译器**不得**自动插入（`03 §3.5.2`）。

### 12.3 `safety` 义务的写法

| 反模式 | 问题 | 推荐写法 |
|---|---|---|
| 写 `loss / exposure > 1/2` 但不声明 `safety` | 分母为 0 时取值未指定 ⇒ 假证明风险 | 显式 `verify safety of RiskPolicy` 独立解除义务 |
| 变量作除数且比较右侧也是变量 | `LinDiv` 不成立 ⇒ `E-NONLINEAR` | 使分母或比较右侧之一为常量（`03 §3.11.3`） |
| 用 `div`/`mod` 且除数非常量 | floor 除法不可线性化 | 固化除数为常量或分段枚举 |

> **正确姿势**：`safety` 与 `invariant`/`refines` 是**正交义务**；前者解除除零义务后，后者才可安全启用 TH-4 线性化。

### 12.4 排序、范围与目标选择

| 反模式 | 问题 | 推荐写法 |
|---|---|---|
| 用 `BitVec(32)` 表示端口号 | 比较须用 `BV` 无符号算子，且与 `Int` 混用被拒 | 端口用 `Int [min:1, max:65535]`，仅 IP 用 `IPv4` |
| 依赖隐式 `Int`→`Real` 提升 | `E-SORT-MISMATCH`（N-4） | 显式 `to_real(x)` |
| `Real [min: 0.1, max: 0.3]` 用二进制浮点推导 | 破坏精确有理数语义（N-1） | 端点写为有理数（`1/10`、`3/10`），编译器以 `num/den` 表示 |
| `domain` 用 `size: 0` 表示「可选实体」 | `E-EMPTY-CARRIER`（W3） | 用 `Bool exists_flag` 字段 + 守卫 |
| 用 `consistency` 代替 `invariant` | 仅证明「存在合法配置」，不能证明「所有配置都满足红线」 | 安全红线用 `invariant`，二者不可互替 |
