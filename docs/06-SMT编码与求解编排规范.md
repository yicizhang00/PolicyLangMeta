# 06 · SMT 编码与求解编排规范

> **文档角色**：定义「无量词 IR → SMT-LIB2 脚本」的全部编码规则，以及「脚本 → 求解器进程 → 判定与诊断」的全部编排规则。
>
> **上游**：`需求文档与开发文档.txt` v2.0 §4.3（FR-8/9/10）、§4.1 验证目标对照表、§4.2 生成器伪码、§4 求解层代码
> **上游依赖**：`03`（TH-1~TH-7、ALG-1/ALG-2、W1~W12、N-1~N-4）、`05`（P6 生成器实现）
> **下游**：`07`（诊断与治理）、`10`（BENCH-1~6）
> **版本**：v2.1　|　**状态**：冻结
>
> **本文修正的上游严重缺陷（详见 `09`）**：`C-1/B-9` 增量批量与首胜强杀的直接冲突；`B-10/C-9` `abort_all()` 不回收导致 NFR-3 与 AC-5 不可能达标；`B-11` 用 `starts_with("sat")` 解析响应；`B-12` 盲目同发 `get-model`/`get-unsat-core`；`A-13/C-3` 把非最小的 `get-unsat-core` 当作「最小冲突核」；`A-14` 硬编码组合逻辑名。

---

## 6.1 生成总则

### 6.1.1 脚本骨架

```
; PLM-GENERATED v2.1  spec=<spec_hash>  goal=<goal_id>  logic=<LOGIC>  gen=<codegen_hash>
; 本文件由 policylang codegen 生成，用于审计复算；请勿手工修改。
(set-logic <LOGIC>)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :print-success false)

<declarations>      ; 6.2.1 / 6.2.2
<bounds>            ; 6.2.4
<goal-asserts>      ; 6.3
(check-sat)
<get-payload>       ; (get-model) 与/或 (get-unsat-core)
```

### 6.1.2 命令序约束（`CO-1 … CO-6`）

| ID | 约束 | 理由 |
|---|---|---|
| `CO-1` | `(set-logic …)` 必须是**首个命令**（注释与空行除外） | SMT-LIB 要求 logic 在任何声明前确定 |
| `CO-2` | 所有 `(set-option …)` 在任何 `declare-fun` / `assert` 之前 | `:produce-*` 必须在首次 `check-sat` 前生效；统一前置以规避求解器差异 |
| `CO-3` | 所有 `(declare-fun …)` 在首个 `(assert …)` 之前 | 部分求解器对交错声明报 `unsupported` |
| `CO-4` | **一个查询文件只对应一个验证目标**，不使用 `(push)/(pop)` | 见 6.1.3 |
| `CO-5` | 文件为 UTF-8 **无 BOM**、LF 行尾、**末尾必须换行** | 跨平台一致性与 `query_hash` 可复算 |
| `CO-6` | 不发射 `(exit)`（由 stdin 关闭触发退出） | 简化 stdio 协议（6.5.2） |

### 6.1.3 一目标一查询的裁决（修正 `C-1` / `B-9`）

> **上游冲突**：FR-9 要求「支持基于 `(push)/(pop)` 的**单文件多验证目标批量求解**」，FR-8 要求「首个求解器返回确定判定后**立即 SIGKILL 其余进程**」。
> 二者在同一查询文件上**不可能同时成立**：首胜强杀会终止进程，使文件中后续 `(check-sat)` 的结果永久丢失；且多 `check-sat` 会产生多个响应，令 `stdout.starts_with("sat")` 式解析错位。

**裁决（DD-6.1）**：**默认路径放弃 `push/pop` 多目标**，改为：

```
一个 verify 目标  ⟶  一个查询文件  ⟶  一次独立竞速
多目标            ⟶  目标级并行（受 --goal-parallelism 与全局信号量约束）
```

**保留增量能力的两处例外**（均应显式启用，且都不与竞速共存）：

| 场景 | 开关 | 说明 |
|---|---|---|
| 单求解器批量排查 | `--incremental-single-solver` | 指定单一后端且 `--no-race`，使用 `push/pop` 批量；由 6.8 的响应流解析器按响应序号取第 n 个判定 |
| 核心最小化 | 自动（`--minimize-core`） | 见 6.9.3：最小化阶段在**单求解器会话**内用 `push/pop` + assumptions 迭代，不与竞速共存 |

> 上游 FR-9 的「增量验证」目标由上述两处例外共同满足，其原始表述（单文件批量）被**收窄**为「单求解器会话内增量」，这是可实现的语义。文档 `01 §4 FR-9` 已按此表述冻结。

### 6.1.4 命名规范（`NM-1 … NM-4`）

| ID | 对象 | 规则 |
|---|---|---|
| `NM-1` | 展平标量常量 | `scalar_symbol(D, i, f)`，见 `03 §3.2.4`（单一实现，`05 §6.5` 复用） |
| `NM-2` | 全局变量 | `PL_g_<escape(name)>` |
| `NM-3` | `:named` 标签 | 规则 `PLR__<policy>__<rule>`；分支 `PLB__<policy>__<branch>`；不变量否定 `PLI__<inv>`；互斥 `PLM__<policy>__<i>__<j>`；覆盖性否定 `PLC__<policy>`；除零 `PLS__<policy>__DIVZERO`；旧策略否定 `PLR__<policy>__OLD_NEG` |
| `NM-4` | `escape(s)` | 非 `[A-Za-z0-9_]` 字符替换为 `_u` + 4 位十六进制；标签总长 > 128 时截断并追加 8 位 SHA-256 前缀 |

- 标签**必须唯一**；编译期校验，冲突即 `E-DUP-LABEL`（exit 3）。
- 每个标签与 `(rule/branch/invariant, Span)` 的映射写入 `ast.labels` 表，供 6.9 归因与 `07 §7.3` 使用。

---

## 6.2 符号声明与边界断言

### 6.2.1 排序到 SMT-LIB2 的映射

| 排序 | 声明 | 附加约束 |
|---|---|---|
| `Int` | `(declare-fun <sym> () Int)` | `bound_{Int,[a,b]}` |
| `Real` | `(declare-fun <sym> () Real)` | `bound_{Real,[a,b]}` |
| `Bool` | `(declare-fun <sym> () Bool)` | 无 |
| `Str` | `(declare-fun <sym> () String)` | `bound_{Str,l..u}` |
| `BV(n)` | `(declare-fun <sym> () (_ BitVec n))` | 无（位宽即界） |
| `Enum(E)` | `(declare-fun <sym> () Int)` | `(or (= x 0) … (= x k−1))` |

> **决策 DD-6.2（Enum 编码，修正 `A-6`）**：上游 §4.1 写「`declare-datatypes` 代数数据类型**或**有界整数编码」，二者任选其一——未定论且后果重大。本规范**定性为有界整数编码**（枚举成员按声明序映射到 `0 … k−1`），理由：
> 1. datatype 编码会使逻辑档位离开 `QF_*` 标准集（datatype 属 `QF_UFDT`/`ALL`），与 6.4 的「最精确档位」目标直接冲突，并使 Bitwuzla 之外的组合路由复杂化；
> 2. 整数编码下 `Enum` 字段与 `Int` 字段共享 `LIA` 推理，`Enum` 与 `BV` 字段可并存于 `QF_BVLIA`；
> 3. 模型还原仅需查表（`07 §7.2`），无需解析 datatype 的 S-Expr（后者在跨求解器上格式差异较大）。
> 代价：反例报告中的枚举值需经映射表还原为成员名（已由 `07 §7.2` 覆盖）。
> 保留开关 `--enum-encoding=datatype`，仅在能力探测确认后端支持相应档位时可启用，默认 `int`。

### 6.2.2 声明发射顺序（确定性，`DET`）

```
1. 全局变量：按源码声明序
2. 域实例：按域声明序 → 实例索引升序（0 … N−1）→ 字段声明序
```
固定顺序是 `query_hash`（`07 §7.5`）可复算的**前提**（定理 `TH-10`）。

### 6.2.3 字面量编码规范（修正 `B-28`）

| 情形 | 编码 | 说明 |
|---|---|---|
| `Int` 非负 | `5` | 十进制 |
| `Int` 负 | `(- 5)` | SMT-LIB 无负字面量，须用前缀 `-` 的一元形式 |
| `Real`，分母 = 1 | `5.0` | SMT-LIB Decimal 字面量 |
| `Real`，分母 ≠ 1 | `(/ 5 3)` | 精确有理数，**禁止** `1.6666667` 之类近似（与 `03 §3.2.3 N-1` 一致） |
| `Int` 出现在 `Real` 位置 | `(to_real 5)` | 显式提升，无隐式转换（`N-4`） |
| `BV(n)` | `(_ bv5 32)` | **统一使用**十进制 `(_ bvN W)` 形式；不发射 `#x…`（规避不同求解器对十六进制宽度的隐式截断差异，见 `03 §3.12.3`） |
| `Bool` | `true` / `false` | |
| `String` | `"abc"` | SMT-LIB 2.6 规定引号内以 `""` 表示一个双引号字符；其余码点按字面（UTF-8）书写，**不**使用 `\xHH`（SMT-LIB 字串字面量不定义反斜杠转义） |

> **关键陷阱**：DSL 侧的 `"..."` 支持 `\n`、`\"`、`\xHH` 等转义（`04 §2`），但**转义在 AST 层即被解析为真实码点**，发射阶段不再有转义概念。`\\` 与 `\"` 的 DSL→SMT 差异必须由 P2（AST 构造）而非 P6（发射）承担，以避免双重转义。

### 6.2.4 边界断言 `Bnd` 发射

- 逐「字段实例」一条 `(assert (and …))`，**不带 `:named`**（`DD-3.1`，见 `03 §3.2.6`）
- `Bool` / `BV(n)` 字段不发射
- `Enum` 字段发射成员析取式
- 可选 `--emit-bounds=<per-symbol|grouped|none>`，默认 `per-symbol`（便于诊断定位到具体字段实例）
- `Bnd` 必须**先于**目标断言发射（`CO-3` 的延伸要求）
- **`Bnd` 可满足性预检**：`codegen` 之前先对 `Bnd` 单独执行一次轻量 `check-sat`（复用同一后端、不做竞速、超时 500ms）；若 `unsat` 直接报 `E-EMPTY-CARRIER`（exit 3），避免所有目标都返回「空核心 UNSAT」这一误导性结果。

---

## 6.3 验证目标编码

记号：`R_P ≜ ⋀{ ground(r) ∣ r ∈ rules(P) }`；`Br_P ≜ ⋁{ ground(b) ∣ b ∈ branches(P) }`；`M` 为状态空间（`03 §3.2.5`）。全部编码均满足 `Q = (assert Bnd) ∧ (assert π′)` 的反证范式，由 `TH-7` 保证可靠性与相对完备性。

### 6.3.1 `consistency(P)` — 策略集自洽性

**数学命题** `π ≜ ∃m ∈ M. R_P(m)`

**查询**
```
(assert (! <ground(r_1)> :named PLR__P__r_1))
…
(assert (! <ground(r_n)> :named PLR__P__r_n))
(check-sat)
(get-unsat-core)
(get-model)
```

| 判定 | 状态 | 诊断产出 |
|---|---|---|
| `sat` | `Pass` | 可选 `--show-witness`：给出一个合法配置摘要（advisory，不参与 gate） |
| `unsat` | `Fail` | 6.9 最小化核心 → 冲突规则集 + 源码行列跨度 |
| `unknown` | `UnknownReviewRequired` | 耗时明细与后端逐项状态 |
| 核心为空集 | `Error` | `E-EMPTY-CARRIER`（`Bnd` 自身不可满足） |

**边角**：`n = 0` 已被 `W12` 阻断（`E-EMPTYPOLICY`）。
**正确性**：`sat(Q) ⟺ ∃m ∈ M. R_P(m) ⟺ π`（`TH-7`）。∎

### 6.3.2 `invariant(Inv, P)` — 安全不变量

**数学命题** `π ≜ ∀m ∈ M. R_P(m) ⟹ ⟦ground(Inv)⟧m`

**查询**
```
(assert <ground(r_i)>)                       ; 规则断言：不带 :named（不进入核心）
(assert (! (not <ground(Inv)>) :named PLI__<Inv>))
(check-sat)
(get-model)
```

| 判定 | 状态 | 诊断产出 |
|---|---|---|
| `unsat` | `Pass` | 若核心**不含** `PLI__*` ⇒ `W-VACUOUS-INVARIANT`（见 6.3.7） |
| `sat` | `Fail` | 模型 → 业务反例 + `FIX-*` 修复建议（`07 §7.4`） |
| `unknown` | `UnknownReviewRequired` | — |

**设计要点**：只有 `¬Inv` 带标签，使 `(get-unsat-core)` 能区分「因不变量否定而 UNSAT（正常 PASS）」与「因策略自身矛盾而 UNSAT（空真 PASS）」。

### 6.3.3 `refines(P_new, P_old)` — 策略精化对比（双查询四态）

**数学命题** `π ≜ ∀m ∈ M. R_new(m) ⟹ R_old(m)`（新策略是旧策略的子集）

**查询（两条）**

```
Q1:                                    Q2:
(assert (! <ground(r)> :named          (assert (! <ground(r)> :named
        PLR__New__r))       ∀ r∈P_new          PLR__Old__r))       ∀ r∈P_old
(assert (! (not (and <r ∈ P_old>))     (assert (! (not (and <r ∈ P_new>))
        :named PLR__Old__OLD_NEG))             :named PLR__New__OLD_NEG))
(check-sat) (get-model)                (check-sat) (get-model)
```

**四态分类（修正 `A-16`/`C-12`）**

| `verdict(Q1)` | `verdict(Q2)` | `refinement_class` | 状态 | 业务含义 |
|---|---|---|---|---|
| `unsat` | `unsat` | `EQUIVALENT` | `Pass` | 两策略语义等价 |
| `unsat` | `sat` | `STRICT` | `Pass` | 新策略**严格更严**，无风险外溢 |
| `sat` | `unsat` | `WIDENED` | `Fail` | 新策略**扩大暴露面** |
| `sat` | `sat` | `INCOMPARABLE` | `Fail` | 两向均有反例，语义不可比 |
| 任一 `unknown` | — | `UNDETERMINED` | `UnknownReviewRequired` | — |

> 上游只有二元 `UNSAT=通过 / SAT=失败`，**无法表达「等价」与「可比性」**（`GateStatus` 三值不足以承载四态）。本规范通过独立字段 `refinement_class` 而非扩状态枚举解决（见 `07 §7.5` 的 `CheckDiagnostic`）。

**AC-3 核算**：`P_new` 允许 `port ∈ [80, 65535]`，`P_old` 允许 `port ∈ [1024, 65535]`。
`Q1` 可满足区 = `[80,65535] ∩ ¬[1024,65535] = [80,1023] ≠ ∅` ⇒ `sat`；`Q2` 可满足区 = `[1024,65535] ∩ ¬[80,65535] = ∅` ⇒ `unsat`。
⇒ `WIDENED` / `Fail`，反例模型满足 `port ∈ [80,1023]`（求解器通常返回边界值 `port = 80`，但不保证；报告须呈现**整个区间**而非单点，见 6.3.7 的「反例区间化」）。

**单查询模式** `--refines-single-query`：仅跑 `Q1`，`refinement_class = STRICT_OR_EQUIVALENT`（无法区分等价与严格）。默认双查询。

### 6.3.4 `completeness(P)` — 分支完备性

**前置（`FR-15`）**：`policy` 可声明 `branches { B1: <formula> … }`。若策略无 `branch` 声明而调用了 `verify completeness` ⇒ `E-NO-BRANCHES`（exit 3）。

**数学命题**

```
π ≜ ∀m ∈ M.  Br_P(m)                    （模式 A：全域完备）
π ≜ ∀m ∈ M.  R_{P0}(m) ⟹ Br_P(m)        （模式 B：P0 前提下的条件完备）
```

**查询**
```
模式 A:  (assert (! (not (or <ground(b_1)> … <ground(b_k)>)) :named PLC__<policy>))
模式 B:  (assert <ground(r)> for r ∈ P0)      ; 前提下界
         (assert (! (not (or …)) :named PLC__<policy>))
(check-sat)
(get-model)
```

| 判定 | 状态 | 诊断产出 |
|---|---|---|
| `unsat` | `Pass` | 全域无死区 |
| `sat` | `Fail` | 模型即**未被覆盖的输入死区**；输出 `FIX-*`（建议新增分支） |
| 核心为空 | `Error` | `E-EMPTY-CARRIER` |

**边角**：`k = 0` ⇒ `E-NO-BRANCHES`；分支排序非 `Bool` ⇒ `E-SORT-MISMATCH`（`W7`）。
**建议**：`completeness` 通过后自动追加 `mutex`（6.3.6）检查，二者共同构成「分支是输入域的一个划分」这一更强性质。

### 6.3.5 `safety(P)` — 除法全域性义务

**数学命题**（`03 §3.11.2`）

```
b̄ = ALG-2 collect_div_obligations(P) = ⟨b_1, …, b_k⟩
π ≜ ∀m ∈ M.  R_P(m) ⟹ ⋀_{j=1..k} ( b_j(m) ≠ 0 )
```

**查询**（**关键：查询本身不含任何除法**）
```
(assert <ground(r_i)>)                                  ; 策略断言（无名）
(assert (! (or (= <ground(b_1)> 0) … (= <ground(b_k)> 0)) :named PLS__<policy>__DIVZERO))
(check-sat)
(get-model)
```

| 判定 | 状态 | 诊断产出 |
|---|---|---|
| `unsat` | `Pass` | 绝对无除零风险 |
| `sat` | `Fail` | 模型给出触发除零的参数赋值 |
| `k = 0` | `Pass` | **必须**标注 `safety_vacuous: true` + `W-SAFETY-VACUOUS`（诚实性要求） |
| 核心不含 `PLS__*` | `Pass` | 空真 ⇒ `W-VACUOUS-SAFETY` |

> **架构收益**：因为义务查询只含**线性**分母表达式（由 `W8` 保证），该查询停留在 `QF_LIA`/`QF_LRA`，**不因除法的出现而降级逻辑档位**。这是「除法」与「可判定性」在架构上解耦的关键（`03 §3.11.5`）。
>
> **预处理**：除法线性化（`TH-4`）在 P5/P6 之间对 `R_P` 执行，因此 `R_P` 已是无 `/` 的形式；仅常量除数的 `div`/`mod` 保留（须能力探测确认后端支持，`06 §6.4.3`）。

### 6.3.6 `mutex(P)` — 分支两两互斥

**数学命题** `π ≜ ∀m ∈ M. R_P(m) ⟹ ⋀_{i<j} ¬( Br_i(m) ∧ Br_j(m) )`

**查询**：对每对 `(i, j)` 生成一个独立查询文件（`CO-4`）
```
(assert (! (and <ground(b_i)> <ground(b_j)>) :named PLM__<policy>__<i>__<j>))
(check-sat)
(get-model)
```
| 判定 | 状态 | 诊断 |
|---|---|---|
| `unsat` | `Pass` | 该对互斥 |
| `sat` | `Fail` | 模型落在重叠区；输出重叠区间描述 |
| 对数 > `--mutex-max-pairs`（默认 64） | `Error` | `E-MUTEX-BUDGET`（提示先合并分支） |

### 6.3.7 编码汇总表与空真检测

**汇总表**

| 目标 | `π` | 查询断言 | PASS | FAIL 诊断 | 查询数 | 含除法？ | 空真检测 |
|---|---|---|---|---|---|---|---|
| `consistency` | `∃m∈M. R_P(m)` | `R_P`（全带标签）+ `Bnd` | `sat` | `unsat` → Core | 1 | 是（可能） | 不适用 |
| `invariant` | `∀m. R_P ⟹ Inv` | `R_P`（无名）+ `¬Inv` | `unsat` | `sat` → Model | 1 | 是（可能） | 核心缺 `PLI__*` |
| `refines` | `∀m. R_new ⟹ R_old` | `Q1` + `Q2` | 见四态表 | `sat` → Model | 2 | 是（可能） | 核心缺 `*_OLD_NEG` |
| `completeness` | `∀m. Br_P` | `¬Br_P` | `unsat` | `sat` → Model | 1 | 是（可能） | `E-EMPTY-CARRIER` |
| `safety` | `∀m. R_P ⟹ b̄ ≠ 0` | `R_P` + `⋁ b_j = 0` | `unsat` | `sat` → Model | 1 | **否** | 核心缺 `PLS__*` |
| `mutex` | `∀m. ⋀_{i<j}¬(Br_i∧Br_j)` | `Br_i ∧ Br_j` | `unsat` | `sat` → Model | `C(k,2)` | 是（可能） | 不适用 |

**空真（Vacuous Truth）检测**（新增，修正上游「静默通过」风险）

> 反证法编码存在一类**隐蔽的假阳性**：若前提 `R_P`（或 `R_new`）本身**不可满足**，则 `R_P ⟹ X` 对任意 `X` 恒真，验证会「通过」但毫无意义。

| 目标 | 空真条件 | 检测方法（零额外求解开销） | 告警 |
|---|---|---|---|
| `invariant` | `R_P` 不可满足 | `Q` 的 Unsat Core **不含** `PLI__*` | `W-VACUOUS-INVARIANT` → 建议补跑 `verify consistency of P` |
| `refines` | `R_new` 不可满足 | `Q1` 的 Core **不含** `PLR__*_OLD_NEG` | `W-VACUOUS-REFINES` |
| `safety` | `R_P` 不可满足 | Core **不含** `PLS__*` | `W-VACUOUS-SAFETY` |
| `completeness` | `Bnd` 不可满足 | Core 为空 | `E-EMPTY-CARRIER`（exit 3，由 6.2.4 预检提前拦截） |

检测**零额外开销**的原理：`(get-unsat-core)` 返回的子集若不含那条唯一的反证断言，则不可满足性完全由前提贡献。

**反例区间化**（新增，提升可读性）
对含连续排序（`Int`/`Real`）字段的反例，额外发射一次「反例邻域探测」查询，取该字段在当前模型下的可自由变动区间：
```
(push 1)
(assert (= <该字段> <模型值>))     ; 固定其余字段与已得模型一致
(pop 1)
```
实现为可选优化 `--counterexample-interval`（默认开启，最多 8 个字段，每个 1 次查询，受 500ms 预算约束）。AC-3 的 `[80,1023]` 即由该机制给出，避免用户误以为只有 `port = 80` 一处违规。

---

## 6.4 逻辑档位推导与能力探测

### 6.4.1 足迹收集（`LogicProfile`）

```rust
#[derive(Debug, Default, Clone)]
pub struct LogicProfile {
    pub uses_int: bool,
    pub uses_real: bool,
    pub uses_bv: bool,
    pub bv_widths: BTreeSet<usize>,      // 确定性
    pub uses_string: bool,
    pub uses_regex: bool,
    pub uses_enum: bool,                 // 计入 uses_int（DD-6.2）
    pub uses_div_const: bool,
    pub uses_mod_const: bool,
    pub nonlinear_opt_in: bool,
    pub violations: Vec<Violation>,      // 非空即 E-NONLINEAR / E-REGEX-*
}
```

**赋值规则（修正 `B-7`）**：上游 §3.1 的 `LogicProfile` **只有 `check_expr` 的分支结构，没有任何把 `uses_*` 置位的语句**——因此 `deduce_smt_logic()` 恒返回 `ALL`，理论路由完全失效。本规范要求：`uses_*` 在 `check_expr` 的最后 `_ => {}` 之前由**排序驱动**置位：

| 遇到 | 置位 |
|---|---|
| `Expr::IntLit` / Int 排序的 `Var`/`Flat` | `uses_int` |
| `Expr::RealLit` / Real 排序 | `uses_real` |
| BV 排序的 `Var`/`Flat` / `bv*` 运算节点 | `uses_bv`（并记入 `bv_widths`） |
| `Str` 排序 / `str.len` / `str.<` / 字串字面量 | `uses_string`（**同时置 `uses_int`**，因 `str.len` 返回 `Int`） |
| `Formula::MatchesAll` | `uses_regex` + `uses_string` + `uses_int` |
| `Formula::Unique` / `InCidr` / `InRange` | 按字段排序置位 |
| `div`/`mod` 且除数为常量 | `uses_div_const` / `uses_mod_const`（并置 `uses_int`） |
| `to_real` | `uses_real` + `uses_int` |

### 6.4.2 档位真值表（完整，修正 `A-14`）

> `uses_string = true` 必然蕴含 `uses_int = true`（`str.len : Int`），故 16 种组合中仅 12 种可达。

| `Str` | `BV` | `Int` | `Real` | 候选档位 | 备注 |
|---|---|---|---|---|---|
| F | F | F | F | `QF_UF` | 纯布尔 / 纯枚举 |
| F | F | T | F | `QF_LIA` | |
| F | F | F | T | `QF_LRA` | |
| F | F | T | T | `QF_LIRA` | |
| F | T | F | F | `QF_BV` | |
| F | T | T | F | `QF_BVLIA` | 候选名，须探测 |
| F | T | F | T | `QF_BVLRA` | 候选名，须探测 |
| F | T | T | T | `QF_BVLIRA` | 候选名，须探测；探测失败回落 `ALL` |
| T | F | T | F | `QF_SLIA` | |
| T | F | T | T | `ALL` | 字串与实数无标准组合档位 ⇒ 回落 + `W-LOGIC-FALLBACK` |
| T | T | T | F | `ALL` | 同上（串与位向量） |
| T | T | T | T | `ALL` | 同上 |
| 任意 + `nonlinear_opt_in` | | | | `ALL` | 且目标强制 `UnknownReviewRequired`（`TH-3a`） |

**候选名回落链**：`<主候选>` → `ALL`。若 `--strict-logic` 且发生回落 ⇒ `E-LOGIC-UNSUPPORTED`（exit 4）。

> **【补全 `A-14`】** 上游 `deduce_smt_logic` 的 `match` 仅列 6 种组合并用 `_ => "ALL"` 兜底，同时把 `(true, true, …)`（串 + 位向量）等可达组合遗漏。更根本的问题在于：**组合逻辑名在 SMT-LIB 各版本中的收录状态、以及其在具体求解器版本中的支持度都存在差异**，硬编码逻辑名必然产生「路由到不支持该逻辑的后端 → `(error "unsupported logic")`」这一上游 FR-8 正要规避的故障。本规范因此把逻辑名降级为**候选名**，以 6.4.3 的**运行期能力探测**作为权威。

### 6.4.3 `ALG-3` 后端能力探测（`FR-17`）

```
ALG-3  probe_backend(path, version) → Capability

P1  执行 `path --version`；非零退出或超时 1s ⇒ unavailable
P2  对候选逻辑名逐一执行冒烟脚本（stdin 投喂，超时 1s）：
        (set-logic L)
        (declare-fun pl_probe_int () Int)
        (declare-fun pl_probe_bv  () (_ BitVec 8))
        (declare-fun pl_probe_str () String)
        (assert (= pl_probe_int 0))
        (assert (= (bvand pl_probe_bv (_ bv1 8)) (_ bv1 8)))
        (assert (str.in_re pl_probe_str (re.inter (re.* re.allchar) (re.range "a" "z"))))
        (check-sat)
    期望响应序列首项为 sat。得到 unsat / unknown / (error ...) / 无响应 ⇒ 不支持。
P3  探测特性位（各自微型脚本 + 期望响应匹配）：
        f_model            对 sat 查询发 (get-model) 并期待 s-expr
        f_unsat_core       对 unsat 查询发 (get-unsat-core) 并期待 ( ... )
        f_incremental      对 (push 1)(check-sat)(pop 1)(check-sat) 期待两次判定
        f_div_mod          单常量除数的 (div …) 查询期待 sat
        f_regex_inter      含 re.inter 的查询期待 sat
        f_proof            发 (get-proof) 且不返回 (error ...)
P4  结果落盘 .policylang/capability-<env_hash>.json（缓存），当 policylang.lock 变化时失效
```

### 6.4.4 基线能力矩阵（**须以实测为准**）

| 后端 | `QF_LIA` | `QF_LRA` | `QF_LIRA` | `QF_BV` | `QF_BVLIA` | `QF_SLIA` | `div/mod` | `re.inter` | 增量 | UnsatCore | 证明 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Z3 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| CVC5 | ✓ | ✓ | ✓ | ✓ | 须探测 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ (Alethe) |
| Bitwuzla | ✗ | ✗ | ✗ | ✓ | ✗ | ✗ | ✗ | ✗ | ✓ | ✓ | ✗ |

**路由结论（与上游 FR-8 / AC-5 的一致性核对）**

| 场景 | 胜任后端集合 | 与上游声明 | 结论 |
|---|---|---|---|
| 含 `String` + `re.inter`（`QF_SLIA`） | `{Z3, CVC5}` | 上游 FR-8/AC-5：「仅调度 Z3 与 CVC5，不调用 Bitwuzla」 | **一致 ✓** |
| 纯位向量网段（`QF_BV`） | `{Z3, CVC5, Bitwuzla}` | 上游 FR-8：「优先调度 Bitwuzla、Z3 与 CVC5」 | **一致 ✓** |
| 含线性整数 / 常量除数 `div`（`QF_LIA`） | `{Z3, CVC5}` | 上游未明确 | 本规范补（Bitwuzla 无整数理论） |
| 组合 `BV + Int`（`QF_BVLIA`） | 须探测，通常 `{Z3}` | 上游未涉及 | 单后端 ⇒ `W-SINGLE-BACKEND` |

**单后端退化的补偿**：`|S| = 1` 时无竞速收益，`--timeout` 自动放大 `×2`（上限 30s）并在报告中标注 `race_degraded: true`。

### 6.4.5 后端选择规则（确定性函数）

```
1. S ← { b ∈ backends ∣ capability[b].logics[候选档位] = supported }
2. 按配置文件中 backends 的**声明顺序**排序（确定性，保证 query_hash 稳定）
3. |S| = 0  ⇒  E-LOGIC-UNSUPPORTED（exit 4）
4. |S| = 1  ⇒  单后端模式（无竞速，超时 ×2）
5. |S| ≥ 2  ⇒  竞速模式
```

---

## 6.5 求解器调用规范

### 6.5.1 命令行与协议

| 后端 | 命令行 | 输入 | 输出 |
|---|---|---|---|
| `z3` | `z3 -in -smt2 -T:<soft_timeout_sec>` | stdin 投喂脚本 | stdout 响应流 |
| `cvc5` | `cvc5 --lang=smt2 --incremental --produce-models --produce-unsat-cores` | stdin | stdout |
| `bitwuzla` | `bitwuzla --lang=smt2` | stdin | stdout |

- **stdin 必须显式关闭**（`ChildStdin` drop）以发送 EOF；三个后端均采用「读至 EOF 再求解」的 stdin 语义，不关闭 stdin 会导致挂起。
- `stderr` 默认丢弃；`--verbose` 时以 4KB 环形缓冲保留尾部用于诊断。
- 求解器**不得**被传入宿主环境中的敏感变量：显式构造白名单环境（`PATH`、`TMPDIR`、locale）。

### 6.5.2 版本锁定 `policylang.lock`（`FR-17`）

```toml
lock_version = 1
[[solver]]
name = "z3"
version = "4.13.0"
binary_sha256 = "9f2c…"
path = "/usr/local/bin/z3"
required = true
```
- 启动时校验 `version` 与 `binary_sha256`；不符 ⇒ `E-SOLVER-VERSION`（exit 4）
- `--allow-version-drift` 降级为 `W-SOLVER-DRIFT` 并在报告中记录实际版本
- 缺失二进制且 `required = true` ⇒ `E-SOLVER-MISSING`（exit 4）
- **不静默降级**：`required = false` 的后端缺失仅记 `W-SOLVER-MISSING` 并从 `S` 中剔除

### 6.5.3 资源限制与沙箱（修正 `B-20`）

| 平台 | 机制 |
|---|---|
| Unix | `setrlimit(RLIMIT_AS, 512 MiB)`、`RLIMIT_CPU`、`RLIMIT_NOFILE`、`setsid()` 建立独立进程组；可选 `unshare` 网络命名空间 |
| Windows | `CreateJobObject` + `JOB_OBJECT_LIMIT_PROCESS_MEMORY` / `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE` + `TerminateJobObject` |
| 通用 | 工作目录设为独立临时目录；求解器不接触策略源目录以外的路径；禁止网络（可配置） |

---

## 6.6 竞速编排

### 6.6.1 `SolverOrchestra` 修正版（修正 `B-10` / `C-9`）

> **上游缺陷（P0）**：`join_set.abort_all()` 是**非阻塞**的——它只标记任务取消并唤醒它们，**不等待任务实际结束**。因此 `solve_race()` 在 `abort_all()` 之后立即返回时，被取消任务所持有的 `tokio::process::Child` **可能尚未被 drop**，`kill_on_drop` 也就尚未触发 `SIGKILL`。后果：
> 1. `NFR-3` 的「竞速结束后子进程残留率为 0」**不成立**；
> 2. `AC-5` 的「Z3 在 10ms 内被 SIGKILL 终止，无后台残留」**不可能稳定通过**（验收指标本身不可实现）。

**修正实现**

```rust
use std::time::Instant;
use tokio::task::JoinSet;

pub async fn solve_race(&self, logic: &str, query: &str, deadline: Instant)
    -> RaceOutcome
{
    let mut set: JoinSet<BackendResult> = JoinSet::new();
    let mut in_flight = 0usize;

    for backend in self.eligible(logic) {            // 6.4.5 的确定性顺序
        in_flight += 1;
        let (cmd, args, query) = (backend.cmd.clone(), backend.args.clone(), query.to_owned());
        set.spawn(async move { run_backend(&cmd, &args, &query).await });
    }

    let mut unsat_votes = 0usize;

    let outcome = tokio::select! {
        biased;
        _ = tokio::time::sleep_until(deadline.into()) => RaceOutcome::Timeout,
        v = async {
            while let Some(res) = set.join_next().await {
                let Ok(r) = res else { continue };
                match r.verdict {
                    // SAT：有模型可独立重放，首胜即接受
                    Verdict::Sat   => return RaceOutcome::Sat(r),
                    // UNSAT：按 --unsat-confirm 策略
                    Verdict::Unsat => {
                        unsat_votes += 1;
                        if unsat_votes >= self.unsat_confirm_quorum() {   // 默认 2
                            return RaceOutcome::Unsat(r);
                        }
                    }
                    Verdict::Unknown => { /* 记录并继续等下一个 */ }
                }
            }
            RaceOutcome::AllUnknown { in_flight }
        } => v,
    };

    // ★ 关键修正：必须 await 回收，不能只 abort_all() 后返回
    //   shutdown() = abort_all() + 循环 join_next() 直至 None，保证每个 Child 被 drop
    set.shutdown().await;

    debug_assert!(set.is_empty(), "所有求解器子进程必须已回收");
    outcome
}
```

**兼容实现**（tokio < 1.31 无 `JoinSet::shutdown`）
```rust
set.abort_all();
while set.join_next().await.is_some() {}   // 阻塞排空，触发 kill_on_drop
```

**强杀时长指标（修正 AC-5）**
> 定义：`t_kill ≜ (` 主控首次读到某后端的确定判定 `)` → (` 该后端进程组从进程表中消失 `)`
> 指标：`P99(t_kill) ≤ 50 ms`（进程表以 20ms 间隔采样 `ps -eo pid,pgid,comm`）。
> 上游给出的「10ms 内」在 OS 调度粒度下不可稳定测量（Linux `SIGKILL` 投递 + 父进程 `waitpid` 回收本身即可达数毫秒，且 `shutdown().await` 是**排空所有**后端而非只回收胜者），故修正为 50ms P99 并在 `10 §10.2 AC-5` 声明判定方法。

**首胜顺序无关性**：`select!` 用 `biased` 只影响超时与就绪的优先级，不保证后端间的到达顺序——这正确反映了竞速的**非确定性**，也是 `proof_hash` 必须排除 winner 与耗时的原因（`07 §7.5`）。

### 6.6.2 判定确认策略

| `--unsat-confirm` | 语义 | 适用 |
|---|---|---|
| `none` | 首个 `unsat` 即接受 | 追求最低延迟，信任后端 |
| `two-of-n`（**默认**） | 需 2 个后端一致报 `unsat`（或直到 deadline）；若第 2 个报 `sat` ⇒ `E-XVALIDATE-MISMATCH` | 平衡速度与可信度 |
| `proof` | 首个 `unsat` 后请求 `(get-proof)`，由外部 Alethe 检查器验证 | 最高可信度，需 `f_proof` 能力 |

> **对上游「首胜即止」的必要修正**：`unsat` 无模型可复核，因此需要独立证据。纯 `sat` 路径**仍严格首胜即止**（因模型可被 6.7.1 独立重放）。`01 §4 FR-8` 已按此表述冻结。

### 6.6.3 调度模型（修正 `C-11`）

> **上游隐含冲突**：`NFR-4` 要求「单机支持 100 并发验证请求」，`FR-8` 要求「每个目标启动 3 个求解器子进程」。朴素实现会产生 **100 × 3 = 300 个并发子进程**，超出典型单机资源模型，且上游**完全未定义资源模型**。

**三层限流模型**

```
请求层   Semaphore(--concurrency, 默认 100)
         指标含义为「稳定排队与调度」，而非「同时 300 个进程」
  ↓
目标层   单请求内目标串行（--goal-parallelism 默认 1）
  ↓
后端层   Semaphore(--solver-slots, 默认 min(8, cpu_cores / 3))
         每个运行中的目标最多占用 |S| 个 slot
```

**峰值进程数上界** = `--solver-slots` + 主控协程数，**不随并发请求数增长**。
队列指标：`queue_depth`、`queue_wait_p99` 写入报告与 KPI（`07 §7.10`）。

### 6.6.4 超时分级（补全上游缺失）

| 层级 | 参数 | 默认 | 语义 |
|---|---|---|---|
| 后端软超时 | `--solver-timeout` | `0.6 × --timeout` | 传给后端自身（Z3 `-T`），到期由后端自行退出并输出 `unknown` |
| 目标硬截止 | `--timeout` | `3000 ms` | 该目标全体后端的共享 `deadline`，到期即 `shutdown()` 全员回收 |
| 请求总截止 | `--request-timeout` | `--timeout × |goals| + 30s` | 整个 CLI 调用的上界，超时 ⇒ `Error` / exit 4 |
| 探测超时 | `--probe-timeout` | `1000 ms` | `ALG-3` 单次冒烟 |
| 预检超时 | 固定 | `500 ms` | `Bnd` 可满足性预检（6.2.4） |

**语义要点**：软超时早于硬截止，给后端**体面退出并返回 `unknown`** 的机会；若后端连软超时都未响应（挂起），硬截止的 `shutdown()` 兜底。这样既避免无意义的进程强杀，又保证永不挂起。

### 6.6.5 跨平台强杀语义（修正 `O-11`）

上游只写「发送 `SIGKILL` 信号」——这是 **Unix 专有**语义，在 Windows 上不存在。本规范：

| 平台 | 进程组建立 | 强杀 | 覆盖范围 |
|---|---|---|---|
| Unix | 子进程 `setsid()` 成为进程组首，记录 `pgid` | `killpg(-pgid, SIGKILL)` | 含后端可能派生的**孙进程** |
| Windows | `CreateJobObject` 并 `AssignProcessToJobObject` | `TerminateJobObject` | 含 Job 内全部进程 |

`kill_on_drop(true)` 保留为**最后防线**（仅覆盖直接子进程），主防线是进程组/Job 级强杀。两者并存以覆盖「drop 顺序异常」等边界。

---

## 6.7 交叉验证（`FR-9`）

### 6.7.1 SAT 路径：模型重放（Model Replay）

> **数学依据**：若一个显式赋值 `m` 使全部断言为真，则「存在满足赋值」被**构造性证明**，无需信任求解器。

| 要求 | 规范 |
|---|---|
| 求值器 | 独立实现 `PLM-Eval`，**不共享** codegen 的任何代码路径（避免同源缺陷） |
| `Int` | `i128`，每步溢出检查；溢出 ⇒ `E-INTERNAL`（exit 4） |
| `Real` | `num-rational::BigRational` **精确有理数**；**严禁 `f64`**（与 `03 §3.2.3 N-1` 一致，浮点比较不可靠） |
| `BV(n)` | `u128` + 宽度掩码，位运算后按 `2^n` 取模 |
| `String` | `Vec<char>` 码点序列；`str.len` 计码点数 |
| 正则 | 在 `R_sub` 上构造 NFA 后模拟（或复用 `regex-automata`），**不用** PCRE 引擎 |
| 重放断言集 | `Bnd` ∪ 目标断言 ∪ 反证断言，**全部**必须为真 |
| 通过 | `sat` 判定被独立证明 ⇒ 可放心 `Fail` 判为反例 |
| 失败 | `E-XVALIDATE-MISMATCH`，`overall_status = Error`，exit 4，并落盘复现包 |
| 关闭 | `--no-cross-validate`（不推荐，报告中标注 `cross_validated: false`） |

### 6.7.2 UNSAT 路径：多后端一致 + 可选证明检查

| 模式 | 手段 | 强度 |
|---|---|---|
| `two-of-n`（默认） | 两个独立后端独立报 `unsat` | 中（共同缺陷概率低） |
| `proof` | Z3 `(set-option :produce-proofs true)` + `(get-proof)`；CVC5 `--proof-format-mode=alethe`；外部 `carcara check` 验证 | 高（机器可验证证明） |
| 证明器不可用 | 降级 `two-of-n` + `W-PROOF-UNAVAILABLE` | 中 |

### 6.7.3 不一致处置（修正 `B-13` 的静默失败）

| 情形 | 处置 |
|---|---|
| 两后端判定相反（`sat` vs `unsat`） | `E-XVALIDATE-MISMATCH`（exit 4）；保存双方响应原文 + 生成的脚本 + 后端版本，写入 `.policylang/anomalies.jsonl` |
| 模型重放失败 | 同上 |
| 同一逻辑档位在 30 天内累计 3 次不一致 | 熔断该档位（标记 `quarantined`），后续该档位强制 `UnknownReviewRequired`，并登记 `RISK-*` |
| 后端 `spawn` 失败 | 记为该后端 `Unavailable` 并从竞速集中剔除；若 `S` 随之变空 ⇒ `E-SOLVER-MISSING`（exit 4）。**禁止静默忽略**（上游 `map_err(|e| e.to_string())` 后丢弃的做法被废止） |

---

## 6.8 响应流解析状态机（修正 `B-11` / `B-12`）

### 6.8.1 为什么必须按响应流而非按行解析

上游的判定提取是 `stdout.starts_with("sat")`。它有三处缺陷：
1. **多响应对齐失效**：一个脚本含 `(check-sat) (get-unsat-core)` 时输出为 `unsat\n(\n…\n)`；含多组时依次排列，`starts_with` 只能看到第一个响应。
2. **匹配过宽**：`sat` 前缀会误匹配任何以 `sat` 开头的非标准输出（如后端自定义的状态行）。
3. **未处理前导空白 / CRLF / BOM / `success`**：`(set-option :print-success true)` 未关闭时首个响应是 `success`，`starts_with` 全部落空。

### 6.8.2 状态机

```
                     ┌──────────────────────────────────────────┐
                     │              ResponseStream              │
                     └──────────────────────────────────────────┘

 Idle ──'sat'|'unsat'|'unknown'──▶ Verdict(n) ──'('──▶ Payload(n) ──┐
   │                                    ▲                            │
   │  'success'|'unsupported'           └────────── 下一响应 ────────┘
   │  '(error "…")'  ──▶ 按 6.8.3 分类后忽略
   └─ EOF ──▶ Done(responses[])
```

```rust
pub enum Response {
    Verdict(VerdictKind),                 // Sat | Unsat | Unknown
    Payload(Sexp),                        // model 或 unsat-core 的 S-表达式
    Error(String),                        // (error "...")
    Ignorable,                            // success | unsupported
}
pub struct ResponseStream { pub responses: Vec<Response> }
```

**规则**
- `R-1` 响应序号 `n` 与脚本中第 `n` 个「产出响应」的命令（`check-sat` / `get-model` / `get-unsat-core`）一一对应；`set-logic`、`set-option`、`declare-fun`、`assert` 默认不产出响应（`:print-success false` 时）。
- `R-2` tokenizer 必须处理：UTF-8 BOM、`\r\n`、连续空行、`;` 行注释、`|quoted symbol|`、`"str""esc"`、`(_ bv5 32)` 三元素列表。
- `R-3` 目标判定取「第一个 `Verdict`」；模型取「第一个 `Payload` 且紧跟在 `Verdict(Sat)` 之后」；核心取「第一个 `Payload` 且紧跟在 `Verdict(Unsat)` 之后」。
- `R-4` **禁止**使用 `starts_with` 判断判定。

### 6.8.3 容错与错误分类

| 响应 | 分类 | 处置 |
|---|---|---|
| `success` | `Ignorable` | 忽略（`:print-success false` 后通常不出现） |
| `unsupported` | `Ignorable` + `W-UNSUPPORTED-CMD` | 记录；若涉及关键命令（`get-model`）则降级为 `Error` |
| `(error "model is not available")` | **预期错配** | 忽略（6.1.1 同发 `get-model` 与 `get-unsat-core` 的必然结果） |
| `(error "no unsat core available")` | **预期错配** | 忽略 |
| 其他 `(error "…")` | `Error` | `E-SOLVER-PROTOCOL`（exit 4） |
| 无任何 `Verdict` 且进程正常退出 | `Error` | `E-SOLVER-PROTOCOL`（exit 4） |
| `Verdict` 数少于 `check-sat` 数 | `Error` | 同上 |
| 非 UTF-8 输出 | 容错 | `from_utf8_lossy` + `W-NONUTF8` |
| stdout > 64 MiB | 截断 | `E-SOLVER-PROTOCOL`（防内存 DoS，对应 `RISK` 安全项） |
| stderr 非空但 stdout 完整 | 忽略（`--verbose` 时采集） | `W-SOLVER-STDERR` |

> **关于「同发 `get-model` 与 `get-unsat-core`」的设计**：SMT-LIB 脚本是静态文本，无法在求解前知道结果是 `sat` 还是 `unsat`；而 `consistency` / `refines` 两种结果都需要 payload。因此二者同发，并把必然出现的错配 `(error …)` 归为**预期响应**。备选方案 `--split-queries`：为 `sat` 与 `unsat` 各生成一个脚本（牺牲 2× 求解成本换取零错配），默认关闭。

---

## 6.9 Unsat Core 最小化（修正 `A-13` / `C-3`）

### 6.9.1 问题陈述

`(get-unsat-core)` 返回的是**一个**不可满足的 `:named` 断言子集，**不保证极小或最小**：Z3 与 CVC5 都会返回「足够用」的子集，其中常含与冲突无关的规则。上游 v2.0 在 §4.1、`FR-7`、`G-6` 三处声称输出「**最小**冲突核」，与 API 实际语义不符——这是**规格与实际能力的偏差**，会导致用户按报告去删无关规则。

### 6.9.2 `ALG-4` 两阶段最小化

**阶段 1：assumption-based 核心提取（一次求解）**

因为 SMT-LIB 的 `check-sat-assuming` 只接受**布尔假设变量**，故把每条带标签的断言改写为「受守卫保护」形式：

```
(declare-fun pl_on_Rule_A () Bool)                       ; 每条规则一个守卫
(assert (! (=> pl_on_Rule_A <ground(ruleA)>) :named PLR__P__RuleA))
…
(check-sat-assuming (pl_on_Rule_A pl_on_Rule_B …))        ; 全部开启
(get-unsat-core)                                          ; 返回假设的子集 ⊆ {pl_on_*}
```

阶段 1 的产出 `C₀ ⊆ {PLR__*}` 是**求解器给出的候选核心**，仍可能非最小。

**阶段 2：deletion-based 精化（最多 `--minimize-budget` 次求解）**

```
ALG-4  minimize(C₀):
  active ← C₀
  for c ∈ C₀（按 NM-3 命名序，确定性）:
      S ← active ∖ {c}
      (check-sat-assuming S)
      if unsat:  active ← S          ; c 冗余，永久剔除
  return active
```

**会话复用**：阶段 2 在**单个求解器会话**内以 `(check-sat-assuming …)` 原地迭代，无需重发脚本——这既是性能关键，也说明「增量能力」在本框架中的正确落点是**核心最小化**而非多目标批量（`DD-6.1`）。

### 6.9.3 保证与预算

| 性质 | 陈述 | 依据 |
|---|---|---|
| 可靠性 | 返回的 `C₀` 与 `active` 均**不可满足** | 每次 `check-sat-assuming` 的 `unsat` 结论（`TH-8`） |
| 相对最小性 | 预算内每个 `c ∈ active` 都是**必需的**（去掉即变为可满足） | `ALG-4` 的剔除判据 |
| 最小性 | 若预算耗尽，`active` 仍是不可满足的**极小**集，但不保证**全局最小**（基数是 NP-hard 的） | `core_minimal: false` 标注 |
| 复杂度 | `O(|C₀|)` 次假设求解 | — |

**预算**：`--minimize-budget` 默认 `64` 次假设求解，`--minimize-timeout` 默认 `1s`（与目标 `--timeout` 独立计费）。
**关闭**：`--no-minimize-core` ⇒ 直接使用阶段 1 的 `C₀`，标注 `core_minimal: false`。

> **诚实性要求**：报告字段 `conflict_core.minimal` 必须如实反映是否在预算内达到极小，禁止无条件声称「最小」（上游 `G-6` 的表述已按此修正）。

### 6.9.4 归因（`07 §7.3` 的输入）

`C₀`/`active` 中的每个 `PLR__<policy>__<rule>` 经 `NM-3` 标签表反查：
```
PLR__P__RuleA  ⟶  (policy = P, rule = RuleA, span = {start_line, start_col, end_line, end_col})
```
输出 `RuleConflictSpan[]`（`07 §7.5` 的 `conflicting_rules`），并在 `(get-unsat-core)` 未返回任何我们注入的标签（即 `C₀ = ∅`）时判定为 `E-EMPTY-CARRIER`（`Bnd` 自身不可满足，见 6.2.4 预检的兜底路径）。

### 6.9.5 定理 `TH-8`（Core Soundness）

> 设 `C` 为 `ALG-4` 返回的标签集，`Assert(C) ≜ ⋀{ r_i ∣ PLR__i ∈ C }`。则 `Assert(C)` 关于 `Bnd` 不可满足。
> **证明**：`ALG-4` 返回的 `active` 是某次 `(check-sat-assuming S)` 返回 `unsat` 的 `S`（阶段 1 的全集或阶段 2 的某轮 `S`）；`check-sat-assuming S` 的 `unsat` 语义恰为 `Bnd ∧ ⋀{ r_i ∣ i ∈ S }` 不可满足。故 `Assert(active)` 不可满足。∎
>
> **推论**：报告中的冲突规则集**确实**导致策略死锁，不存在「报告了无关规则」的假归因（但可能遗漏同属必要的其他规则，故仍需 `core_minimal` 标注）。

---

## 6.10 求解性能工程

| 手段 | 说明 | 关联指标 |
|---|---|---|
| 求解器常驻池 | `--solver-pool` 预启动 `--solver-slots` 个后端进程，每次查询前发 `(reset)` 复位会话，避免 30–80 ms 冷启动 | `NFR-1` P99 |
| 查询结果缓存 | 以 `query_hash`（`07 §7.5`）为键缓存判定；同 spec + 同 logic + 同后端集合 ⇒ 命中 | CI 场景重复验证 |
| 大写串发射 | `Vec<u8>` 一次性 `String::from_utf8`，禁止 `format!` 逐段拼接（`G = 10⁶` 时 `format!` 会成为瓶颈） | `NFR-2b` |
| CSE 复用 | 同一 `(str.in_re …)` 子式跨规则复用为 `(let …)`（`03 §3.6` 的 `CSE-1`） | 文本规模与求解规模 |
| 逻辑档位最小化 | 6.4.2 选**最精确**档位而非 `ALL`，可直接选取更合适的判定过程 | `NFR-1`、`NFR-5` |
| 单后端补偿 | `race_degraded` 时 `--timeout ×2` | `NFR-5` |
| 慢目标告警 | 单目标 > 3 s 输出 `W-SLOW-GOAL` 并在报告标记 | 回归定位 |

**基准设计**见 `10 §10.4`（`BENCH-1` ~ `BENCH-6`），每个基准均须绑定 `--max-groundings` 与 `--timeout` 具体数值，否则指标不可证伪（修正 `C-8` / `C-15`）。
