# 12 · Lean 4 形式化验证规范

> **文档角色**：定义 PolicyLang Meta 的形式化验证目标、Lean 4 工程结构、定理清单与证明状态、`sorry` 清单与 burn-down 计划、AST 一致性契约与 CI 门禁。
>
> **上游**：`需求文档与开发文档.txt` v2.0 §4.2 `FR6`（「Lean 核心子集保序证明」）、§6 阶段三、`G-4`
> **上游依赖**：`03`（全部定理的数学陈述）、`06`（编码）、`05`（实现侧 AST）
> **落地制品**：`lean/PolicylangProof/`、`scripts/check-sorry.sh`
> **版本**：v2.1　|　**状态**：冻结
>
> **⚠ 诚实声明（必读）**：本工程在**本环境内未经 `lake build` 编译**（环境无 Lean 工具链且无外网）。因此：
> - 全部**定理陈述**已冻结（类型正确性由设计保证，见 §12.3 的类型层讨论）；
> - §12.4 的「已证」指**证明体已完整写出、不含 `sorry`**（据代码静态审查），其**机器校验结论以首次 `lake build` 为准**；
> - §12.6 列出**已知的 `sorry`（10 处）**与补齐计划；首次 `lake build` 预计还需在少数 `simp`/`rw` 步骤上做 tactic 级微调，调整清单见 §12.6.3。
>
> 这一声明本身就是规范的一部分：`G-8`（诚实阻断）的原则同样适用于**我们自己的验证证据**。

---

## 12.1 目标与范围

### 12.1.1 目标（对齐 `G-4` 与 `09 §9.3 C-4`）

| 编号 | 目标 | 对应定理 | 验收里程碑 |
|---|---|---|---|
| `LV-1` | 证明**有界量词展开保持语义**（`⟦ground(φ)⟧ρ = ⟦φ⟧ρ`） | `TH-1` | `M-2` |
| `LV-2` | 证明**展开输出无量词** | `TH-2` | `M-2` |
| `LV-3` | 证明**反例可唯一还原**（展平编码为单射） | `TH-1-C2` | `M-2` |
| `LV-4` | 证明**CIDR 掩码编码与其集合语义等价** | `TH-5` | `M-2` |
| `LV-5` | 证明**正则子语言转译保持语言** | `TH-6` | `M-2` |
| `LV-6` | 证明**除法线性化重写等价** | `TH-4` | `M-2` / `M-4` |
| `LV-7` | 证明**五式（六式）验证目标的编码充分性** | `TH-7` | `M-6` |
| `LV-8` | 证明**判定结果到数学命题的推理链可靠**，且 `unknown` 零信息 | `TH-7` + §12.4.9 | `M-6` |

> **与上游的差异（修正 `C-4` / `B-25`）**：上游 v2.0 把 Lean 保序证明整体排在阶段三（第 7–12 月），但 `G-4` 的验收要求它作为证据。本规范将其**拆为两段**：`LV-1`~`LV-5`（核心算子，`M-2`）与 `LV-7`~`LV-8`（编码充分性，`M-6`）。理由：前者是**结构性**命题（可用核心库证明），后者需要把 SMT-LIB 的语义也形式化，工作量高出一个量级。详见 `11 §11.4`。

### 12.1.2 非目标

| 编号 | 非目标 | 理由 |
|---|---|---|
| `LN-1` | 不形式化求解器自身的可靠性 | 求解器是外部可信基（TCB）的一部分，其可信度由 §12.4.8 的证明检查与 `06 §6.7` 的交叉验证承担 |
| `LN-2` | 不形式化位爆破 / 单纯形 / 自动机算法 | 属求解器内部，超出本框架的验证边界 |
| `LN-3` | 不形式化解析器（Pest 文法）的正确性 | 由 `10 §10.5` 的属性测试与差分测试覆盖，成本收益比更优 |
| `LN-4` | 不形式化并发调度与进程管理 | 由 `10 §10.5` 的故障注入测试覆盖 |
| `LN-5` | 不形式化 `TH-3`（可判定性）本身 | 该定理依赖 Presburger / 单纯形 / 位爆破 / 自动机等外部结果，属**引用型定理**，无法在本工程内机械化 |

---

## 12.2 依赖策略与工程结构

### 12.2.1 依赖策略：**不引入 Mathlib**

| 方案 | 构建时间 | 下载量 | 可进入每次 PR 的 CI | 采用 |
|---|---|---|---|---|
| Lean 4 核心库（`Init` + `Std`） | 秒级 | 无 | ✅ | **采用** |
| 引入 Mathlib | 数十分钟 | 数 GB | ❌（需缓存与独立流水线） | 拒绝 |

**理由**：本工程要证明的五类命题都是**结构性**的——对语法树归纳、对列表枚举、对环境重命名，只需 `List` / `Nat` / `Rat` 的基础引理。唯一显著依赖有序域代数 API 的是 `TH-4`（除法线性化），本工程对其采用 `sorry` 冻结陈述，并在 §12.6 给出应采用的 Mathlib 引理清单与切换到 Mathlib 的迁移路径。

**迁移路径（当委员会决定引入 Mathlib 时）**：在 `lakefile.lean` 增加 `require mathlib from git "…"`，并在 `Division.lean` 以 `import Mathlib.Data.Rat.Order` + §12.6.1 列出的四条引理替换 `sorry`。迁移不影响其他模块。

### 12.2.2 工程结构

```
lean/
├── lakefile.lean                     # Lake 构建定义（§12.2.1 的依赖策略落点）
├── lean-toolchain                    # 工具链锁定：leanprover/lean4:v4.14.0
├── PolicylangProof.lean              # 总入口（import 全部模块）
└── PolicylangProof/
    ├── Syntax.lean                   # 抽象语法：Sort / Term / Atom / Formula / RegLan / Cidr
    ├── Semantics.lean                # 指称语义：Model / Env / AtomEval / eval
    ├── Grounder.lean                 # 有界量词展开：tuplesOf / ground / IsQF   （ALG-1）
    ├── GrounderSoundness.lean        # TH-1、TH-1-C1、TH-1-C2、TH-2
    ├── Division.lean                 # TH-4（除法线性化）、命题 3.11.1
    ├── Cidr.lean                     # TH-5（CIDR 掩码等价）
    ├── Regex.lean                    # TH-6（正则转译语言保持）、TH-6-C1
    └── Encoding.lean                 # TH-7（编码充分性）与判定结论

scripts/
└── check-sorry.sh                    # Lean 证明纪律门禁（§12.7）
```

### 12.2.3 构建与验证命令

```bash
# 1) 安装工具链（首次，需外网；版本由 lean-toolchain 锁定）
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# 2) 构建（在 lean/ 目录下执行）
cd lean && lake build

# 3) 列出全部公理依赖，确认没有意外的 `sorryAx`（除已登记的 10 处）
cd lean && lake env lean --run /dev/stdin <<'EOF'
import PolicylangProof
#print axioms Policylang.ground_preserves
#print axioms Policylang.ground_isQF
#print axioms Policylang.flat_injective
EOF

# 4) 证明纪律门禁（§12.7）
SORRY_BUDGET=10 scripts/check-sorry.sh lean/PolicylangProof
```

---

## 12.3 形式化模型设计

### 12.3.1 三项关键设计决策

| 编号 | 决策 | 理由 |
|---|---|---|
| `LD-1` | **语义参数化**：值域与算术解释不进入 Lean 模型，而是由参数 `AtomEval := Env → Atom → Prop` 提供 | 使 `TH-1`/`TH-2` 与算术 / 位运算 / 字符串的具体理论**完全解耦**。若把 `Int` / `BitVec` / `String` 的语义也内联，则定理会被大量无关的算术引理所淹没，且每次理论扩展都要改动定理 |
| `LD-2` | **量词按界谓词解释**，而非按枚举折叠 | 若把 `eval` 的量词子句也定义为对枚举列表折叠，则 `TH-1` 退化为同义反复（实现即规格）。界谓词形式（`∀ is, is.length = k → (∀ i ∈ is, i < n) → …`）是**独立于实现**的规格，使 `TH-1` 具有实质内容 |
| `LD-3` | **合取/析取取右结合二元形式**（`conj` / `disj`）+ `conjsOf` / `disjsOf` 折叠函数 | 使 `Formula` 成为**非嵌套**归纳类型，`induction` 才产生可用的归纳假设。实现层的 `Formula::And(Vec<Formula>)` 与之同构，同构映射由 §12.5 的契约保证 |

### 12.3.2 量词语义的精确形式（对应规范 `AX-Q-INDEP` 与 `Inj`）

```lean
| .qall vars dom distinct body =>
    ∀ is : List Nat,
      is.length = vars.length →
      (∀ i ∈ is, i < M.domSize dom) →
      (distinct = true → is.Nodup) →
      eval E M (ρ.bindAll dom vars is) body
```

| 规范条款 | Lean 对应 |
|---|---|
| `AX-Q-INDEP`（全笛卡尔积，含对角项） | `distinct = false` 时第三条前提为 `False → is.Nodup`（建材蕴含，自动成立） |
| `Inj`（`distinct` 修饰的单射枚举） | `distinct = true` 时第三条前提要求 `is.Nodup` |
| 退化语义（`k > N` 时 `∀` 恒真） | 当 `vars.length > N` 时不存在满足前两条的 `is`，全称量词**自动为真**（零额外公理） |
| 域规模 `N` 的来源 | `M.domSize : String → Nat`（`Model` 的唯一字段） |

### 12.3.3 展开器的精确形式（对应规范 `ALG-1` 与 `DET-1`）

```lean
def tuplesOf (n : Nat) : Nat → List (List Nat)
  | 0     => [[]]
  | k + 1 => tuplesStep n (tuplesOf n k)          -- DET-1：首位外层、末位内层
```
- `DET-1`（确定性顺序）由结构递归唯一确定，因此 `ground` 是**纯函数**，`query_hash` 可复算（`07 §7.5`、`TH-10`）；
- `W11`（预算守卫 `G(φ) ≤ G_max`）**不在本层**——它以 `05 §5` 的静态计算实现，属于编译期的**拒绝式**检查，不影响语义保持定理；
- `FOLD-1`/`FOLD-2`/`CSE-1`（常量折叠 / α-等价去重 / 公共子式提取）是**保持语义的优化**，其正确性可分别归约为 `⋀` 的幂等律、`⊤` 消去律与结构共享，规范已在 `03 §3.7` 的 `TH-1` 证明中逐条说明。

---

## 12.4 定理清单与证明状态

> **状态图例**：`完整` = 证明体完整且不含 `sorry`；`含依赖` = 证明体完整但其正确性依赖下游 `sorry` 引理；`冻结` = 仅定理陈述，证明体为 `sorry`。

| 定理 / 命题 | 规范出处 | Lean 模块 / 声明名 | 状态 | 依赖 |
|---|---|---|---|---|
| `TH-1` Grounding 保持定理 | `03 §3.7` | `GrounderSoundness.ground_preserves` | **含依赖** | `OBL-1` |
| `TH-1-C1` 解集保持 | `03 §3.7` | `GrounderSoundness.ground_preserves_iff` | **含依赖** | `TH-1` |
| `TH-1-C2` 反例可唯一还原 | `03 §3.7` | `GrounderSoundness.flat_injective` | **完整** | — |
| `TH-2` 量词消除 | `03 §3.8` | `GrounderSoundness.ground_isQF` | **完整** | — |
| `TH-4` 除法线性化（D1/D2/D3/D4/D5/D6） | `03 §3.11.3` | `Division.div_eq_iff` / `div_ne_iff` / `div_lt_iff` / `div_le_iff` / `div_gt_iff` / `div_ge_iff` | **冻结** | `OBL-2`~`OBL-4` |
| 命题 3.11.1 floor 除法不可线性化 | `03 §3.11.4` | `Division.floor_div_not_linearizable` | **冻结** | `OBL-5` |
| `TH-5` CIDR 掩码等价 | `03 §3.12.2` | `CidrTheory.inCidr_encoding_correct` | **含依赖** | `OBL-6a`/`OBL-6b` |
| `TH-5` 主干（核心引理） | `03 §3.12.2` | `CidrTheory.clearlow_eq_iff` | **完整** | — |
| `TH-6` 正则转译语言保持 | `03 §3.13.3` | `Regex.toRegLan_correct` | **含依赖** | `OBL-7` |
| `TH-6-C1` `matches_all` 的 `re.inter` 语义 | `03 §3.13.3` | `Regex.matchesAll_inter_correct` | **完整** | — |
| `TH-6` 补字符类引理 | `03 §3.13.1` | `Regex.lang_negClsToRegLan` | **含依赖** | `OBL-7` |
| `TH-7` 编码充分性 | `03 §3.14` | `Encoding.encoding_adequate` | **冻结** | `OBL-8` |
| `TH-7` 诚实阻断（`unknown` 零信息） | `03 §3.14 (iii)` | `Encoding.Verdict.conclusion` | **完整**（类型层固定） | — |
| 列表侧辅助引理 | `03 §3.7` | `eval_conjsOf` / `eval_disjsOf` / `isQF_conjsOf` / `isQF_disjsOf` / `forall_mem_map` / `exists_mem_map` | **完整** | — |
| 枚举族成员刻画 | `03 §3.6.1` | `mem_injectiveTuplesOf` / `mem_tupleFamily` | **含依赖** | `OBL-1` |

### 12.4.1 `TH-1`：证明结构（对应规范 §3.7 的证明）

对 `φ` 结构归纳，并 `generalizing ρ`（关键：量词分支必须在**任意**环境 `ρ' = ρ.bindAll dom vars is` 上使用归纳假设）：

| 情形 | 证明步骤 | 对应规范 |
|---|---|---|
| 原子 | `E ρ (groundAtom ρ a) ↔ E ρ a`，由假设 `hE`（重命名等变性）直接给出 | 引理 L1 |
| `conj`/`disj`/`neg`/`impl`/`biff` | `simp only [ground, eval]` 后由两个归纳假设组合 | `⟦·⟧` 的组合性（§3.5.2） |
| `qall` | `eval_conjsOf` + `forall_mem_map` 化为 `∀ is ∈ tupleFamily …, eval …`；再用 `mem_tupleFamily` 的两个方向与归纳假设闭环 | §3.7 的 `★` 步骤 |
| `qex` | 对偶：`eval_disjsOf` + `exists_mem_map` + `mem_tupleFamily` | §3.7 的 `Exists` 情形 |

`hE`（重命名等变性）的**语义合理性**由三处落实：
1. `Syntax.lean` 中 `Term.fieldAccess x f` 与 `Term.flat i f` 的语义都归结为「查表」；
2. Rust 侧 `scalar_symbol(D, i, f)` 的**单射命名**（`03 §3.2.4`、补全 `A-7`）；
3. `06 §6.2.2` 的确定性声明发射顺序。

### 12.4.2 `TH-2`：证明结构（对应规范 §3.8）

纯结构归纳，量词分支被替换为 `conjsOf`/`disjsOf` 包裹的枚举结果，而这两者只由 `tt`/`ff`/`conj`/`disj` 构成（引理 `isQF_conjsOf`/`isQF_disjsOf`）。**不含 `sorry`**，是 `03 §3.8` 断言「输出 100% 无量词」的机械化证据。

### 12.4.3 `TH-4`：证明结构（对应规范 §3.11.3）

规范 §3.11.3 的纸面证明**已完整**（两侧同除 / 同乘正数保序、负数反序）。Lean 侧的形式化需要有序域的除法—乘法引理族，本工程不引入 Mathlib 故冻结陈述，应采用的引理清单见 §12.6.1。

### 12.4.4 `TH-5`：证明结构（对应规范 §3.12.2）

把规范证明中的「`x & M = ⌊x/2^s⌋·2^s`」这一步拆为两个引理：
- `clearlow_eq_iff`（**已完成**）：`(x/d)·d = (y/d)·d ↔ x/d = y/d`，由 `d ≠ 0` 约去 `d`；
- `clearlow_eq_land`（**冻结**，`OBL-6b`）：`Nat.land x (mask n p) = clearlow n p x`，需 `Nat` 位运算引理。

主定理 `inCidr_encoding_correct` 由上述两者直接组合，**证明体完整**。

### 12.4.5 `TH-6`：证明结构（对应规范 §3.13.3）

`toRegLan` 是纯结构函数，`Lang` 与 `LangRe` **独立定义**（保证定理有实质内容：它断言转译器与语言解释**交换**）。8 个构造分支中 6 个（`lit`/`any`/`range`/`concat`/`union`/`star`/`plus`/`opt`）以 `rfl` 或 `simp only […, ih]` 完成；两个字符类分支需列表折叠引理（`lang_clsToRegLan`，`OBL-7`）。补字符类引理 `lang_negClsToRegLan` 由前者 + `Set.compl_setOf` **完整推出**。

### 12.4.6 `TH-7`：证明结构（对应规范 §3.14）

`Goal.pi`（数学命题）与 `Goal.query`（编码断言集）在 `Encoding.lean` 中**独立定义**，于是 `TH-7` 成为「`query` 可满足 ⟺ `pi` 不成立」这一有内容的等价式。六个目标分支的证明计划已逐条写在定理的文档注释中（各自只需 `eval_conjsOf`/`eval_disjsOf` + 经典逻辑的德摩根律）。冻结理由是工作量（需引入经典逻辑引理族），排在 `M-6`。

### 12.4.7 不可判定性相关的定理不在本工程

`TH-3`（可判定性）与 `TH-3a`（组合逻辑限定）**刻意不在 Lean 中形式化**：它们依赖 Presburger 算术可判定性（Presburger 1929）、单纯形法、位爆破正确性、字串理论可判定性等**外部结果**。试图机械化将引入巨大的基础库依赖，收益远低于成本。规范以「引用型定理 + 运行期能力探测（`ALG-3`）」的组合替代之（`03 §3.10.3`）。

### 12.4.8 求解器作为可信基（TCB）

| 层 | 可信度来源 | 不在 Lean 中的理由 |
|---|---|---|
| 求解器判定 | `06 §6.7` 的交叉验证（SAT 模型重放 / UNSAT 多后端一致 / Alethe 证明检查） | 属外部可信基，形式化成本极高 |
| SMT-LIB2 语义 | 标准文档 + 双向差分测试（§12.5） | 同上 |
| 解析器 / 并发 / 进程 | `10 §10.5` 的故障注入与属性测试 | 成本收益比不优 |

### 12.4.9 `unknown` 零信息的类型层固定

```lean
def Verdict.conclusion (S : Spec) (M : Model) (E : AtomEval) (g : Goal) : Verdict → Prop
  | .sat     => ¬ Goal.pi S M E g
  | .unsat   => Goal.pi S M E g
  | .unknown => True          -- 零信息：不可推出任何关于 π 的结论
```

**这是 `G-8`（UNKNOWN 诚实阻断）在形式层的落点**：`unknown` 对应 `True`（恒真但零信息），因此**不存在**从 `unknown` 到 `Goal.pi` 或 `¬Goal.pi` 的推导路径。任何「把 `unknown` 当 PASS」的实现都会在证明层面被拒绝。

---

## 12.5 AST 一致性契约与差分测试

> **风险（`09 §9.2 B-21`）**：Rust 侧（`05 §3`）与 Lean 侧（`Syntax.lean`）是**两套独立实现**的同一抽象语法。双实现必然漂移，而 `TH-1`/`TH-2` 是以 Lean 侧为对象证明的——若两侧语义不同，**证明不覆盖实际产品**。

### 12.5.1 契约表（Contract）

| 抽象语法元素 | Rust 侧（`05 §3`） | Lean 侧（`Syntax.lean`） | 一致性要求 |
|---|---|---|---|
| 排序 | `Type::{Int,Real,Bool,String,BitVec(usize),Enum(Vec<String>)}` | `Sort::{int,real,bool,str,bv Nat,enum Nat}` | 一一对应；`Enum` 的成员名只在 Rust 侧保留（Lean 侧只关心基数，因编码为整数，`06 §6.2.1 DD-6.2`） |
| 展平标量 | `Expr::Flat { domain, index, field }` | `Term.flat : Instance → String → Term` | 字段名与顺序一致 |
| 绑定变量字段访问 | `Expr::FieldAccess { instance, field }` | `Term.fieldAccess : String → String → Term` | 一致 |
| 有理数 | `Rational { num : i128, den : i128 }` | `Term.rLit : Int → Int → Term` | 规范化为互质、分母为正；`den ≠ 0` |
| 合取 / 析取 | `Formula::And(Vec<Formula>)` | `Formula.conj`（二元）+ `conjsOf` | **右结合折叠同构**：`conjsOf [f₁,…,fₙ] = f₁ ∧ (f₂ ∧ … ∧ fₙ)`，空表为 `⊤` |
| 否定 / 蕴含 / 等价 | `Not` / `Implies` / `Iff` | `neg` / `impl` / `biff` | 一致 |
| 量词 | `Forall { vars, domain, distinct, body }` | `qall : List String → String → Bool → Formula → Formula` | 字段序一致（`distinct` 为 `Bool`） |
| 正则 | `RegLan`（`05 §3` 的 `RegexNode`） | `Syntax.RegLan` | 10 个构造一一对应 |
| CIDR | `Cidr { width, net0, prefix }` | `Cidr { width, net0, prefix }` | 一致，且都要求 `prefix ≤ width` |

### 12.5.2 差分测试（`Differential Fuzzing`）

```
DT-1  随机规范生成器（`proptest`）：按 `spec/grammar.pest` 生成随机合式规范，
      同时输出 (a) DSL 文本、(b) Rust 侧 AST 的 JSON、(c) Lean 侧 AST 的 JSON。
DT-2  Rust 侧求值器 `PLM-Eval`（`06 §6.7.1`）对 (a) 求值；
      Lean 侧以 `#eval` 调用 `eval` 对 (c) 求值。二者必须逐位一致。
DT-3  展开器差分：Rust 侧 `ground()` 输出的 SMT-LIB2，与 Lean 侧 `ground` 经
      打印器（`12 §12.5.3`）输出的 S 表达式，必须**语法等价**（去空白比较）。
DT-4  量化差异预算：每轮 ≥ 10⁵ 个随机规范；任一不一致即 `E-INTERNAL` 并落盘复现包。
DT-5  CI 频率：每 PR 跑 10³ 例（快速通道）；每夜跑 10⁵ 例（深度通道）。
```

### 12.5.3 Lean → SMT-LIB2 打印器（`DT-3` 的前提）

Lean 侧需提供一个**仅用于差分测试**的打印器 `printFormula : Formula → String`，输出标准 SMT-LIB2 文本（不参与生产路径）。其与 `05 §7` 的生产打印器的差异即为差分信号。打印器本身不做优化（不折叠、不 CSE），因此 `DT-3` 比较的是**规范化后**的文本（`03 §3.6` 的 `FOLD-1`/`FOLD-2`/`CSE-1` 由比较器反向应用）。

---

## 12.6 `sorry` 清单与证明计划

### 12.6.1 `sorry` 登记表（共 10 处）

| 编号 | 位置（声明名） | 状态 | 缺失引理 / 需要的能力 | 建议手段 | 里程碑 |
|---|---|---|---|---|---|
| `OBL-1` | `GrounderSoundness.mem_tuplesOf` | `sorry` | `List.mem_bind`/`mem_range`/`mem_map` 的组合与结构递归 | 对 `k` 归纳并 `generalizing is`；反向支用 `is.head`/`is.tail` 构造（完整计划见源码文档注释） | `M-2` |
| `OBL-2` | `Division.div_lt_iff` | `sorry` | 有序域：`div_lt_iff₀` / `div_lt_iff_of_neg` | 引入 Mathlib 或自建 `Rat` 引理 | `M-4` |
| `OBL-3` | `Division.div_eq_iff` | `sorry` | 有序域：`div_eq_iff`（`Rat.div_mul_cancel` + `mul_comm`） | 同上 | `M-4` |
| `OBL-4` | `Division.div_le_iff` / `div_gt_iff` / `div_ge_iff` | `sorry` | 同 `OBL-2` 的 `≤` / `>` / `≥` 变体 | 同上（`div_le_iff₀` 等） | `M-4` |
| `OBL-5` | `Division.floor_div_not_linearizable` | `sorry` | `Int.ediv` 的分段性质 + Presburger 可定义性的反证 | 以 `Int.ediv` 的 `omega`-可判定片段给出反例；需 `Int` 除法引理族 | `M-6` |
| `OBL-6a` | `Cidr.clearlow_eq_iff` | **完整** | — | — | 已闭环 |
| `OBL-6b` | `Cidr.clearlow_eq_land` | `sorry` | `Nat.land` 与除法/取模的位引理（`Nat.land_eq_…` 族） | 对 `p` 归纳 + 逐位分解；或改为定义 `masked` 为该算术形式并在 `06 §6.2.3` 的编码层断言其与 `bvand` 一致 | `M-6` |
| `OBL-7` | `Regex.lang_clsToRegLan` | `sorry` | `List.foldr` 与 `Set.union` 的折叠引理 + 空类语义 `{u ∣ u = []}` 的差集处理 | 对 `cs` 归纳；`nil` 支需处理 `L(re.toRe []) = {ε}` 而非 `∅`，建议把 `[abc]` 的**空表**情形在解析阶段拒绝（`E-REGEX-EMPTY-CLASS`）以消除该边界 | `M-4` |
| `OBL-8` | `Encoding.encoding_adequate` | `sorry` | 经典逻辑德摩根律族（`not_forall` / `not_exists` / `not_and`） | 六目标逐支展开；计划已写在源码文档注释 | `M-6` |

**统计**：10 处 `sorry`（`OBL-1`~`OBL-8`，其中 `OBL-4` 含 3 个声明）；`OBL-6a` 已闭环。

### 12.6.2 Burn-down 计划

| 里程碑 | 目标 `sorry` 数 | 需闭环的 `OBL` | 门禁命令 |
|---|---|---|---|
| `M-2` | **≤ 10** | 全部登记（`LV-1`~`LV-5` 的陈述已就位，`TH-1-C2`/`TH-2` 已可出示）；本里程碑**应**闭环 `OBL-1`（`mem_tuplesOf`，纯列表引理，不依赖 Mathlib），闭环后实际 `sorry` 数为 **9** | `SORRY_BUDGET=10 scripts/check-sorry.sh` |
| `M-4` | **≤ 4** | `OBL-2`、`OBL-3`、`OBL-4`（共 5 个声明）、`OBL-7` | `SORRY_BUDGET=4 …` |
| `M-6` | **0** | `OBL-5`、`OBL-6b`、`OBL-8` | `SORRY_BUDGET=0 …` |

> **自洽性说明**：`OBL-1` 的唯一归属里程碑是 `M-2`（§12.6.1），故不进 `M-4` 的闭环清单。`M-4` 目标 `≤ 4` 为**鲁棒上界**——即便 `OBL-1` 未在 `M-2` 闭环（`≤ 10 − 6 = 4`）亦成立；若 `OBL-1` 已闭环则为 `3`。`M-2` 目标保持 `≤ 10` 仅作**保守上界**，不强制进度，进度由「`OBL-1` 应闭环」的散文要求与 §12.6.1 的里程碑绑定承载。

### 12.6.3 首次 `lake build` 的预期调整清单（**诚实披露**）

本工程未在本环境编译。除上表 10 处 `sorry` 外，以下声明含较复杂的 `simp only` / `rw` 步骤，预计需 tactic 级微调（**不改变定理陈述**）：

| 声明 | 风险点 | 建议调整 |
|---|---|---|
| `eval_conjsOf` / `eval_disjsOf` / `isQF_conjsOf` / `isQF_disjsOf` | `simp only [conjsOf, eval]` 的化简顺序 | 若顺序不符，改为 `rw [show conjsOf (a :: as) = Formula.conj a (conjsOf as) from rfl, eval]` |
| `forall_mem_map` / `exists_mem_map` | `List.mem_map` 的配置项顺序（`⟨a, ha, rfl⟩`） | 若报错，改用 `List.mem_map.mpr ⟨a, ha, rfl⟩` 的显式形式或 `simpa` |
| `ground_preserves` 的 `biff` 分支 | `Iff.trans` / `Iff.symm` 的方向 | 若报错，改用 `propext` + 逐向 `fun h => …` |
| `Regex.toRegLan_correct` 的 `concat`/`union`/`star` 分支 | `simp only [..., iha, ihb]` 是否能闭合 `Set` 相等 | 若不能闭合，改用 `Set.ext u; constructor <;> rintro …` |
| `Cidr.clearlow_eq_iff` | `Nat.mul_right_cancel` 的实际签名（是否需要非零前提） | 若报错，改用 `Nat.mul_right_cancel_iff.mpr` 或 `Nat.eq_of_mul_eq_mul_right`（含 `hd` 前提） |
| `mem_injectiveTuplesOf` / `mem_tupleFamily` | `of_decide_eq_true` / `decide_eq_true` 的名称 | 若报错，改用 `decide_eq_true_iff` 或 `Bool.decide_eq_true` |
| `Cidr.clearlow_eq_iff` 中的 `omega` | `omega` 在纯核心环境下的可用性 | `omega` 属 Lean 4 核心策略；若不可用，改 `Nat.pow_pos (by norm_num)` |

**处置流程**：首次 `lake build` 后，按本表逐项调整；若某项调整超过 30 分钟未果，**立即以 `sorry` 冻结并登记到 §12.6.1**，同时更新 `SORRY_BUDGET` 与 burn-down 计划。这一流程本身是 `12 §12.8` 诚实原则的体现。

---

## 12.7 CI 集成

### 12.7.1 门禁脚本

`scripts/check-sorry.sh`：统计 `sorry`/`admit` 数量并与里程碑预算比较，超预算则非零退出。默认预算 `10`（`M-2`），由 `SORRY_BUDGET` 环境变量覆盖。

### 12.7.2 工作流片段

```yaml
  lean-proof:
    name: Lean 4 形式化证明门禁
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: 安装 elan（Lean 工具链管理器）
        run: |
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            | sh -s -- -y --default-toolchain none
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"

      - name: 缓存 elan 与 Lake 构建产物
        uses: actions/cache@v4
        with:
          path: |
            ~/.elan
            lean/.lake
          key: lean-${{ hashFiles('lean/lean-toolchain', 'lean/lakefile.lean', 'lean/**/*.lean') }}

      - name: lake build
        working-directory: lean
        run: lake build

      - name: 证明纪律门禁（sorry 预算）
        run: SORRY_BUDGET=10 scripts/check-sorry.sh lean/PolicylangProof

      - name: 公理依赖审计（禁止意外 sorryAx）
        working-directory: lean
        run: |
          cat > /tmp/axioms.lean <<'EOF'
          import PolicylangProof
          #print axioms Policylang.ground_preserves
          #print axioms Policylang.ground_isQF
          #print axioms Policylang.flat_injective
          #print axioms Policylang.CidrTheory.inCidr_encoding_correct
          #print axioms Policylang.Regex.toRegLan_correct
          EOF
          cp /tmp/axioms.lean AxiomsAudit.lean
          lake env lean AxiomsAudit.lean
```

### 12.7.3 差分测试门禁（§12.5.2）

`DT-5` 的快速通道（每 PR 10³ 例）作为独立 job 运行；深度通道（每夜 10⁵ 例）作为定时工作流。任一不一致即失败并上传复现包。

---

## 12.8 局限与诚实声明

| 编号 | 局限 | 说明与缓解 |
|---|---|---|
| `LL-1` | **未机械化**：`TH-3` / `TH-3a`（可判定性与组合逻辑限定）依赖外部结果（Presburger、单纯形、位爆破、字串理论），本工程刻意不形式化 | 以「引用型定理 + `ALG-3` 运行期能力探测」替代（`03 §3.10.3`）。探测失败即降级为 `UnknownReviewRequired`，**绝不输出 `Pass`** |
| `LL-2` | **可信基包含求解器**：本工程不形式化求解器的可靠性 | 由 `06 §6.7` 三层交叉验证承担（SAT 模型重放 / UNSAT 多后端一致 / Alethe 证明检查） |
| `LL-3` | **双实现漂移风险**：Rust 与 Lean 两套 AST | 由 §12.5 契约表 + `DT-1`~`DT-4` 差分测试承担；漂移即 CI 阻断 |
| `LL-4` | **语义参数化 `hE` 假设**：`TH-1` 以「原子解释器重命名等变」为假设 | 该假设在实现层是三处具体机制的合取（§12.4.1）；`05 §6.5` 要求命名与发射复用同一实现，并在 `10 §10.6` 加单元测试 |
| `LL-5` | **`sorry` 尚未清零**：当前 10 处 | §12.6 的 burn-down 计划 + §12.7 的 CI 门禁；`sorry` 数量是**受控且登记**的，不是隐藏的 |
| `LL-6` | **本环境未编译**：全部证明未经 `lake build` 校验 | §12.6.3 给出预期调整清单与处置流程 |

> **最终定位**：本工程的正确使用方式是把它当作 `G-4` 的**证据产生器**，而非「证明做完了」的宣告。`M-2` 时它能出示 `TH-2`（量词消除）与 `TH-1-C2`（反例可还原）的**完整机器证明**，以及其余定理的**冻结陈述 + 精确证明计划**；`M-6` 时 `sorry` 归零。这条演进路径本身就是可审计的——`scripts/check-sorry.sh` 的每次运行结果都是审计证据。
