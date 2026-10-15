# PolicyLang Meta — 工程立项与核心研发蓝本文档集（v2.1）

> **定位**：领域无关的策略语言定义、可判定性编译与形式化验证元框架。
> 用户通过自定义实体本体、有界变量与声明式约束描述领域规范；框架在编译期执行可判定性守卫与有界量词展开，编译为**无量词 SMT-LIB2** 查询，通过**理论感知的多求解器并行竞速**完成数学证明，并以业务可读语言输出**违规反例**或**最小化冲突规则集**。
>
> 它不是又一种单一领域的策略语言，而是**生产高可信策略语言的标准化产线**。

---

## 0. 本次交付做了什么

| 事项 | 结果 |
|---|---|
| 上游 v2.0 的 `TXT` / `TXT +N` 跨文档引用占位符与破损表格 | **全量处理**（合并单元格、还原数学记号），处理规则见 `docs/00 §0.5`；无内容丢失，归属核对见 `docs/09 §9.7` |
| 数学与工程细节补全 | 上游存在 **89 项**缺口/冲突/遗漏（`A` 数学 18 · `B` 工程 33 · `C` 冲突 15 · `O` 治理 23），其中 **15 项 P0**；已**全部闭环**或登记为开放问题 |
| 需求 ↔ 设计对应关系 | 建立 `G ↔ FR ↔ NFR ↔ AC ↔ CR ↔ IF ↔ Test` **双向追溯矩阵**（`docs/08`），并附 17 条评审自检清单 |
| 形式化证据 | 新增 `lean/PolicylangProof/` Lean 4 工程（8 模块），冻结 `TH-1`/`TH-2`/`TH-1-C2`/`TH-4`/`TH-5`/`TH-6`/`TH-7` 的机器可检查陈述，`sorry` 受控为 10 处并附 burn-down 计划（`docs/12`） |
| 机器可读规格 | `spec/grammar.pest`（修正后完整文法）、`spec/report.schema.json`（审计报告 JSON Schema） |
| 验收案例 | `examples/{cloud-deployment,exchange-compliance,marketing-coupon}.plm` 三个可解析的领域案例 |
| 结论 | **15 项 P0 缺口必须在 `M-1` 前闭环**（本文档集已给出裁决与补全）；**10 项开放问题 `OQ-1`~`OQ-10` 需立项委员会裁决**，其中 `OQ-5`、`OQ-9` 建议在立项评审当日决议 |

---

## 1. 文档集导航

| 编号 | 文件 | 角色 | 主要读者 |
|---|---|---|---|
| 00 | [`docs/00-术语表与编号规范.md`](docs/00-术语表与编号规范.md) | **唯一术语 / ID / 退出码事实源** | 全部 |
| 01 | [`docs/01-需求规格说明书-PRD.md`](docs/01-需求规格说明书-PRD.md) | 需求（目标 / FR-1~FR-20 / NFR / AC-1~AC-12） | 产品、评审、客户 |
| 02 | [`docs/02-系统设计说明书-SDD.md`](docs/02-系统设计说明书-SDD.md) | 架构、8 个 Crate、接口契约 IF-1~IF-6、设计决策 DD-1~DD-12 | 架构师、研发 |
| 03 | [`docs/03-形式化语义与可判定性规范.md`](docs/03-形式化语义与可判定性规范.md) | **数学内核**：语义、类型系统、可判定性、定理 TH-1~TH-7 | 形式化工程师 |
| 04 | [`docs/04-DSL语言参考手册.md`](docs/04-DSL语言参考手册.md) | 文法、原语、SMT 映射、错误码总表 | DSL 使用者、编译器研发 |
| 05 | [`docs/05-编译管线工程规范.md`](docs/05-编译管线工程规范.md) | P1~P7 编译管线与完整 Rust 实现 | 编译器研发 |
| 06 | [`docs/06-SMT编码与求解编排规范.md`](docs/06-SMT编码与求解编排规范.md) | 六式编码、逻辑档位、竞速编排、交叉验证 | 求解器/后端研发 |
| 07 | [`docs/07-诊断审计与治理规范.md`](docs/07-诊断审计与治理规范.md) | 反例还原、Core 归因、审计哈希、CI 门禁、Waiver、评审状态机 | 平台、DevOps、审计 |
| 08 | [`docs/08-需求设计追溯矩阵.md`](docs/08-需求设计追溯矩阵.md) | **双向追溯矩阵 + 一致性自检清单** | 评审、QA |
| 09 | [`docs/09-一致性与缺口分析报告.md`](docs/09-一致性与缺口分析报告.md) | **89 项缺口/冲突/遗漏清单与裁决** + 10 项开放问题 | 评审委员会 |
| 10 | [`docs/10-验收标准与测试计划.md`](docs/10-验收标准与测试计划.md) | AC-1~AC-12 测试设计、BENCH-1~6、故障注入 | QA |
| 11 | [`docs/11-实施路线图与风险管理.md`](docs/11-实施路线图与风险管理.md) | 三阶段、M-1~M-6、RISK-1~RISK-20 | PM、管理层 |
| 12 | [`docs/12-Lean4形式化验证规范.md`](docs/12-Lean4形式化验证规范.md) | Lean 定理清单、`sorry` 清单与 burn-down、AST 一致性契约 | 形式化工程师 |
| 13 | [`docs/13-项目交接说明.md`](docs/13-项目交接说明.md) | **交接唯一入口**：当前状态、决策脉络、待验证事项、接续动作序列 | 接手者（人 / AI） |

**机器可读制品**

| 文件 | 说明 |
|---|---|
| [`spec/grammar.pest`](spec/grammar.pest) | 修正后的完整 Pest 文法（修复上游 4 处缺陷、补齐 7 处产生式） |
| [`spec/report.schema.json`](spec/report.schema.json) | 审计报告 JSON Schema（`overall_status` 五值枚举、有序数组保证确定性） |
| [`lean/`](lean/) | Lean 4 保序证明工程（`lake build`） |
| [`examples/`](examples/) | 三大领域验收案例（`.plm`） |
| [`scripts/check-sorry.sh`](scripts/check-sorry.sh) | Lean 证明纪律门禁 |

**推荐阅读路径**

| 目的 | 路径 |
|---|---|
| **接手本项目（人 / AI）** | **`docs/13`（交接唯一入口）** → `README` → `01 §2` → `09 §9.0` |
| **构建 / 运行代码** | **`IMPLEMENTATION.md`**（Rust 参考实现：模块划分、关键算法、用法、验证结果）→ `02` → `05` |
| 立项决策 / 管理层 | 本 README → `01 §2`（目标）→ `09 §9.6`（影响评估）→ `11` |
| 架构评审 | `01` → `02` → `03`（定理部分）→ `08` |
| 编译器研发 | `04` → `03` → `05` → `spec/grammar.pest` |
| 求解器 / 后端研发 | `03` → `06` → `07` |
| 形式化 / 学术 | `03` → `12` → `lean/` |
| QA / DevOps | `10` → `07` → `08` |

---

## 2. 上游 v2.0 的核心修正（速览）

> 完整清单（89 项，含严重级、证据位置、裁决）见 `docs/09`。以下是影响面最大的 8 项。

| 编号 | 上游问题 | 本次修正 |
|---|---|---|
| `C-5` | `FR-5`/`G-4` 声称「100% 拦截非线性」，但守卫实现 `!left.is_constant() && !right.is_constant()` **漏掉 `2 / x`**（左侧常量、右侧变量）这一真正非线性构造 | 拆为两个独立侧条件：`LinMul(a,b) ≜ isConst(a) ∨ isConst(b)`；**除法独立要求常/可线性化除数**（`03 §3.4.1`）。`AC-4` 扩展为 6 个边界用例 |
| `A-12` | 未识别 `/`、`div`、`mod` 在 SMT-LIB 中是**全函数**、除数为 0 时**取值未指定** ⇒ 含除法比较的 PASS 可能是**假证明**；且缺「除法线性化」技术 | 新增 `FR-16`：`safety` 义务（`ALG-2`）+ **除法线性化定理 `TH-4`**（交叉相乘，含不等号反转），使义务查询**不含除法**从而不降级逻辑档位（`03 §3.11`） |
| `A-3` | 有界量词展开的组合爆炸 `N^k` **完全未度量、未守卫**；示例 `size:4` 掩盖了问题 | 新增规模度量 `G(φ) = A(φ)·∏ N^{k'}`、静态计算算法与 `G_max = 10⁶` 预算（`W11` / `E-GROUNDING-BUDGET`），附量级测算表（`03 §3.9`） |
| `A-13` | 三处声称输出「**最小**冲突核」，但 `(get-unsat-core)` **不保证最小** | 新增 `ALG-4` 两阶段最小化（assumption-based 提取 + deletion-based 精化）+ `core_minimal` **诚实标注**（`06 §6.9`） |
| `B-7` | `LogicProfile` **没有任何 `uses_*` 置位语句** ⇒ 理论路由恒为 `ALL`，`FR-8` 核心功能形同不存在 | 补按**排序驱动**的置位规则 + 12 行完整档位真值表；逻辑名降级为**候选名**，以 `ALG-3` 运行期**能力探测**替代硬编码（`03 §3.10.3`、`06 §6.4`） |
| `C-1` | `FR-9`（单文件多目标 `push/pop`）与 `FR-8`（首胜 SIGKILL）**不可能同时成立** | 决策 `DD-6.1`：默认**一目标一查询文件**；增量能力仅保留在「单求解器批量排查」与「核心最小化」两处（`06 §6.1.3`） |
| `C-9` | `AC-5`「Z3 在 **10 ms** 内被 SIGKILL」不可测：`abort_all()` **不等待回收**，NFR-3「残留率为 0」亦不成立 | 改用 `JoinSet::shutdown().await`（排空 `join_next` 保证 `drop` 触发强杀）；指标修正为 **P99 ≤ 50 ms** 并给出进程表采样判定法（`06 §6.6.1`、`10 §10.2`） |
| `A-10` | **完全没有正则转译器**：只给了「编译为 `re.inter`」的目标，未定义允许子集与映射 | 定义子语言 `R_sub` + `τ` 映射表 + **10 类拒绝清单**（含上游遗漏的**反向引用**）+ `TH-6` 语言保持定理（`03 §3.13`） |

---

## 3. 快速开始

**环境要求**：Rust 1.75+（`cargo`）；SMT 求解器用 `bash scripts/install-solvers.sh`
一键安装到用户目录（**无需修改 `PATH`**，也无需管理员权限）；可选 Lean 4 工具链（仅做形式化证明时需要）。
提供 `Cargo.lock`，**可完全离线构建**。

```bash
# 0) 构建（离线亦可；首次约 1 分钟）
cargo build            # 加 --offline 可在无网络环境构建
cargo test             # 161 个自动化测试

# 1) 静态检查（不求解）—— 验证 DSL 与可判定性守卫
./target/debug/policylang check examples/cloud-deployment.plm

# 2) 形式化验证（需已安装求解器；未安装时诚实报 E-SOLVER-MISSING ⇒ 退出码 4）
./target/debug/policylang verify examples/cloud-deployment.plm --timeout 3000ms --output report.json

#   退出码：0=PASS  1=FAIL(反例/冲突)  2=UNKNOWN(转人工)  3=编译阻断  4=内部错误

# 3) 导出可审计中间产物（SMT-LIB2 脚本、能力矩阵、SARIF）
./target/debug/policylang verify examples/cloud-deployment.plm \
    --emit-smt out/smt --emit-capability out/capability.json --sarif out/report.sarif

# 4) 查看本机求解器能力矩阵（ALG-3 探测结果）
./target/debug/policylang solvers

# 5) Lean 形式化证明
cd lean && lake build
SORRY_BUDGET=10 ../scripts/check-sorry.sh PolicylangProof
```

> 完整的模块划分、关键算法说明、逐 crate 文件表与验证结论见 **[`IMPLEMENTATION.md`](IMPLEMENTATION.md)**。

---

## 4. 术语与编号纪律

- 全部 ID（`G-` / `FR-` / `NFR-` / `AC-` / `CR-` / `IF-` / `DD-` / `TH-` / `ALG-` / `E-` / `W-` / `RISK-` / `OQ-`）以 `docs/00 §0.2` 为**唯一事实源**；ID 一经分配**永不回收、永不重排**。
- 状态值恰为 5 个：`Pass` / `Fail` / `UnknownReviewRequired` / `Waived` / `Error`；合并格 `Error ⊐ Fail ⊙ UnknownReviewRequired ⊐ Waived ⊐ Pass`（`docs/00 §0.4`）。
- CLI 退出码恰为 5 个：`0` / `1` / `2` / `3` / `4`（`docs/00 §0.4.3`）。
- DSL 源文件扩展名为 **`.plm`**（PolicyLang Meta），**不沿用**上游的 `.pl`（与 Perl 冲突）。
- 错误码别名（`E-CROSSVAL-MISMATCH`、`E-REPORT-IO`）已废弃，规范名为 `E-XVALIDATE-MISMATCH`、`E-REPORT-WRITE`（`docs/00 §0.2.4`）。

---

## 5. 当前状态与后续动作

| 项 | 状态 |
|---|---|
| 文档集（01–13 + spec + examples + lean） | **冻结（v2.1）**，可直接作为立项与核心研发蓝本；**交接入口 = `docs/13`** |
| 跨文档不一致 `INC-1`~`INC-13` | **已全部修复**（登记与证据见 `docs/08 §8.8.3`；变更记录见 `docs/01 §8` 的 `CHG-12`~`CHG-16`） |
| 15 项 P0 缺口 | 已全部给出裁决与补全去向；**闭环判据**见 `docs/08 §8.5`（可勾选） |
| 10 项开放问题 `OQ-1`~`OQ-10` | **待立项委员会裁决**（`docs/09 §9.5`）；建议 `OQ-5`（是否保留 `--allow-nonlinear`）与 `OQ-9`（Lean 证明是否作为 `G-4` 硬门禁）当日决议 |
| Lean 工程 | 陈述已冻结，`sorry` 受控为 10 处；**首次 `lake build` 为下一步动作**，预期调整清单见 `docs/12 §12.6.3` |
| 求解器基线锁定 | 需在 `M-1` 结束前完成 `ALG-3` 实测并写入 `policylang.lock`（`OQ-6`） |

---

## 6. Rust 参考实现

`docs/01`–`docs/13` 所定义的系统已有一套**可编译、可运行、可测试**的 Rust 参考实现。

| 项 | 值 |
|---|---|
| 规模 | **8 个 crate / 48 个 Rust 文件 / 18,898 行**（`policylang-{ast,parser,check,codegen,solver,diagnostics,governance,cli}`） |
| 测试 | **213 个自动化测试全部通过**（186 单元 + 27 端到端），**0 编译告警** |
| 外部依赖 | `pest` / `pest_derive` / `serde` / `serde_json` / `sha2` / `hex` / `thiserror`——均为标准生态库；**未引入** tokio / clap / regex / rfc8785（等价替换的理由见 `IMPLEMENTATION.md §6.1`） |
| 求解器 | **已接入真实 z3 5.3.0 / cvc5 1.4.2 / bitwuzla 0.9.1**（`bash scripts/install-solvers.sh`）；能力矩阵由 `--solvers` 实测 |
| 可执行文件 | `policylang`（9 个子命令，含 `lock`）、`pl-stub-solver`（端到端测试桩，**非真求解器**） |
| 详细说明 | **[`IMPLEMENTATION.md`](IMPLEMENTATION.md)** |

实现过程中反向修正了规范与冻结文法中的 6 处缺陷（`INC-14`–`INC-19`，其中 `INC-18` 为**阻断性**缺陷：
文法的词边界断言在 Pest 下因隐式空白跳过而失效，导致所有关键字起始声明解析失败）。
**这些问题只在文法被真正编译时才会暴露**——完整登记见 `docs/08 §8.8.3`。

---

## 7. 许可证

本项目采用 **[MIT License](LICENSE)**。

依赖与工具的许可证合规清单（Z3 / CVC5 / Bitwuzla / Lean 4 / Pest 等）见 `docs/11 §11.9`。
其中所有 SMT 求解器均以**进程外调用**方式使用，不做静态链接。
