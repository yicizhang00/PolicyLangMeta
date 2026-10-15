/-
  PolicyLang Meta — 有界量词展开器（Bounded Quantifier Grounder）
  对应规范：docs/03-形式化语义与可判定性规范.md §3.6（算法 ALG-1）、§3.8、§3.9

  实现要点（与规范逐条对应）：
  * `DET-1` 确定性枚举顺序：`tuplesOf` 以「首位外层、末位内层」的字典序生成；
  * `ALG-1-P` 死变量剪枝：由 `TupleFamily` 的基数参数 `k = vars.length` 控制
    （规范要求 k 取**实际出现**的变量数；此处的形式上界证明用全体变量数，
    剪枝是保持语义的优化，见规范 §3.6.1 的 `ALG-1-P` 条款）；
  * `FOLD-1`/`FOLD-2`/`CSE-1` 属于发射阶段的优化，不影响语义保持定理；
  * `W11` 预算守卫在 `05 §5` 以 `G(φ)` 静态计算实现（不在此层）。
-/

import PolicylangProof.Semantics

namespace Policylang

/-- 单步笛卡尔积扩展：给定已有的尾元组集合 `base`，对每个首位 `i < n`
    生成 `i :: is`（规范 §3.6.1 的 `cartesian_indices` 的递归步骤） -/
def tuplesStep (n : Nat) (base : List (List Nat)) : List (List Nat) :=
  (List.range n).bind (fun i => base.map (fun is => i :: is))

/-- 索引元组枚举（规范 §3.6.1）：长度 `k`、元素 `< n` 的全部列表。
    结构递归仅发生在 `k` 上，且递归调用是 `tuplesStep` 的直接实参，
    以满足结构递归的终止性检查。 -/
def tuplesOf (n : Nat) : Nat → List (List Nat)
  | 0     => [[]]
  | k + 1 => tuplesStep n (tuplesOf n k)

/-- 单射枚举（规范 §3.5.2 的 `Inj`）：额外要求无重复。
    `filter` 需要 `Bool` 谓词，故显式使用 `decide`。 -/
def injectiveTuplesOf (n k : Nat) : List (List Nat) :=
  (tuplesOf n k).filter (fun is => decide (is.Nodup))

/-- 索引列表族：按 `distinct` 修饰在「全笛卡尔积」与「单射枚举」之间切换
    （规范 §3.6.1 的 `Tuples`） -/
def tupleFamily (n k : Nat) (distinct : Bool) : List (List Nat) :=
  if distinct then injectiveTuplesOf n k else tuplesOf n k

/-- 右结合 n 元合取（与实现层 `Formula::And(Vec<_>)` 同构，见 `12 §12.5`） -/
def conjsOf : List Formula → Formula
  | []      => .tt
  | f :: fs => .conj f (conjsOf fs)

/-- 右结合 n 元析取（与实现层 `Formula::Or(Vec<_>)` 同构） -/
def disjsOf : List Formula → Formula
  | []      => .ff
  | f :: fs => .disj f (disjsOf fs)

/-- 项重命名（规范 §3.6.2 的 `ground_expr`）。
    关键条款：`fieldAccess x f ↦ flat (ρ x) f`，即用环境中绑定的实例替换
    绑定变量；这正是 §3.6.2「重命名一致性」引理 L1 的语法侧。 -/
def groundTerm (ρ : Env) : Term → Term
  | .gvar v          => .gvar v
  | .fieldAccess x f => .flat (ρ x) f
  | .flat i f        => .flat i f
  | .iLit n          => .iLit n
  | .rLit n d        => .rLit n d
  | .bLit b          => .bLit b
  | .sLit w          => .sLit w
  | .bvLit w v       => .bvLit w v
  | .binop op a b    => .binop op (groundTerm ρ a) (groundTerm ρ b)
  | .strLen t        => .strLen (groundTerm ρ t)

/-- 原子重命名 -/
def groundAtom (ρ : Env) : Atom → Atom
  | .cmp a op b      => .cmp (groundTerm ρ a) op (groundTerm ρ b)
  | .inRange x a b   => .inRange (groundTerm ρ x) (groundTerm ρ a) (groundTerm ρ b)
  | .unique d f      => .unique d f
  | .matchesAll t rs => .matchesAll (groundTerm ρ t) rs
  | .inCidr t c      => .inCidr (groundTerm ρ t) c
  | .boolAtom t      => .boolAtom (groundTerm ρ t)

/-- 有界量词展开（规范 §3.6.1 的算法 `ALG-1`）。
    输出**不含 `qall`/`qex` 节点**——这是定理 `TH-2` 的内容。 -/
def ground (M : Model) (ρ : Env) : Formula → Formula
  | .tt               => .tt
  | .ff               => .ff
  | .atom a           => .atom (groundAtom ρ a)
  | .conj a b         => .conj (ground M ρ a) (ground M ρ b)
  | .disj a b         => .disj (ground M ρ a) (ground M ρ b)
  | .neg f            => .neg (ground M ρ f)
  | .impl a b         => .impl (ground M ρ a) (ground M ρ b)
  | .biff a b         => .biff (ground M ρ a) (ground M ρ b)
  | .qall vars dom distinct body =>
      conjsOf ((tupleFamily (M.domSize dom) vars.length distinct).map
                 (fun is => ground M (ρ.bindAll dom vars is) body))
  | .qex vars dom distinct body =>
      disjsOf ((tupleFamily (M.domSize dom) vars.length distinct).map
                 (fun is => ground M (ρ.bindAll dom vars is) body))

/-- 无量词判定谓词（规范 §3.8 定理 `TH-2`） -/
def IsQF : Formula → Prop
  | .tt        => True
  | .ff        => True
  | .atom _    => True
  | .conj a b  => IsQF a ∧ IsQF b
  | .disj a b  => IsQF a ∧ IsQF b
  | .neg f     => IsQF f
  | .impl a b  => IsQF a ∧ IsQF b
  | .biff a b  => IsQF a ∧ IsQF b
  | .qall _ _ _ _ => False
  | .qex  _ _ _ _ => False

end Policylang
