/-!
# 义务机七态格（obligation-machine 7-state poset）· lean-lab 首个 sorry 回填本体

状态拓扑（与 `atp/oblig/p1_lattice_pos.in` 的 Prover9 模型逐条对齐，P1 已机判为 lattice）：

```
raised < fixed < implemented < tested < verified < legislated   （主链）
raised < wontfix < legislated                                    （终态侧枝）
```

纯 Lean4 core 路线（不挂 Mathlib，取舍记录见 `lakefile.lean` 注释）：
定义七态归纳类型 + 偏序表，并证明它是 PartialOrder——自反/反对称/传递三法则
全部 `decide` 闭核，无 sorry。
-/

namespace Usrm

/-- 义务机七态：主链六态 + 终态侧枝 `wontfix` -/
inductive OblState where
  | raised | fixed | implemented | tested | verified | legislated | wontfix
  deriving DecidableEq, Repr

/-- 偏序表（Bool 版，便于 kernel 计算判定）：
与 `p1_lattice_pos.in` 的 `le` 表一一对应（24 个真对，其余为假）。 -/
def OblState.leb : OblState → OblState → Bool
  | .raised, _ => true
  | _, .legislated => true
  | .fixed, .fixed | .fixed, .implemented | .fixed, .tested | .fixed, .verified => true
  | .implemented, .implemented | .implemented, .tested | .implemented, .verified => true
  | .tested, .tested | .tested, .verified => true
  | .verified, .verified => true
  | .wontfix, .wontfix => true
  | _, _ => false

/-- 偏序的 Prop 版 -/
def OblState.Le (a b : OblState) : Prop := OblState.leb a b = true

/-- 自反性：7 态逐点核判 -/
theorem OblState.le_refl : ∀ a : OblState, OblState.leb a a = true := by
  intro a; cases a <;> decide

/-- 反对称性：7×7 全表核判 -/
theorem OblState.le_antisymm : ∀ a b : OblState,
    OblState.leb a b = true → OblState.leb b a = true → a = b := by
  intro a b; cases a <;> cases b <;> decide

/-- 传递性：7×7×7 全表核判 -/
theorem OblState.le_trans : ∀ a b c : OblState,
    OblState.leb a b = true → OblState.leb b c = true → OblState.leb a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- 极小偏序结构（core 自带；若未来挂 Mathlib，替换为 Mathlib `PartialOrder` 实例） -/
structure PartialOrder (α : Type) where
  le : α → α → Prop
  le_refl : ∀ a, le a a
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_trans : ∀ a b c, le a b → le b c → le a c

/-- 义务机七态格是 PartialOrder：三法则全部为无 sorry 的机器证明 -/
def OblState.partialOrder : PartialOrder OblState where
  le := OblState.Le
  le_refl := OblState.le_refl
  le_antisymm := OblState.le_antisymm
  le_trans := OblState.le_trans

/-- 语义钉：`wontfix` 是终态侧枝——上接 `legislated`、下接 `raised`，与主链中段不可比 -/
theorem OblState.wontfix_side_branch :
    OblState.leb .raised .wontfix = true
    ∧ OblState.leb .wontfix .legislated = true
    ∧ OblState.leb .wontfix .fixed = false
    ∧ OblState.leb .tested .wontfix = false := by
  decide

end Usrm
