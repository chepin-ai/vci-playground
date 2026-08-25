/-!
# 义务⇄证据 Galois 连接（P3 机判回填）· lean-lab L1

与 `atp/oblig/p3_galois_valid.smt2`（cvc5 实例，期望 unsat）逐条对齐：

```
α(o) = o / 2          （下伴 lower adjoint：义务 o 要求的证据强度）
γ(e) = min(3, 2e + 1) （上伴 upper adjoint：证据 e 可卸的最弱义务）
```

Galois 公理：`∀ o e, o ≤ γ e ↔ α o ≤ e`（4×4 全表核判，无 sorry）。

对照件（负·ATP 正反互补）：`gammaWrong(e) = min(3, 2e)` 破坏公理，
cvc5 在 `atp/oblig/p3_galois_broken.smt2` 判 sat 并给见证 (o,e)=(1,0)；
本文件末以 `example` 机判该破坏，并把失败示例保留为注释。

纯 Lean4 core 路线：复用 `Usrm/Obligation.lean` 的极小 `PartialOrder` structure，
一般化定理（Galois 连接 ⇒ 双单调 + 闭包/核）不依赖任何外部库。
-/

import Usrm.Obligation

namespace Usrm

/-- 义务四态链 `o0 < o1 < o2 < o3`（对应 smt2 中 0..3） -/
inductive Obl4 where
  | o0 | o1 | o2 | o3
  deriving DecidableEq, Repr

/-- 证据四态链 `e0 < e1 < e2 < e3`（对应 smt2 中 0..3） -/
inductive Ev4 where
  | e0 | e1 | e2 | e3
  deriving DecidableEq, Repr

/-- 义务态到序数的嵌入 -/
def Obl4.toNat : Obl4 → Nat
  | .o0 => 0
  | .o1 => 1
  | .o2 => 2
  | .o3 => 3

/-- 证据态到序数的嵌入 -/
def Ev4.toNat : Ev4 → Nat
  | .e0 => 0
  | .e1 => 1
  | .e2 => 2
  | .e3 => 3

/-- 偏序表（Bool 版，链序即序数比较，便于 kernel 计算判定） -/
def Obl4.leb (a b : Obl4) : Bool := Nat.ble a.toNat b.toNat

/-- 偏序表（Bool 版） -/
def Ev4.leb (a b : Ev4) : Bool := Nat.ble a.toNat b.toNat

/-- 偏序的 Prop 版 -/
def Obl4.Le (a b : Obl4) : Prop := Obl4.leb a b = true

/-- 偏序的 Prop 版 -/
def Ev4.Le (a b : Ev4) : Prop := Ev4.leb a b = true

/-- 自反性：4 态逐点核判 -/
theorem Obl4.le_refl : ∀ a : Obl4, Obl4.leb a a = true := by
  intro a; cases a <;> decide

/-- 反对称性：4×4 全表核判 -/
theorem Obl4.le_antisymm : ∀ a b : Obl4,
    Obl4.leb a b = true → Obl4.leb b a = true → a = b := by
  intro a b; cases a <;> cases b <;> decide

/-- 传递性：4×4×4 全表核判 -/
theorem Obl4.le_trans : ∀ a b c : Obl4,
    Obl4.leb a b = true → Obl4.leb b c = true → Obl4.leb a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- 自反性：4 态逐点核判 -/
theorem Ev4.le_refl : ∀ a : Ev4, Ev4.leb a a = true := by
  intro a; cases a <;> decide

/-- 反对称性：4×4 全表核判 -/
theorem Ev4.le_antisymm : ∀ a b : Ev4,
    Ev4.leb a b = true → Ev4.leb b a = true → a = b := by
  intro a b; cases a <;> cases b <;> decide

/-- 传递性：4×4×4 全表核判 -/
theorem Ev4.le_trans : ∀ a b c : Ev4,
    Ev4.leb a b = true → Ev4.leb b c = true → Ev4.leb a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- 义务链是 PartialOrder（复用 Obligation.lean 的极小 structure） -/
def Obl4.partialOrder : PartialOrder Obl4 where
  le := Obl4.Le
  le_refl := Obl4.le_refl
  le_antisymm := Obl4.le_antisymm
  le_trans := Obl4.le_trans

/-- 证据链是 PartialOrder -/
def Ev4.partialOrder : PartialOrder Ev4 where
  le := Ev4.Le
  le_refl := Ev4.le_refl
  le_antisymm := Ev4.le_antisymm
  le_trans := Ev4.le_trans

/-- 下伴 `α`：义务 o 要求的证据强度（= o / 2，与 smt2 `(div o 2)` 对齐） -/
def alpha : Obl4 → Ev4
  | .o0 => .e0
  | .o1 => .e0
  | .o2 => .e1
  | .o3 => .e1

/-- 上伴 `γ`：证据 e 可卸的最弱义务（= min(3, 2e + 1)，与 smt2 ite 对齐） -/
def gamma : Ev4 → Obl4
  | .e0 => .o1
  | .e1 => .o3
  | .e2 => .o3
  | .e3 => .o3

/-- 语义钉：α 的 Nat 规范实现 `o / 2` -/
theorem alpha_spec : ∀ o : Obl4, (alpha o).toNat = o.toNat / 2 := by
  intro o; cases o <;> decide

/-- 语义钉：γ 的 Nat 规范实现 `min 3 (2e + 1)` -/
theorem gamma_spec : ∀ e : Ev4, (gamma e).toNat = min 3 (2 * e.toNat + 1) := by
  intro e; cases e <;> decide

/-- P3 主定理：义务⇄证据 Galois 连接，4×4 全表核判（cvc5 `p3_galois_valid` 判 unsat 的正面对应） -/
theorem galois_conn :
    ∀ (o : Obl4) (e : Ev4), Obl4.Le o (gamma e) ↔ Ev4.Le (alpha o) e := by
  intro o e; cases o <;> cases e <;> decide

/-- 一般化：任意偏序集之间的 Galois 连接 ⇒ 双单调 + 闭包/核。
伴随基本定理的四个分量，全部从公理 `gc` 与偏序三法则推出（无逐点枚举）。 -/
theorem galois_conn_general {A B : Type} (P : PartialOrder A) (Q : PartialOrder B)
    (f : A → B) (g : B → A)
    (gc : ∀ a b, P.le a (g b) ↔ Q.le (f a) b) :
    (∀ a a', P.le a a' → Q.le (f a) (f a'))
    ∧ (∀ b b', Q.le b b' → P.le (g b) (g b'))
    ∧ (∀ a, P.le a (g (f a)))
    ∧ (∀ b, Q.le (f (g b)) b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- f 单调：a ≤ a' ≤ g (f a')，经 gc 换边得 f a ≤ f a'
    intro a a' h
    exact (gc a (f a')).mp
      (P.le_trans _ _ _ h ((gc a' (f a')).mpr (Q.le_refl _)))
  · -- g 单调：f (g b) ≤ b ≤ b'，经 gc 换边得 g b ≤ g b'
    intro b b' h
    exact (gc (g b) b').mpr
      (Q.le_trans _ _ _ ((gc (g b) b).mp (P.le_refl _)) h)
  · -- 闭包（closure）：a ≤ g (f a)，由 f a ≤ f a 自反经 gc 换边
    intro a
    exact (gc a (f a)).mpr (Q.le_refl _)
  · -- 核（kernel）：f (g b) ≤ b，由 g b ≤ g b 自反经 gc 换边
    intro b
    exact (gc (g b) b).mp (P.le_refl _)

/-- α 单调：由一般化定理实例化（非逐点枚举） -/
theorem alpha_mono : ∀ a b : Obl4, Obl4.Le a b → Ev4.Le (alpha a) (alpha b) :=
  (galois_conn_general Obl4.partialOrder Ev4.partialOrder alpha gamma galois_conn).1

/-- γ 单调：由一般化定理实例化 -/
theorem gamma_mono : ∀ a b : Ev4, Ev4.Le a b → Obl4.Le (gamma a) (gamma b) :=
  (galois_conn_general Obl4.partialOrder Ev4.partialOrder alpha gamma galois_conn).2.1

/-- 闭包性质：o ≤ γ (α o)（义务不超过自身要求证据所能卸的最弱义务） -/
theorem closure_le : ∀ o : Obl4, Obl4.Le o (gamma (alpha o)) :=
  (galois_conn_general Obl4.partialOrder Ev4.partialOrder alpha gamma galois_conn).2.2.1

/-- 核性质：α (γ e) ≤ e（证据不被其可卸义务的要求反超） -/
theorem kernel_le : ∀ e : Ev4, Ev4.Le (alpha (gamma e)) e :=
  (galois_conn_general Obl4.partialOrder Ev4.partialOrder alpha gamma galois_conn).2.2.2

/-- 对照件（负）：`γ_wrong(e) = min(3, 2e)`，cvc5 `p3_galois_broken.smt2` 的破坏版上伴 -/
def gammaWrong : Ev4 → Obl4
  | .e0 => .o0
  | .e1 => .o2
  | .e2 => .o3
  | .e3 => .o3

/-- 语义钉：γ_wrong 的 Nat 规范实现 `min 3 (2e)` -/
theorem gammaWrong_spec : ∀ e : Ev4, (gammaWrong e).toNat = min 3 (2 * e.toNat) := by
  intro e; cases e <;> decide

-- @falsified galois_gamma_wrong witness=(o,e)=(1,0): 1 ≤ min(3,2·0)=0 为假 而 α(1)=0 ≤ 0 为真
-- 见证来源：cvc5 对 atp/oblig/p3_galois_broken.smt2 判 sat，模型 (o,e)=(1,0)，与 P3 正例
-- （p3_galois_valid.smt2 判 unsat）构成 ATP 正反互补。下列正命题应证不出，故意保留为注释：
--   example : ∀ (o : Obl4) (e : Ev4), Obl4.Le o (gammaWrong e) ↔ Ev4.Le (alpha o) e := by
--     intro o e; cases o <;> cases e <;> decide   -- ✗ (o1,e0) 分支 decide 失败

/-- 负面对照的机判：γ_wrong 破坏 Galois 公理，反例即 cvc5 见证 (o,e)=(1,0) -/
example : ¬ (∀ (o : Obl4) (e : Ev4), Obl4.Le o (gammaWrong e) ↔ Ev4.Le (alpha o) e) := by
  intro h
  have hw := h Obl4.o1 Ev4.e0
  revert hw
  decide

end Usrm
