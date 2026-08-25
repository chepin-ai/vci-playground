/-!
# 有限义务机活性（fairness ⇒ leads-to）· lean-lab L1+ 回填

对应义务：NMUST-02 N9′（公平调度下义务终达终态）。

模型：四态简化义务机——七态 `OblState`（`Usrm/Obligation.lean`）的活性投影：
`raised..verified` 主链折叠为 `pending → inProgress` 两段非终态，终态
`legislated / wontfix` 保留（终态侧枝 wontfix 即义务被拒绝了结）：

```
pending（stall 自环）→ inProgress（stall 自环）→ legislated（吸收）/ wontfix（吸收）
```

- 迹：core 无 Stream，以 `Nat → LState` 表无限迹；合法性 = 相邻两步均在步进关系内。
- 公平性（有限机简化版）：无最终滞留——不存在 t₀ 使迹从此永驻同一非终态
  （即任何待处理义务不会被 t₀ 之后永远避开）。
- 主定理 `fair_leads_to_terminal`：合法 ∧ 公平 ⇒ 任意 t₀ 起 ∃ t ≥ t₀ 达终态。

证明路线（core-only，构造性，不用选择公理/经典逻辑）：
自然数度规 `rank`（pending=2、inProgress=1、终态=0）沿步进单调不增
（`rank_antitone`，归纳于 `t₀ ≤ t`，传递于逐规则核判的 `lstep_rank_le`）；
公平性给出"必离开当前非终态"的晚时刻 t₁，而 rank 在非终态上单射，
故 `rank (τ t₁) < rank (τ t₀)`；rank ≤ 2 至多两次下降即归零。
两段分别收敛（`reach_terminal_from_inProgress`、`reach_terminal_from_pending`），
主定理按当前态分派。规模：kernel 秒级（无大枚举，仅 4 态逐点判定）。

弱化点（对照 N9′ 原述，有界 vs 无条件）：
1. 状态有界：四态机 rank 上界 2，存在统一有限步界；N9′ 原述面向一般义务机
   （七态格乃至开状态空间）的无条件"终达"此处未覆盖——七态全机（rank≤5）
   同法可证，留待后续回填。
2. 公平性弱化：仅排除"永久滞留于单一非终态"，弱于 LTL 强公平
   （每使能动作无限次被取）；对有限步进图，无滞留即足以推出活性。
3. 非确定性外生：迹函数给定非确定选择，未建模调度器本身
   （对照 `atp/oblig/p2_bmc.py` P2a 的显式交替调度模型）。

对照件（负·去 fairness 假设）：滞留迹 `stallTrace ≡ pending` 合法但永不达终态，
kernel 机判其非 LeadsTo（`stallTrace_not_leadsTo`）；与 `atp/oblig/p2_bmc.py` P2b
（严格 FIFO 头阻塞、无公平交替，Z3 对"k=8 步内永不处理"判 SAT 的饥饿反迹）互为印证。
-/

namespace Usrm

/-- 简化义务机四态（七态 OblState 的活性投影，见模块头） -/
inductive LState where
  | pending | inProgress | legislated | wontfix
  deriving DecidableEq, Repr

/-- 非确定步进关系：非终态可滞留（stall）或前进，终态吸收 -/
inductive LStep : LState → LState → Prop where
  | stallP  : LStep .pending .pending
  | begin   : LStep .pending .inProgress
  | stallI  : LStep .inProgress .inProgress
  | fulfill : LStep .inProgress .legislated
  | decline : LStep .inProgress .wontfix
  | stayL   : LStep .legislated .legislated
  | stayW   : LStep .wontfix .wontfix

/-- 无限迹：core 无 Stream，以 Nat 索引函数建模 -/
abbrev LTrace := Nat → LState

/-- 迹合法：每一步都是步进关系允许的非确定选择 -/
def LTrace.Valid (τ : LTrace) : Prop := ∀ n, LStep (τ n) (τ (n + 1))

/-- 终态：legislated（义务已了结）或 wontfix（义务被拒了结） -/
def LState.Terminal (s : LState) : Prop := s = .legislated ∨ s = .wontfix

/-- LeadsTo（状态迹版）：目标性质在未来某刻成立。
与 `Rules.lean` 事件迹版 `LeadsTo a b τ`（a 现 ⇒ b 后现）同型，此处直接作用于状态谓词。 -/
def LeadsTo (τ : LTrace) (P : LState → Prop) (t₀ : Nat) : Prop :=
  ∃ t, t₀ ≤ t ∧ P (τ t)

/-- 公平性（有限机简化版）：无最终滞留——两个非终态都不会从某刻起被永久驻留；
等价地：待处理义务不会被永远避开。弱化于 LTL 强公平（见模块头弱化点 2）。 -/
def LTrace.Fair (τ : LTrace) : Prop :=
  (∀ t₀, ∃ t, t₀ ≤ t ∧ τ t ≠ .pending) ∧ (∀ t₀, ∃ t, t₀ ≤ t ∧ τ t ≠ .inProgress)

/-- 距终态的自然数度规：良基递降的度量（每次有效换态严格下降） -/
def LState.rank : LState → Nat
  | .pending => 2
  | .inProgress => 1
  | .legislated => 0
  | .wontfix => 0

/-- 步进不升度规：换态必降、滞留持平、终态保 0（7 条规则逐一核判） -/
theorem lstep_rank_le {a b : LState} (h : LStep a b) : LState.rank b ≤ LState.rank a := by
  cases h <;> decide

/-- 度规沿合法迹单调不增（归纳于 `t₀ ≤ t`，传递于步进不升） -/
theorem rank_antitone {τ : LTrace} (hvalid : LTrace.Valid τ) {t₀ t : Nat} (h : t₀ ≤ t) :
    LState.rank (τ t) ≤ LState.rank (τ t₀) := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (lstep_rank_le (hvalid _)) ih

/-- rank = 0 即终态（4 态逐点核判） -/
theorem terminal_of_rank_zero {s : LState} (h : LState.rank s = 0) : LState.Terminal s := by
  cases s <;> simp_all [LState.rank, LState.Terminal]

/-- 终态吸收：终态出发的步仍停在终态（经 rank 推出，不逐条枚举） -/
theorem lstep_terminal_absorbing {s t : LState} (hs : LState.Terminal s) (h : LStep s t) :
    LState.Terminal t := by
  have h0 : LState.rank s = 0 := by
    cases hs with
    | inl e => subst e; rfl
    | inr e => subst e; rfl
  exact terminal_of_rank_zero (Nat.eq_zero_of_le_zero (h0 ▸ lstep_rank_le h))

/-- 活性步一：处理中的义务在公平迹上必达终态。
公平性给 t₁ ≥ t₀ 使 τ t₁ ≠ inProgress；rank 单调给 `rank (τ t₁) ≤ 1`，
排除回退 pending（rank=2），余者皆终态。 -/
theorem reach_terminal_from_inProgress {τ : LTrace} (hvalid : LTrace.Valid τ)
    (hfair : LTrace.Fair τ) {t₀ : Nat} (h0 : τ t₀ = .inProgress) :
    LeadsTo τ LState.Terminal t₀ := by
  obtain ⟨t₁, ht₁, hne⟩ := hfair.2 t₀
  have hr := rank_antitone hvalid ht₁
  rw [h0] at hr
  cases hs : τ t₁ with
  | pending =>
      rw [hs] at hr
      exact absurd hr (by decide)
  | inProgress => exact absurd hs hne
  | legislated => exact ⟨t₁, ht₁, Or.inl hs⟩
  | wontfix => exact ⟨t₁, ht₁, Or.inr hs⟩

/-- 活性步二：挂单的义务在公平迹上必达终态——先由公平性离 pending，
落终态则毕，落 inProgress 则由步一收敛（rank 2→1→0 的两次递降） -/
theorem reach_terminal_from_pending {τ : LTrace} (hvalid : LTrace.Valid τ)
    (hfair : LTrace.Fair τ) {t₀ : Nat} (_h0 : τ t₀ = .pending) :
    LeadsTo τ LState.Terminal t₀ := by
  obtain ⟨t₁, ht₁, hne⟩ := hfair.1 t₀
  cases hs : τ t₁ with
  | pending => exact absurd hs hne
  | inProgress =>
      obtain ⟨t₂, ht₂, hterm⟩ := reach_terminal_from_inProgress hvalid hfair hs
      exact ⟨t₂, Nat.le_trans ht₁ ht₂, hterm⟩
  | legislated => exact ⟨t₁, ht₁, Or.inl hs⟩
  | wontfix => exact ⟨t₁, ht₁, Or.inr hs⟩

/-- 主定理（N9′ 有限版活性）：合法且公平的迹上，任意时刻起义务必在有限步内到达终态
（`∃ t ≥ t₀` 即"有限步内"；终态 = legislated/wontfix）。 -/
theorem fair_leads_to_terminal {τ : LTrace} (hvalid : LTrace.Valid τ)
    (hfair : LTrace.Fair τ) (t₀ : Nat) :
    LeadsTo τ LState.Terminal t₀ := by
  cases hs : τ t₀ with
  | pending => exact reach_terminal_from_pending hvalid hfair hs
  | inProgress => exact reach_terminal_from_inProgress hvalid hfair hs
  | legislated => exact ⟨t₀, Nat.le_refl t₀, Or.inl hs⟩
  | wontfix => exact ⟨t₀, Nat.le_refl t₀, Or.inr hs⟩

/-- 滞留迹：义务永远停在 pending（合法但非公平的反迹） -/
def stallTrace : LTrace := fun _ => .pending

/-- 滞留迹合法：每步均为 stallP 自环 -/
theorem stallTrace_valid : LTrace.Valid stallTrace := fun _ => LStep.stallP

/-- 滞留迹非公平：pending 从 t₀ = 0 起被永久驻留 -/
theorem stallTrace_not_fair : ¬ LTrace.Fair stallTrace := by
  intro h
  obtain ⟨h₁, _⟩ := h
  obtain ⟨t, _, hne⟩ := h₁ 0
  exact hne rfl

-- @falsified unfair_starvation witness=滞留迹 stallTrace≡pending：合法（stallP 自环）但 ∀ t 非终态，非 LeadsTo
-- 见证来源：atp/oblig p2_bmc.py P2b——严格 FIFO 头阻塞、无公平交替时，Z3 对
-- "k=8 步内义务永不处理"判 SAT（反迹 done_t=false, ∀ t ≤ 8）；此处 kernel 机判其无限迹版。
-- 下列正命题应证不出（N9′ 的 fairness 假设不可去），故意保留为注释：
--   theorem unfair_leads_to_terminal :
--       ∀ τ, LTrace.Valid τ → LeadsTo τ LState.Terminal 0   -- ✗ 反例即 stallTrace
/-- 对照件（负）机判：去 fairness 假设，滞留迹永不达终态（N9′ 公平性前提的必要性钉） -/
theorem stallTrace_not_leadsTo : ¬ LeadsTo stallTrace LState.Terminal 0 := by
  intro h
  obtain ⟨t, _, hterm⟩ := h
  cases hterm with
  | inl e => exact absurd e (by decide)
  | inr e => exact absurd e (by decide)

end Usrm
