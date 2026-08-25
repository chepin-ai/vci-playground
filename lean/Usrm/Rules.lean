-- spec/rules-formal-01/Rules.lean （骨架，sorry 待 ATP-lab 回灌）
-- 2026-08-25 拷贝自 chepin-ai/vci-library · spec/rules-formal-01/Rules.lean（lean-lab 落地）
-- 最小修复（仅求可编译，语义保持骨架原貌；逐项就地标注）：
--   [R1] N1/N4/M5 的 ∀ 绑定元补类型占位（工单/指令/决断 id，Nat；骨架 LeadsTo 暂未消费）——
--        原文件未标类型，Lean4 无法推断绑定元类型
--   [R2] Delta3 引用的 dagFrontier 原文件未定义——补占位定义（义务机 DAG 前沿节点表，
--        后续由 Usrm.Obligation 七态机供给）
inductive Ev | report | track | close | build | enable | order
  | respond | iterate | verify | feedback | act | decide | test
def Trace := List (Ev × Nat)          -- 事件 × 时刻
def LeadsTo (a b : Ev) (τ : Trace) : Prop :=
  ∀ i, (a, i) ∈ τ → ∃ j, (b, j) ∈ τ ∧ j > i
def Always (P : Trace → Prop) : Prop := ∀ τ, P τ

def N1 : Prop := Always fun τ => ∀ _x : Nat, LeadsTo .report .track τ   -- [R1] 首报必跟进
def N4 : Prop := Always fun τ => ∀ _c : Nat, LeadsTo .order .respond τ  -- [R1] 指令必响应
def M5 : Prop := Always fun τ => ∀ _d : Nat, LeadsTo .decide .test τ    -- [R1] 决断必检验
-- Δ3：残差非零 → DAG 新增节点
def dagFrontier : List Nat := []  -- [R2] 骨架占位
def Delta3 (obs exp : Int) : Prop := obs - exp ≠ 0 → ∃ n, n ∈ dagFrontier

-- ═══ 回填 #0（2026-08-25 · lean-lab 首个回填）：LeadsTo 传递性（无 sorry） ═══
-- 链式元规则 N8 的元性质：report→track→close 等链可复合
theorem leadsTo_trans {a b c : Ev} {τ : Trace}
    (hab : LeadsTo a b τ) (hbc : LeadsTo b c τ) : LeadsTo a c τ := by
  intro i hi
  have ⟨j, hbj, hij⟩ := hab i hi
  have ⟨k, hck, hjk⟩ := hbc j hbj
  exact ⟨k, hck, Nat.lt_trans hij hjk⟩
