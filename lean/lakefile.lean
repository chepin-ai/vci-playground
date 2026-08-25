import Lake
open Lake DSL

package «usrm-lean-lab» where
  -- 依赖取舍记录（2026-08-25 · 首个 sorry 回填）：
  --   路线：纯 Lean4 core，不挂 Mathlib。
  --   取：toolchain 即全部依赖——CI 构建秒级、零外部供应链、无版本漂移面；
  --       core 无 Order 类型类，故 PartialOrder 以极小 structure 自带（见 Usrm/Obligation.lean）。
  --   舍：Mathlib 的 Order/LTL 引理库不可用；后续深度回填（bandit 遗憾界等，见
  --       vci-usrm ure/capsules/n3-rules-01 §4）若确需 Mathlib，在此加
  --         require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.9.0"
  --       并把局部 PartialOrder 换成 Mathlib 实例（届时接受分钟级构建与依赖缓存成本）。

@[default_target]
lean_lib «Usrm» where
