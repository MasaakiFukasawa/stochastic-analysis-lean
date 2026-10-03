import Chapter6NovikovEndpointHolder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

/-- Passing to the endpoint in the Holder bound forces the mean to be at
least one; this is the limiting step not supplied by strict Novikov. -/
theorem endpoint_holder_limit (I K : ℝ) (hK : 0 < K)
    (hbound : ∀ l : ℝ,0 < l → l < 1 → 1 ≤ I^l*K^(1-l)) : 1 ≤ I := by
  let l := fun n : ℕ => 1-1/(n+1:ℝ)
  have hl : Tendsto l atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hIp := (Real.continuousAt_const_rpow' (a := I) (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hl
  have hKp := (Real.continuousAt_const_rpow (a := K) (b := 0) hK.ne').tendsto.comp
    (show Tendsto (fun n => 1-l n) atTop (𝓝 0) by simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hl)
  have hlim : Tendsto (fun n => I^(l n)*K^(1-l n)) atTop (𝓝 I) := by
    simpa only [Function.comp_def,Real.rpow_one,Real.rpow_zero,mul_one] using hIp.mul hKp
  apply ge_of_tendsto hlim
  apply eventually_atTop.2 ⟨1,?_⟩
  intro n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n+1:ℝ) := by positivity
  apply hbound
  · dsimp [l]
    exact sub_pos.mpr ((div_lt_one hd).mpr (by linarith))
  · dsimp [l]
    exact sub_lt_self _ (div_pos zero_lt_one hd)

end Asakura.Chapter6
