import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.Notation
import Mathlib.Tactic.Positivity

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem lp_affine_norm_bound {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1≤p)]
    (u : Lp E p P) (v : Lp F p P) (C r : ℝ) (hC : 0≤C) (hr : 0≤r)
    (hb : ∀ᵐw ∂P,‖u w‖≤C*(‖v w‖+r)) : ‖u‖≤C*(‖v‖+r) := by
  let V : Lp ℝ p P := (Lp.memLp v).norm.toLp (fun w => ‖v w‖)
  let R : Lp ℝ p P := (memLp_const r).toLp (fun _ : Ω => r)
  have hV : ∀ᵐw ∂P,V w=‖v w‖ := (Lp.memLp v).norm.coeFn_toLp
  have hR : ∀ᵐw ∂P,R w=r := (memLp_const r).coeFn_toLp
  have hcmp : ‖u‖≤C*‖V+R‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hb,hV,hR,Lp.coeFn_add V R] with w hw hv hrr ha
    rw [ha,Pi.add_apply,hv,hrr,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) hr)]
    exact hw
  have hVn : ‖V‖≤‖v‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hV] with w hw
    rw [hw,norm_norm]
  have hRn : ‖R‖≤r := by
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (f:=R) hr
      (hR.mono (fun w hw => by rw [hw,Real.norm_eq_abs,abs_of_nonneg hr]))
  exact hcmp.trans (mul_le_mul_of_nonneg_left ((norm_add_le V R).trans (add_le_add hVn hRn)) hC)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.lp_affine_norm_bound
