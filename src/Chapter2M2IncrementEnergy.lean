import Chapter2TerminalExtension
import FullAuditMartingaleCrossIncrement

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem norm_toLp_square_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖^2 = ∫ ω, f ω^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp only [hω,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- The L2 increment identity is derived from the conditional expectation
martingale identity and pull-out at the earlier time. -/
theorem continuous_martingale_increment_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ m) (X : ClosedTime T → Ω → ℝ)
    (hX : ContinuousM2Witness P F X) (s t : ClosedTime T) (hst : s ≤ t) :
    (∫ ω, (X t ω-X s ω)^2 ∂P) = (∫ ω, X t ω^2 ∂P)-(∫ ω, X s ω^2 ∂P) := by
  have hi := (memLp_two_iff_integrable_sq (hX.moment s).aestronglyMeasurable).1 (hX.moment s)
  have hd := (hX.moment t).sub (hX.moment s)
  have hid := (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).1 hd
  have hc := l2_product_increment_integrable P (hX.moment s) (hX.moment t)
  have hzero : (∫ ω, X s ω*(X t ω-X s ω) ∂P) = 0 := by
    have h := integral_congr_ae (martingale_cross_increment_zero P F hle X hX.adapted hX.moment hX.martingale s t hst)
    rw [integral_condExp (hle s)] at h
    simpa only [Pi.zero_apply,Pi.mul_apply,Pi.sub_apply,integral_zero] using h
  have he : (fun ω => X t ω^2) = (fun ω => (X t ω-X s ω)^2+2*(X s ω*(X t ω-X s ω))+X s ω^2) := by
    funext ω
    ring
  have h1 := integral_add (hid.add (hc.const_mul 2)) hi
  have h2 := integral_add hid (hc.const_mul 2)
  simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply] at h1 h2
  rw [he,h1,h2,integral_const_mul,hzero]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.norm_toLp_square_integral
#print axioms Asakura.Chapter2Complete.continuous_martingale_increment_energy
