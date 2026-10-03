import Chapter6IndependentResidualNorm
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Conditional Cauchy--Schwarz with a uniformly bounded first factor. -/
theorem conditional_inner_bound {Ω E : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b X : Ω → E) (hb : AEStronglyMeasurable b P) (hX : Integrable X P)
    (K : ℝ) (hK : 0≤K) (hbound : ∀ᵐ w ∂P,‖b w‖≤K) (G : MeasurableSpace Ω) :
    ∀ᵐ w ∂P,|P[(fun w => ⟪b w,X w⟫_ℝ)|G] w|≤K*P[(fun w => ‖X w‖)|G] w := by
  letI : MeasurableSpace Ω := m
  have hi : Integrable (fun w => ⟪b w,X w⟫_ℝ) P := by
    apply (hX.norm.const_mul K).mono' (hb.inner hX.aestronglyMeasurable)
    filter_upwards [hbound] with w hw
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  have ha := abs_condExp_ae_le_condExp_abs (μ := P) (m := G) (fun w => ⟪b w,X w⟫_ℝ)
  have hm := condExp_mono (m := G) hi.abs (hX.norm.const_mul K) (hbound.mono (fun w hw =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))))
  have hs := condExp_smul (μ := P) K (fun w => ‖X w‖) G
  filter_upwards [ha,hm,hs] with w ha hm hs
  change P[(fun w => K*‖X w‖)|G] w=K*P[(fun w => ‖X w‖)|G] w at hs
  exact ha.trans (hs ▸ hm)

end Asakura.Chapter6
