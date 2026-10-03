import Chapter7RandomIntegralSquare

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma random_field_energy {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [SigmaFinite P] (μ : Measure S) [IsFiniteMeasure μ]
    (H : Ω × S → ℝ) (hm : Measurable H) (K : ℝ)
    (hh : ∀ᵐ s ∂μ,Integrable (fun w => H (w,s)^2) P ∧ (∫ w,H (w,s)^2 ∂P) ≤ K) :
    MemLp H 2 (P.prod μ) := by
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff' (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨hh.mono (fun s hs => hs.1),?_⟩
  have hme := ((hm.pow_const 2).norm.stronglyMeasurable.integral_prod_left' (μ := P))
  apply (integrable_const K).mono' hme.aestronglyMeasurable
  filter_upwards [hh] with s hs
  simp only [Real.norm_eq_abs,abs_sq]
  rw [abs_of_nonneg (integral_nonneg (fun w => sq_nonneg (H (w,s))))]
  exact hs.2

end Asakura.Chapter7
