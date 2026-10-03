import Chapter5HeatFDeriv

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- The regularity that really survives the manuscript's backwards
averaging and identification of the last two coordinates is C¹ with a
bounded gradient. No bound on the original second derivatives is used. -/
theorem cylinder_recursion_preserves_bounded_C1
    {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hDb : ∀ x,‖D x‖ ≤ C) (L : K →L[ℝ] E) (t : ℝ) :
    let g := fun x => ∫ z,f (L x+Real.sqrt t • z) ∂ν
    ContDiff ℝ 1 g ∧ (∀ x,‖fderiv ℝ g x‖ ≤ C*‖L‖) := by
  dsimp only
  obtain ⟨ha,hac,hab,_⟩ := averaged_bounded_fderiv ν hi f D hd hDc C hDb
  have hs : ContDiff ℝ 1 (fun x => ∫ z,f (x+Real.sqrt t • z) ∂ν) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨_,hac.comp (continuous_id.prodMk continuous_const),fun x => ha x t⟩
  refine ⟨hs.comp L.contDiff,?_⟩
  intro x
  have hh := (ha (L x) t).comp x L.hasFDerivAt
  simp only [Function.comp_def] at hh
  rw [hh.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hab (L x) t) (norm_nonneg L))

end Asakura.Chapter5
