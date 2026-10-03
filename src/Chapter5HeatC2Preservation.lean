import Chapter5HeatFDeriv

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2200000

/-- With a bounded second derivative (as for the compactly supported
smooth approximants), averaging really preserves C² and both derivative
bounds. This extra bound is deliberately explicit: the general cylinder
lemma in the current manuscript only assumes a bounded first derivative. -/
theorem averaging_preserves_bounded_C2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hDb : ∀ x,‖D x‖ ≤ C) (hDDb : ∀ x,‖DD x‖ ≤ K) (t : ℝ) :
    let A := fun x => ∫ z,f (x+Real.sqrt t • z) ∂ν
    ContDiff ℝ 2 A ∧ (∀ x,‖fderiv ℝ A x‖ ≤ C) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K) := by
  dsimp only
  obtain ⟨h0,_,hb0,_⟩ := averaged_bounded_fderiv ν hi f D hd hDc C hDb
  obtain ⟨h1,hc1,hb1,_⟩ := averaged_bounded_fderiv ν hi D DD hdd hDDc K hDDb
  have hcD : ContDiff ℝ 1 (fun x => ∫ z,D (x+Real.sqrt t • z) ∂ν) := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    exact ⟨(fun x => ∫ z,DD (x+Real.sqrt t • z) ∂ν),
      hc1.comp (continuous_id.prodMk continuous_const),fun x => h1 x t⟩
  have he : fderiv ℝ (fun x => ∫ z,f (x+Real.sqrt t • z) ∂ν) =
      (fun x => ∫ z,D (x+Real.sqrt t • z) ∂ν) := funext (fun x => (h0 x t).fderiv)
  refine ⟨?_,?_,?_⟩
  · exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_,hcD,fun x => h0 x t⟩
  · intro x; rw [he]; exact hb0 x t
  · intro x; rw [he,(h1 x t).fderiv]; exact hb1 x t

end Asakura.Chapter5
