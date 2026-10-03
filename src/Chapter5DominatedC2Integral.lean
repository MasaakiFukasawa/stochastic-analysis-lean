import Chapter5HeatFDeriv

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000

/-- Two differentiations under the integral with genuine integrable
bounds. This is used for joint space and time regularity of heat averages. -/
theorem dominated_integral_C2
    {E V Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace Z] (ν : Measure Z)
    (F : E → Z → V) (D : E → Z → E →L[ℝ] V)
    (DD : E → Z → E →L[ℝ] E →L[ℝ] V)
    (hD : ∀ p z,HasFDerivAt (fun q => F q z) (D p z) p)
    (hDD : ∀ p z,HasFDerivAt (fun q => D q z) (DD p z) p)
    (hDDc : ∀ z,Continuous (fun p => DD p z))
    (hFi : ∀ p,Integrable (F p) ν)
    (hDm : ∀ p,AEStronglyMeasurable (D p) ν)
    (hDDm : ∀ p,AEStronglyMeasurable (DD p) ν)
    (B K : Z → ℝ) (hBi : Integrable B ν) (hKi : Integrable K ν)
    (hDb : ∀ z p,‖D p z‖ ≤ B z) (hDDb : ∀ z p,‖DD p z‖ ≤ K z) :
    ContDiff ℝ 2 (fun p => ∫ z,F p z ∂ν) := by
  have hDi p : Integrable (D p) ν := hBi.mono' (hDm p) (ae_of_all _ fun z => hDb z p)
  have h0 p : HasFDerivAt (fun q => ∫ z,F q z ∂ν) (∫ z,D p z ∂ν) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := ν) (s := univ) (bound := B) (F' := D) univ_mem
    · exact Eventually.of_forall fun q => (hFi q).aestronglyMeasurable
    · exact hFi p
    · exact hDm p
    · exact ae_of_all _ fun z q _ => hDb z q
    · exact hBi
    · exact ae_of_all _ fun z q _ => hD q z
  have h1 p : HasFDerivAt (fun q => ∫ z,D q z ∂ν) (∫ z,DD p z ∂ν) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := ν) (s := univ) (bound := K) (F' := DD) univ_mem
    · exact Eventually.of_forall hDm
    · exact hDi p
    · exact hDDm p
    · exact ae_of_all _ fun z q _ => hDDb z q
    · exact hKi
    · exact ae_of_all _ fun z q _ => hDD q z
  have hc : Continuous (fun p => ∫ z,DD p z ∂ν) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply tendsto_integral_filter_of_dominated_convergence K
    · exact Eventually.of_forall hDDm
    · exact Eventually.of_forall fun q => ae_of_all _ fun z => hDDb z q
    · exact hKi
    · exact ae_of_all _ fun z => (hDDc z).continuousAt
  apply contDiff_succ_iff_hasFDerivAt.mpr
  exact ⟨_,contDiff_one_iff_hasFDerivAt.mpr ⟨_,hc,h1⟩,h0⟩

end Asakura.Chapter5
