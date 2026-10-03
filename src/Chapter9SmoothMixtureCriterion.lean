import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'
set_option backward.isDefEq.respectTransparency false

/-- Differentiation to every order under a finite-measure integral.
The Taylor coefficients here are actual successive derivatives, not a
formal power series assumed to converge. Bounds are uniform on an open
parameter neighborhood and may depend on the derivative order. -/
theorem smooth_mixture_taylor {E V Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (U : Set E) (hU : IsOpen U) (F : E → Z → V)
    (J : Z → E → FormalMultilinearSeries ℝ E V)
    (hJ : ∀ z,HasFTaylorSeriesUpToOn ∞ (fun x => F x z) (J z) U)
    (hm : ∀ n x,x∈U → AEStronglyMeasurable (fun z => J z x n) μ)
    (B : ℕ → ℝ) (hb : ∀ n z x,x∈U → ‖J z x n‖≤B n) :
    HasFTaylorSeriesUpToOn ∞ (fun x => ∫ z,F x z ∂μ)
      (fun x n => ∫ z,J z x n ∂μ) U := by
  have hi n x (hx : x∈U) : Integrable (fun z => J z x n) μ :=
    (integrable_const (B n)).mono' (hm n x hx) (ae_of_all _ (fun z => hb n z x hx))
  let K : E → FormalMultilinearSeries ℝ E V := fun x n => ∫ z,J z x n ∂μ
  have ht : HasFTaylorSeriesUpToOn ∞ (fun x => ∫ z,F x z ∂μ) K U := by
    constructor
    · intro x hx
      let C := (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
      have hc := C.integral_comp_comm (hi 0 x hx)
      change (∫ z,(J z x 0).curry0 ∂μ)=(K x 0).curry0 at hc
      rw [←hc]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => (hJ z).zero_eq x hx)
    · intro n hn x hx
      let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).toContinuousLinearEquiv.toContinuousLinearMap
      have hcm q (hq : q∈U) : AEStronglyMeasurable (fun z => (J z q (n+1)).curryLeft) μ :=
        C.continuous.comp_aestronglyMeasurable (hm (n+1) q hq)
      have hd : HasFDerivAt (fun q => ∫ z,J z q n ∂μ)
          (∫ z,(J z x (n+1)).curryLeft ∂μ) x := by
        apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := U) (bound := fun _ => B (n+1))
          (hU.mem_nhds hx)
        · exact (show ∀ᶠ q in 𝓝 x,q∈U from hU.mem_nhds hx).mono (fun q hq => hm n q hq)
        · exact hi n x hx
        · exact hcm x hx
        · exact ae_of_all _ (fun z q hq => by simpa only [ContinuousMultilinearMap.curryLeft_norm] using hb (n+1) z q hq)
        · exact integrable_const _
        · exact ae_of_all _ (fun z q hq => ((hJ z).fderivWithin n hn q hq).hasFDerivAt (hU.mem_nhds hq))
      letI : NormedAddCommGroup (E →L[ℝ] (E [×n]→L[ℝ] V)) := inferInstance
      have hci : Integrable (fun z => ((J z x (n+1)).curryLeft : E →L[ℝ] (E [×n]→L[ℝ] V))) μ :=
        (integrable_const (B (n+1))).mono' (hcm x hx) (ae_of_all _ (fun z => by
          simpa only [ContinuousMultilinearMap.curryLeft_norm] using hb (n+1) z x hx))
      have hc : (∫ z,(J z x (n+1)).curryLeft ∂μ)=(K x (n+1)).curryLeft := by
        ext v w
        rw [ContinuousLinearMap.integral_apply hci]
        have hv : Integrable (fun z => (J z x (n+1)).curryLeft v) μ :=
          (ContinuousLinearMap.apply ℝ (E [×n]→L[ℝ] V) v).integrable_comp hci
        rw [ContinuousMultilinearMap.integral_apply hv]
        change (∫ z,J z x (n+1) (Fin.cons v w) ∂μ)=(∫ z,J z x (n+1) ∂μ) (Fin.cons v w)
        exact (ContinuousMultilinearMap.integral_apply (hi (n+1) x hx) _).symm
      rw [hc] at hd
      exact hd.hasFDerivWithinAt
    · intro n hn x hx
      apply tendsto_integral_filter_of_dominated_convergence (fun _ => B n)
      · exact (show ∀ᶠ q in 𝓝[U] x,q∈U from self_mem_nhdsWithin).mono (fun q hq => hm n q hq)
      · exact (show ∀ᶠ q in 𝓝[U] x,q∈U from self_mem_nhdsWithin).mono (fun q hq => ae_of_all _ (fun z => hb n z q hq))
      · exact integrable_const _
      · exact ae_of_all _ (fun z => (hJ z).cont n hn x hx)
  exact ht

theorem smooth_mixture_criterion {E V Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (U : Set E) (hU : IsOpen U) (F : E → Z → V)
    (J : Z → E → FormalMultilinearSeries ℝ E V)
    (hJ : ∀ z,HasFTaylorSeriesUpToOn ∞ (fun x => F x z) (J z) U)
    (hm : ∀ n x,x∈U → AEStronglyMeasurable (fun z => J z x n) μ)
    (B : ℕ → ℝ) (hb : ∀ n z x,x∈U → ‖J z x n‖≤B n) :
    ContDiffOn ℝ ∞ (fun x => ∫ z,F x z ∂μ) U := by
  exact (smooth_mixture_taylor μ U hU F J hJ hm B hb).contDiffOn
end Asakura.Chapter9
