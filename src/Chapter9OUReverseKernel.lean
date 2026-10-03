import Chapter9OUFutureRegression
import Chapter9FiniteFutureInformation
import Chapter9OUMarginalDensity
import Chapter9ReverseDensityFormula

open MeasureTheory Matrix Set
open scoped NNReal ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The displayed reverse transition kernel is the conditional law given
the full reversed natural information, including null events, for the actual
OU process. All densities are computed from the actual time-zero law. -/
theorem standard_ou_reverse_kernel_conditional {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (s t T : ℝ) (hs : 0<s) (hst : s<t) (htT : t≤T)

    (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    let p := fun r y => ∫ z,Real.exp (ouExponent z (r,y)) ∂P.map (X 0)
    P[(fun w => f (X s w))|nullAugmentedInformation P
      (MeasurableSpace.comap (fun w (r : Icc t T) => X r w) MeasurableSpace.pi)]=ᵐ[P]
      (fun w => (∫ y,f y*p s y*gaussianKernel (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) y (X t w))/p t (X t w)) := by
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  have hXm r : Measurable (X r) := (standard_ou_adapted P B N hN ξ hξ r).mono (B.le _) le_rfl
  let μ := P.map (X 0)
  let ν := P.map (X s)
  haveI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff (hXm s).aemeasurable).mpr inferInstance
  let v : ℝ≥0 := ⟨1-Real.exp (-2*(t-s)),(ou_variance_positive (t-s) (sub_pos.mpr hst)).le⟩
  have hv : v≠0 := by
    intro he
    exact (ou_variance_positive (t-s) (sub_pos.mpr hst)).ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) he)
  let R := gaussianPosteriorTest ν (Real.exp (-(t-s))) v f
  have hR : IsBoundedBorel R := gaussian_posterior_bounded_borel ν _ v hv f hf
  have hfuture := standard_ou_future_regression P B N hN hNI ξ hξ s t hs.le hst f hf
  have hfinite := finite_future_regression P X hXm t T htT (fun w => f (X s w))
    ((hf.comp (X s) (hXm s)).integrable P) R hR hfuture
  have hν : ν=volume.withDensity (fun y => ENNReal.ofReal (∫ z,Real.exp (ouExponent z (s,y)) ∂μ)) := by
    simpa only [sub_zero,gaussianKernel,ouExponent,μ,ν,X] using! standard_ou_marginal_from_time P B N hN hNI ξ hξ 0 s le_rfl hs
  have h0t : P.map (X t)=volume.withDensity (fun y => ENNReal.ofReal (∫ z,Real.exp (ouExponent z (t,y)) ∂μ)) := by
    simpa only [sub_zero,gaussianKernel,ouExponent,μ,ν,X] using! standard_ou_marginal_from_time P B N hN hNI ξ hξ 0 t le_rfl (hs.trans hst)
  have hstlaw := standard_ou_marginal_from_time P B N hN hNI ξ hξ s t hs.le hst
  have hmarg : volume.withDensity (fun y => ENNReal.ofReal (∫ z,Real.exp (ouExponent z (t,y)) ∂μ))=
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ENNReal.ofReal (∫ z,Real.exp (ouExponent z (t-s,y)) ∂ν)) :=
    h0t.symm.trans hstlaw
  apply hfinite.trans
  apply ae_of_all
  intro w
  exact ou_posterior_density_formula μ ν s t hs hst hν hmarg f (X t w)
end Asakura.Chapter9
