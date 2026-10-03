import FullAuditFinitePastIndependence
import FullAuditGaussianIndependence
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit

/-- The finite-dimensional Gaussian argument extends to the entire observation
history. The index set may contain all times and all observation coordinates. -/
theorem gaussian_error_independent_history {Ω ι : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (e : Ω → Fin d → ℝ) (I : ι → Ω → ℝ)
    (he : Measurable e) (hI : ∀ i, Measurable (I i))
    (hg : ∀ J : Finset ι,
      HasGaussianLaw (fun w => (e w, fun j : J => I j.val w)) P)
    (hc : ∀ i j, cov[(fun w => e w i), I j; P] = 0) :
    IndepFun e (fun w i => I i w) P := by
  have hh := process_independent_of_finite_coordinates
    (MeasurableSpace.comap e inferInstance) P I hI he.comap_le
    (fun J => (gaussian_independence_coordinates_written (hg J)
      (fun i j => hc i j.val)).symm)
  exact hh.symm

/-- An independent centered residual gives the conditional mean, with no
assumption that the proposed estimator is already a conditional expectation. -/
theorem independent_error_conditional_mean {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ m)
    (e a : Ω → ℝ) (he : Measurable[m] e) (hi : Integrable e P)
    (ha : StronglyMeasurable[G] a) (hia : Integrable a P)
    (hind : Indep (MeasurableSpace.comap e inferInstance) G P)
    (hzero : ∫ w, e w ∂P = 0) :
    P[(fun w => a w + e w) | G] =ᵐ[P] a := by
  letI : MeasurableSpace Ω := m
  have hz := condExp_indep_eq he.comap_le hG
    (show StronglyMeasurable[MeasurableSpace.comap e inferInstance] e from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind
  have hs := condExp_add hia hi G
  have hself := condExp_of_stronglyMeasurable hG ha hia
  filter_upwards [hz, hs] with w hw hs
  simpa only [Pi.add_apply, hself, hw, hzero, add_zero] using! hs

end Asakura.Chapter10
