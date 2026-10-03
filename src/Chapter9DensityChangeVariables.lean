import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory MeasureTheory.Measure Set
namespace Asakura.Chapter9
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The pointwise density-Jacobian identity implies equality of the actual
pushforward measures. No transport identity is assumed at measure level. -/
theorem density_transport_change_variables {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsAddHaarMeasure ν] (e : E ≃ₜ E)
    (D : E → E →L[ℝ] E) (hD : ∀ x,HasFDerivAt e (D x) x)
    (p q : E → ℝ) (hdet : ∀ x,0≤(D x).det)
    (hpq : ∀ x,q (e x)*(D x).det=p x) :
    (ν.withDensity (fun x => ENNReal.ofReal (p x))).map e=
      ν.withDensity (fun x => ENNReal.ofReal (q x)) := by
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    withDensity_apply _ (e.continuous.measurable hs),withDensity_apply _ hs]
  have he : e '' (e ⁻¹' s)=s := e.surjective.image_preimage s
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul ν
    (e.continuous.measurable hs) (fun x _ => (hD x).hasFDerivWithinAt)
    e.injective.injOn (fun x => ENNReal.ofReal (q x))
  rw [he] at h
  rw [h]
  apply lintegral_congr
  intro x
  rw [abs_of_nonneg (hdet x),←ENNReal.ofReal_mul (hdet x),mul_comm, hpq x]
/-- Forward transport by an invertible continuous map gives backward
transport by its actual inverse. -/
theorem homeomorph_inverse_transport {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] (e : E ≃ₜ E) (μ ν : Measure E)
    (h : μ.map e=ν) : ν.map e.symm=μ := by
  have hh := congrArg (Measure.map e.symm) h
  rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable] at hh
  simpa [Function.comp_def] using hh.symm
end Asakura.Chapter9
