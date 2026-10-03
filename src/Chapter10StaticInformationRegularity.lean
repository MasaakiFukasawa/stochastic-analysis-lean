import Chapter10StaticVariance
import Chapter10IntegratingFactorRegularity

open MeasureTheory Set
namespace Asakura.Chapter10

noncomputable def staticInformation (c : ℝ → ℝ) (S0 σ t : ℝ) : ℝ :=
  S0⁻¹+∫ s in 0..t,(c s)^2/σ^2

lemma static_information_derivative (c : ℝ → ℝ) (hc : Continuous c) (S0 σ t : ℝ) :
    HasDerivAt (staticInformation c S0 σ) ((c t)^2/σ^2) t := by
  have hf : Continuous (fun s => (c s)^2/σ^2) := (hc.pow 2).div_const _
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt).const_add _

lemma static_information_C1 (c : ℝ → ℝ) (hc : Continuous c) (S0 σ : ℝ) :
    ContDiff ℝ 1 (staticInformation c S0 σ) := by
  have hd := static_information_derivative c hc S0 σ
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt,?_⟩
  have he : deriv (staticInformation c S0 σ)=(fun t => (c t)^2/σ^2) := funext (fun t => (hd t).deriv)
  rw [he]
  exact (hc.pow 2).div_const _

lemma static_information_positive (c : ℝ → ℝ) (S0 σ : ℝ) (hS0 : 0<S0) (t : ℝ) (ht : 0≤t) :
    0<staticInformation c S0 σ t := by
  exact add_pos_of_pos_of_nonneg (inv_pos.mpr hS0)
    (intervalIntegral.integral_nonneg ht (fun s _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Extend the variance constantly to negative times only to use the real-line
Ito infrastructure; on the manuscript's time domain this is exactly 1/J. -/
noncomputable def staticVariance (c : ℝ → ℝ) (S0 σ t : ℝ) : ℝ :=
  (staticInformation c S0 σ (max t 0))⁻¹

lemma static_variance_continuous (c : ℝ → ℝ) (hc : Continuous c) (S0 σ : ℝ) (hS0 : 0<S0) :
    Continuous (staticVariance c S0 σ) := by
  exact ((static_information_C1 c hc S0 σ).continuous.comp (continuous_id.max continuous_const)).inv₀
    (fun t => (static_information_positive c S0 σ hS0 _ (le_max_right _ _)).ne')

lemma static_information_variance (c : ℝ → ℝ) (S0 σ : ℝ) (hS0 : 0<S0) (t : ℝ) (ht : 0≤t) :
    staticInformation c S0 σ t*staticVariance c S0 σ t=1 := by
  simp only [staticVariance,max_eq_left ht]
  exact mul_inv_cancel₀ (static_information_positive c S0 σ hS0 t ht).ne'

end Asakura.Chapter10
