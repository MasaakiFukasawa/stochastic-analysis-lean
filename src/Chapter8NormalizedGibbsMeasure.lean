import Chapter8GibbsC2Generator
import Chapter6DensityProbability

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000

/-- The manuscript's weighted second-moment hypothesis constructs an
actual probability measure, with integrable norm and second moment. -/
theorem normalized_gibbs_measure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    (U : E → ℝ) (hU : Continuous U) (β : ℝ)
    (hi : Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x))) :
    let Z := ∫ x : E, Real.exp (-β*U x)
    let π := volume.withDensity (fun x : E => ENNReal.ofReal (Z⁻¹*Real.exp (-β*U x)))
    0 < Z ∧ IsProbabilityMeasure π ∧ Integrable (fun x : E => ‖x‖) π ∧
      Integrable (fun x : E => ‖x‖^2) π ∧
      (∀ f : E → ℝ, (∫ x,f x ∂π)=Z⁻¹*∫ x,Real.exp (-β*U x)*f x) := by
  dsimp only
  let ρ := fun x : E => Real.exp (-β*U x)
  let Z := ∫ x : E, ρ x
  have hρ : Continuous ρ := by fun_prop
  have hρpos x : 0 < ρ x := Real.exp_pos _
  have h0 : Integrable ρ := by
    apply hi.mono' hρ.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_pos (hρpos x)]
    change ρ x ≤ (1+‖x‖^2)*ρ x
    nlinarith [sq_nonneg ‖x‖,hρpos x]
  have hZ : 0 < Z := integral_exp_pos h0
  have hnorm : (∫ x, Z⁻¹*ρ x)=1 := by rw [integral_const_mul]; exact inv_mul_cancel₀ hZ.ne'
  have hp := Asakura.Chapter6.mean_one_density_probability volume (fun x => Z⁻¹*ρ x)
    (h0.const_mul Z⁻¹) (ae_of_all _ fun x => by positivity) hnorm
  have hm : Measurable (fun x => ENNReal.ofReal (Z⁻¹*ρ x)) := by fun_prop
  have ht : ∀ᵐ x ∂(volume : Measure E), ENNReal.ofReal (Z⁻¹*ρ x)<⊤ := ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have he (f : E → ℝ) :
      (fun x => (ENNReal.ofReal (Z⁻¹*ρ x)).toReal • f x) = fun x => Z⁻¹*(ρ x*f x) := by
    funext x
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring
  refine ⟨hZ,hp,?_,?_,?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hm ht,he]
    apply (hi.const_mul Z⁻¹).mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hn : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (hρpos x).le)
      (inv_nonneg.mpr hZ.le)).trans_eq (by dsimp only [ρ]; ring)
  · rw [integrable_withDensity_iff_integrable_smul' hm ht,he]
    apply (hi.const_mul Z⁻¹).mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hn : ‖x‖^2 ≤ 1+‖x‖^2 := by linarith
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (hρpos x).le)
      (inv_nonneg.mpr hZ.le)).trans_eq (by dsimp only [ρ]; ring)
  · intro f
    rw [integral_withDensity_eq_integral_toReal_smul hm ht,he,integral_const_mul]

end Asakura.Chapter8
