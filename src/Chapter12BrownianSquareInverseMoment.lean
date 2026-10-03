import Chapter12GaussianInverseSquare
import FullAuditFiniteBrownianHitting

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- For the manuscript's square of Brownian motion, positivity of the
Malliavin covariance does not even imply finiteness of its first inverse moment. -/
theorem brownian_square_covariance_inverse_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0<T) :
    (∀ᵐ w ∂P,0<4*(T:ℝ)*(B T w)^2) ∧
      ¬Integrable (fun w => (4*(T:ℝ)*(B T w)^2)⁻¹) P := by
  have hl := hB.hasLaw_eval T
  have hn : T≠0 := hT.ne'
  have hc : 0<4*(T:ℝ) := by positivity
  have hzero : P {w | B T w=0}=0 := by
    have hh := hl.measure_eq (measurableSet_singleton (0:ℝ))
    have hz : gaussianReal 0 T {0}=0 := gaussianReal_absolutelyContinuous 0 hn (measure_singleton (0:ℝ))
    change P {w | B T w=0}=gaussianReal 0 T {0} at hh
    exact hh.trans hz
  have ha : ∀ᵐ w ∂P,B T w≠0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  refine ⟨ha.mono (fun w hw => mul_pos hc (sq_pos_of_ne_zero hw)),?_⟩
  intro hi
  have he : (fun w => (4*(T:ℝ))*((4*(T:ℝ)*(B T w)^2)⁻¹)) =
      (fun w => ((B T w)^2)⁻¹) := by
    funext w
    rw [mul_inv_rev]
    calc
      _ = ((4*(T:ℝ))*(4*(T:ℝ))⁻¹)*((B T w)^2)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hc.ne',one_mul]
  have hir := hi.const_mul (4*(T:ℝ))
  rw [he] at hir
  have hm : AEStronglyMeasurable (fun x : ℝ => (x^2)⁻¹) (P.map (B T)) := by fun_prop
  have hmap := (integrable_map_measure hm hl.aemeasurable).mpr hir
  rw [hl.map_eq] at hmap
  exact gaussian_inverse_square_not_integrable T hn hmap

end Asakura.Chapter12
