import Chapter12AsianDenominatorBound
import Chapter12BrownianMaximumMoments

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem asianFirstTimeMoment_measurable (x σ r T : ℝ) (hT : 0 ≤ T) :
    Measurable (asianFirstTimeMoment x σ r T hT) := by
  let f := fun w : C(Icc (0:ℝ) T,ℝ) × ℝ =>
    w.2*x*Real.exp ((r-σ^2/2)*w.2+σ*w.1 (projIcc 0 T hT w.2))
  have hf : Continuous f := by unfold f; fun_prop
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))).measurable
  convert hm using 1
  funext w
  exact intervalIntegral.integral_of_le hT

theorem asian_first_time_inverse_bound (x σ r T : ℝ)
    (hx : 0 < x) (hT : 0 < T) (f : C(Icc (0:ℝ) T,ℝ)) :
    |(asianFirstTimeMoment x σ r T hT.le f)⁻¹| ≤
      (2/(T^2*x))*Real.exp (|r-σ^2/2| *T+|σ| *‖f‖) := by
  have hi := asian_first_time_moment_pos x σ r T hx hT f
  rw [abs_of_pos (inv_pos.mpr hi)]
  have hlo := asian_first_time_moment_lower_bound x σ r T hx hT f
  have hb := one_div_le_one_div_of_le (show 0 < (T^2/2)*(x*Real.exp
    (-|r-σ^2/2| *T-|σ| *‖f‖)) by positivity) hlo
  rw [one_div] at hb
  apply hb.trans_eq
  rw [one_div,mul_inv_rev,mul_inv_rev,← Real.exp_neg]
  have he : -(-|r-σ^2/2| *T-|σ| *‖f‖) = |r-σ^2/2| *T+|σ| *‖f‖ := by ring
  rw [he]
  field_simp
  <;> ring

/-- All finite inverse moments of the actual Asian denominator follow
from the pathwise lower bound and the Brownian maximal tail calculation. -/
theorem asian_first_time_inverse_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x σ r : ℝ) (hx : 0 < x) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun w => (asianFirstTimeMoment x σ r T (show 0 ≤ (T:ℝ) from hT.le) (X w))⁻¹) p P := by
  have ht : (0:ℝ) < T := hT
  have hbound := (brownian_path_exponential_memLp P B hB hm hc T X hXm he |σ| p hp).const_mul
    ((2/(T^2*x))*Real.exp (|r-σ^2/2| *T))
  apply hbound.of_le (((asianFirstTimeMoment_measurable x σ r T ht.le).comp hXm).inv.aestronglyMeasurable)
  exact ae_of_all P fun w => by
    have hb := asian_first_time_inverse_bound x σ r T hx ht (X w)
    change |(asianFirstTimeMoment x σ r T ht.le (X w))⁻¹| ≤
      |((2/(T^2*x))*Real.exp (|r-σ^2/2| *T))*Real.exp (|σ| *‖X w‖)|
    have hpos : 0 ≤ ((2/(T^2*x))*Real.exp (|r-σ^2/2| *T))*Real.exp (|σ| *‖X w‖) := by positivity
    rw [abs_of_nonneg hpos,mul_assoc,← Real.exp_add]
    exact hb

end Asakura.Chapter12
