import Chapter3GeneralDiagonalQuadraticApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic variation of a linear combination is proved directly
from the covariance witnesses and their finite-variation parts. -/
theorem quadratic_variation_linear_combination
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hA : LocalCovarianceWitness P F X X A)
    (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C) (a b : ℝ) :
    LocalCovarianceWitness P F
      (fun t ω => a*X t ω+b*Y t ω) (fun t ω => a*X t ω+b*Y t ω)
      (fun t ω => a^2*A t ω+2*a*b*C t ω+b^2*B t ω) := by
  constructor
  · have h := ((hA.defect.smul P F (a^2)).add P F hF hle
      (hC.defect.smul P F (2*a*b))).add P F hF hle (hB.defect.smul P F (b^2))
    convert h using 1
    funext t ω
    ring
  · exact ((hA.variation.smul F (a^2)).add F (hC.variation.smul F (2*a*b))).add F
      (hB.variation.smul F (b^2))

/-- A common partition controls the half-sum and half-difference with the
same dyadic rate; there is no loss in the polarization normalization. -/
theorem half_combination_increment_bounds
    {ι : Type*} [LinearOrder ι] (X Y : ι → ℝ) (a b t : ι) (δ : ℝ)
    (hx : ‖X (min b t)-X (min a t)‖ ≤ δ)
    (hy : ‖Y (min b t)-Y (min a t)‖ ≤ δ) :
    ‖((1/2:ℝ)*X (min b t)+(1/2:ℝ)*Y (min b t))-
      ((1/2:ℝ)*X (min a t)+(1/2:ℝ)*Y (min a t))‖ ≤ δ ∧
    ‖((1/2:ℝ)*X (min b t)+(-1/2:ℝ)*Y (min b t))-
      ((1/2:ℝ)*X (min a t)+(-1/2:ℝ)*Y (min a t))‖ ≤ δ := by
  have hx' : |X (min b t)-X (min a t)| ≤ δ := hx
  have hy' : |Y (min b t)-Y (min a t)| ≤ δ := hy
  have hp := Asakura.Chapter3Written.half_sum_oscillation hx' hy'
  have hm := Asakura.Chapter3Written.half_sum_oscillation hx'
    (show |-(Y (min b t)-Y (min a t))| ≤ δ by simpa only [abs_neg] using hy')
  constructor
  · convert hp using 1 <;> congr 1 <;> ring
  · convert hm using 1 <;> congr 1 <;> ring

/-- Uniform limits are stable under the subtraction used in polarization. -/
theorem uniform_limit_sub
    {ι : Type*} (U V : ℕ → ι → ℝ) (u v : ι → ℝ)
    (hU : TendstoUniformly U u atTop) (hV : TendstoUniformly V v atTop) :
    TendstoUniformly (fun n t => U n t-V n t) (fun t => u t-v t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hU (ε/2) (half_pos hε),
    Metric.tendstoUniformly_iff.mp hV (ε/2) (half_pos hε)] with n hu hv
  intro t
  have hu' : |u t-U n t| < ε/2 := by simpa only [Real.dist_eq] using hu t
  have hv' : |v t-V n t| < ε/2 := by simpa only [Real.dist_eq] using hv t
  have hb : |(u t-U n t)-(v t-V n t)| ≤ |u t-U n t|+|v t-V n t| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (u t-U n t) (v t-V n t)
  have h := hb.trans_lt (add_lt_add hu' hv')
  have he : (u t-U n t)-(v t-V n t) = (u t-v t)-(U n t-V n t) := by ring
  rw [he,add_halves] at h
  simpa only [Real.dist_eq] using h

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.quadratic_variation_linear_combination
#print axioms Asakura.Chapter3Complete.half_combination_increment_bounds
#print axioms Asakura.Chapter3Complete.uniform_limit_sub
