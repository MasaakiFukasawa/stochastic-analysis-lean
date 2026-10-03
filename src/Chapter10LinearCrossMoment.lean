import Chapter10ErrorCovariancePositive

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The expectation of the linear drift times an error coordinate is matrix
multiplication by the actual second-moment matrix. -/
theorem linear_cross_moment {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (e : ι → Ω → ℝ) (he : ∀ i,MemLp (e i) 2 P)
    (A : Matrix ι ι ℝ) (i j : ι) :
    Integrable (fun w => (∑ k,A i k*e k w)*e j w) P ∧
    (∫ w,(∑ k,A i k*e k w)*e j w ∂P)=
      ∑ k,A i k*(∫ w,e k w*e j w ∂P) := by
  have hh k : Integrable (fun w => A i k*e k w*e j w) P := by
    convert ((he k).integrable_mul (he j)).const_mul (A i k) using 1
    funext w
    simp only [Pi.mul_apply]
    ring
  simp only [Finset.sum_mul]
  constructor
  · exact integrable_finset_sum _ (fun k _ => hh k)
  · rw [integral_finset_sum _ (fun k _ => hh k)]
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_assoc,integral_const_mul]

/-- Both drift contributions in the covariance equation, with the deterministic
noise covariance term. -/
theorem covariance_drift_expectation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ι → Ω → ℝ) (he : ∀ i,MemLp (e i) 2 P)
    (A Q : Matrix ι ι ℝ) (i j : ι) :
    let V : Matrix ι ι ℝ := fun k l => ∫ w,e k w*e l w ∂P
    (∫ w,((A*ᵥ(fun k => e k w)) i)*e j w+
      e i w*((A*ᵥ(fun k => e k w)) j)+Q i j ∂P)=
      (A*V+V*A.transpose+Q) i j := by
  have hl := linear_cross_moment P e he A i j
  have hr := linear_cross_moment P e he A j i
  have her (w : Ω) : e i w*((A*ᵥ(fun k => e k w)) j) =
      (∑ k,A j k*e k w)*e i w := mul_comm _ _
  dsimp only
  simp_rw [her]
  simp only [Matrix.mulVec,dotProduct]
  rw [integral_add (show Integrable (fun w => (∑ k,A i k*e k w)*e j w+(∑ k,A j k*e k w)*e i w) P from hl.1.add hr.1) (integrable_const _),integral_add hl.1 hr.1,
    hl.2,hr.2,integral_const]
  simp only [probReal_univ,one_smul,Matrix.add_apply,Matrix.mul_apply,transpose_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (A j k)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => mul_comm _ _)

end Asakura.Chapter10
