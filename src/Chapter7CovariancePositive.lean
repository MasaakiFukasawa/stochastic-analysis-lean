import FullAuditGaussianCovariance

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Positivity of the covariance matrix does not require Gaussian inputs. -/
lemma covariance_matrix_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 P) :
    (Matrix.of (fun i j => cov[X i,X j;P])).PosSemidef := by
  have hs (a : ι → ℝ) : MemLp (fun w => ∑ i,a i*X i w) 2 P :=
    memLp_finsetSum _ (fun i _ => (hX i).const_mul (a i))
  have he (a : ι → ℝ) : cov[(fun w => ∑ i,a i*X i w),(fun w => ∑ i,a i*X i w);P]=
      dotProduct a ((Matrix.of fun i j => cov[X i,X j;P]).mulVec a) := by
    rw [covariance_fun_sum_left (fun i => (hX i).const_mul (a i)) (hs a)]
    simp_rw [covariance_const_mul_left,
      covariance_fun_sum_right (fun j => (hX j).const_mul (a j)) (hX _),covariance_const_mul_right]
    simp only [dotProduct,Matrix.mulVec,Matrix.of_apply,mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    exact covariance_comm _ _
  · intro a
    simp only [star_trivial]
    rw [← he a,covariance_self (hs a).aestronglyMeasurable.aemeasurable]
    exact variance_nonneg _ _

end Asakura.Chapter7
