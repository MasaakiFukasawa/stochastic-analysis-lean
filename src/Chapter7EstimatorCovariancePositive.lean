import Chapter7CovariancePositive
import Chapter7BrownianProductFourth

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

noncomputable def estimatorLimitCovariance {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
    fun p q => (S*S.transpose) p.1 q.1*(S*S.transpose) p.2 q.2+
      (S*S.transpose) p.1 q.2*(S*S.transpose) p.2 q.1

/-- The displayed limiting covariance is the covariance of ZZᵀ-a,
using the actual mixed fourth Gaussian moments. -/
theorem estimator_covariance_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (S : Matrix (Fin d) (Fin d) ℝ) : (estimatorLimitCovariance S).PosSemidef := by
  let Z := fun i w => ∑ j,S i j*(B.W j (realTimeClamp 1) w-B.W j (realTimeClamp 0) w)
  let a := S*S.transpose
  let X := fun p : Fin d × Fin d => fun w => Z p.1 w*Z p.2 w-a p.1 p.2
  have ha i j : a i j=∑ k,S i k*S j k := by simp only [a,Matrix.mul_apply,Matrix.transpose_apply]
  have hprod i j : MemLp (fun w => Z i w*Z j w) 2 P :=
    (brownian_product_fourth P B 0 1 le_rfl (by norm_num) (S i) (S j)).1
  have hX p : MemLp (X p) 2 P := (hprod p.1 p.2).sub (memLp_const _)
  have hmean i j : (∫ w,Z i w*Z j w ∂P)=a i j := by
    simpa only [sub_zero,one_mul,← ha] using
      (brownian_projection_cross P B 0 1 le_rfl (by norm_num) (S i) (S j)).2
  have hcov (p q : Fin d × Fin d) : cov[X p,X q;P]=estimatorLimitCovariance S p q := by
    dsimp only [X]
    rw [covariance_sub_const_left ((hprod p.1 p.2).integrable (by norm_num)),
      covariance_sub_const_right ((hprod q.1 q.2).integrable (by norm_num)),covariance_eq_sub (hprod p.1 p.2) (hprod q.1 q.2)]
    have hfour := (brownian_transformed_mixed_fourth P B ![S p.1,S p.2,S q.1,S q.2] 0 1 le_rfl (by norm_num)).2
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk] at hfour
    change (∫ w,Z p.1 w*Z p.2 w*Z q.1 w*Z q.2 w ∂P)=_ at hfour
    simp only [sub_zero,one_mul,← ha] at hfour
    have he w : (Z p.1 w*Z p.2 w)*(Z q.1 w*Z q.2 w)=Z p.1 w*Z p.2 w*Z q.1 w*Z q.2 w := by ring
    simp only [Pi.mul_apply,he,hfour,hmean,estimatorLimitCovariance]
    change a p.1 p.2*a q.1 q.2+a p.1 q.1*a p.2 q.2+a p.1 q.2*a p.2 q.1-a p.1 p.2*a q.1 q.2=
      a p.1 q.1*a p.2 q.2+a p.1 q.2*a p.2 q.1
    ring
  have he : (Matrix.of fun p q => cov[X p,X q;P])=estimatorLimitCovariance S := by
    ext p q
    exact hcov p q
  rw [← he]
  exact covariance_matrix_posSemidef P X hX

end Asakura.Chapter7
