import Chapter5CoordinateGenerator

open Set
open scoped BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The drift and covariance generator transforms by the ordinary chain
rule. This connects the space-time heat equation to finite-coordinate Ito. -/
theorem linear_generator_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d n : ℕ} (g : E → ℝ) (hg : ContDiff ℝ 2 g)
    (L : (Fin d → ℝ) →L[ℝ] E) (x B : Fin d → ℝ) (Q : Fin n → Fin d → ℝ)
    (hz : fderiv ℝ g (L x) (L B)+(1/2:ℝ)*∑ k,
      fderiv ℝ (fderiv ℝ g) (L x) (L (Q k)) (L (Q k))=0) :
    (∑ i,fderiv ℝ (fun y => g (L y)) x (Pi.single i 1)*B i)+
      (∑ i,∑ j,fderiv ℝ (fderiv ℝ (fun y => g (L y))) x (Pi.single i 1) (Pi.single j 1)*
        (∑ k,Q k i*Q k j))/2=0 := by
  have hd := ((hg.differentiable (by norm_num)).differentiableAt (x := L x)).hasFDerivAt.comp x L.hasFDerivAt
  dsimp only [Function.comp_def] at hd
  have hfirst : (∑ i,fderiv ℝ (fun y => g (L y)) x (Pi.single i 1)*B i)=
      fderiv ℝ g (L x) (L B) := by
    rw [hd.fderiv]
    change (∑ i,((fderiv ℝ g (L x)).comp L) (Pi.single i 1)*B i)=((fderiv ℝ g (L x)).comp L) B
    conv_rhs => rw [pi_eq_sum_univ' B]
    simp only [map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond k : fderiv ℝ (fderiv ℝ (fun y => g (L y))) x (Q k) (Q k)=
      fderiv ℝ (fderiv ℝ g) (L x) (L (Q k)) (L (Q k)) := by
    simpa only [zero_add] using affine_restriction_hessian g hg L 0 x (Q k) (Q k)
  rw [hfirst,covariance_matrix_hessian_trace]
  simp_rw [hsecond]
  linarith

end Asakura.Chapter5
