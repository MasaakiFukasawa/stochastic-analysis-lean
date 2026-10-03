import Chapter7GaussianMatrixLinearLaw
import Chapter7DistributionLawTransfer
import Chapter7BrownianMatrixContraction

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter7
open Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem brownian_matrix_scalar_clt {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (Baux : BrownianSystem Q 1)
    (H S : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose=H)
    (T : ℝ) (hT : 0<T) :
    TendstoInDistribution (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*
      (∑ i,∑ j,H i j*(realizedCovarianceEntry B (S i) (S j) T (n+1) w-(S*S.transpose) i j))) atTop
      (fun g : EuclideanSpace ℝ (Fin d × Fin d) => ∑ i,∑ j,H i j*g (i,j))
      (fun _ => P) (estimatorGaussianLaw S) := by
  let K := S.transpose*H*S
  let q := ∑ i,∑ j,(K i j)^2
  have hq : 0≤q := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  have hKs : ∀ i j,K i j=K j i := by
    have he : K.transpose=K := by simp only [K,Matrix.transpose_mul,Matrix.transpose_transpose,hH,Matrix.mul_assoc]
    intro i j
    exact (congrFun (congrFun he i) j).symm
  have hG := gaussian_matrix_linear_law P B H S hH
  have hlim : TendstoInDistribution (fun n => brownianQuadraticStatistic B K T (n+1)) atTop
      (fun g : EuclideanSpace ℝ (Fin d × Fin d) => ∑ i,∑ j,H i j*g (i,j))
      (fun _ => P) (estimatorGaussianLaw S) := by
    rcases eq_or_lt_of_le hq with hz|hp
    · have hd := brownian_quadratic_statistic_degenerate_clt P B K hz.symm T
      have hzero : HasLaw (fun _ : Ω => (0:ℝ)) (gaussianReal 0 (2*q).toNNReal) P := by
        refine ⟨measurable_const.aemeasurable,?_⟩
        simp [← hz,gaussianReal_zero_var,Measure.map_const]
      exact distribution_limit_same_law P P (estimatorGaussianLaw S) hd hzero hG
    · obtain ⟨B0,hd⟩ := brownian_quadratic_statistic_clt P Q B Baux K hKs T hT hp
      have hl := scaled_brownian_gaussian_law (P.prod Q) B0 (2*q/T) T
        (div_nonneg (mul_nonneg (by norm_num) hq) hT.le) hT.le
      have hv : (⟨2*q/T*T,mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hq) hT.le) hT.le⟩ : ℝ≥0)=
          (2*q).toNNReal := by
        apply NNReal.eq
        rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hq)]
        exact div_mul_cancel₀ _ hT.ne'
      rw [hv] at hl
      exact distribution_limit_same_law P (P.prod Q) (estimatorGaussianLaw S) hd hl hG
  apply hlim.congr _ (ae_of_all _ (fun _ => rfl))
  intro n
  exact ae_of_all _ (fun w => (brownian_matrix_contraction B H S T hT (n+1) (Nat.succ_pos _) w).symm)

end Asakura.Chapter7
