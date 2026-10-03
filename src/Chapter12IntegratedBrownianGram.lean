import Chapter12IntegratedBrownianCovariance

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

theorem integrated_brownian_cross_inner (T : ℝ) (hT : 0≤T) :
    inner ℝ (finiteTimeIntervalVector T 0 T) (integratedBrownianDirection T hT)=T^2/2 := by
  rw [L2.inner_def]
  have ht : (finiteTimeIntervalVector T 0 T : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (fun _ => 1) := by
    have hh : (finiteTimeIntervalVector T 0 T : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
        (Ioc 0 T).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
    have hs : Iic T ∩ Ioi (0:ℝ)=Ioc 0 T := by ext s; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto
    have hmem : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))).restrict (Iic T),s∈Ioc 0 T := by
      rw [Measure.restrict_restrict measurableSet_Iic,hs]
      exact ae_restrict_mem measurableSet_Ioc
    filter_upwards [hh,hmem] with s hh hm
    rw [hh,indicator_of_mem hm]
  have he : (fun s => inner ℝ (finiteTimeIntervalVector T 0 T s)
      (integratedBrownianDirection T hT s)) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (fun s => T-s) := by
    filter_upwards [ht,integrated_brownian_direction_coe T hT] with s hs hg
    rw [hs,hg,Real.inner_apply,one_mul]
  rw [integral_congr_ae he,Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic T ∩ Ioi (0:ℝ)=Ioc 0 T := by ext s; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto
  rw [hs,←intervalIntegral.integral_of_le hT,intervalIntegral.integral_sub,
    intervalIntegral.integral_const,integral_id]
  · simp only [sub_zero,zero_pow,smul_eq_mul]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integrated_brownian_gram_matrix (T : ℝ) (hT : 0≤T) :
    let v : Fin 2 → Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) :=
      ![finiteTimeIntervalVector T 0 T,integratedBrownianDirection T hT]
    (fun i j => inner ℝ (v i) (v j))=(!![T,T^2/2;T^2/2,T^3/3] : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp only
  funext i j
  fin_cases i <;> fin_cases j
  · exact finite_prefix_terminal_inner T T hT le_rfl
  · exact integrated_brownian_cross_inner T hT
  · change inner ℝ (integratedBrownianDirection T hT) (finiteTimeIntervalVector T 0 T)=T^2/2
    rw [real_inner_comm]
    exact integrated_brownian_cross_inner T hT
  · exact integrated_brownian_direction_inner T hT

theorem integrated_brownian_gram_positive_determinant (T : ℝ) (hT : 0<T) :
    let v : Fin 2 → Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) :=
      ![finiteTimeIntervalVector T 0 T,integratedBrownianDirection T hT.le]
    0<Matrix.det (fun i j => inner ℝ (v i) (v j)) := by
  dsimp only
  rw [integrated_brownian_gram_matrix T hT.le,integrated_brownian_covariance_determinant]
  positivity

end Asakura.Chapter12
