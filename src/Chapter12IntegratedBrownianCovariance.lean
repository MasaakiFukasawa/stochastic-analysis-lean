import Chapter12CompactPrefixKernel
import Chapter12PrefixTerminalPairing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

noncomputable def integratedBrownianDirection (T : ℝ) (hT : 0≤T) :
    Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) :=
  ∫ t : Icc (0:ℝ) T,finiteTimeIntervalVector T 0 t.val ∂compactTimeMeasure T hT

theorem integrated_brownian_direction_coe (T : ℝ) (hT : 0≤T) :
    (integratedBrownianDirection T hT : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (fun s => T-s) := by
  simpa only [integratedBrownianDirection,one_smul,intervalIntegral.integral_const,
    smul_eq_mul,mul_one] using compact_prefix_L2_kernel T hT (fun _ => 1)
      continuous_const 1 zero_le_one (fun _ _ => by norm_num)

theorem integrated_brownian_direction_inner (T : ℝ) (hT : 0≤T) :
    inner ℝ (integratedBrownianDirection T hT) (integratedBrownianDirection T hT)=T^3/3 := by
  rw [L2.inner_def]
  have he : (fun s => inner ℝ (integratedBrownianDirection T hT s)
      (integratedBrownianDirection T hT s)) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (fun s => (T-s)^2) := by
    filter_upwards [integrated_brownian_direction_coe T hT] with s hs
    rw [hs,Real.inner_apply,pow_two]
  rw [integral_congr_ae he,Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic T ∩ Ioi (0:ℝ)=Ioc 0 T := by ext s; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto
  rw [hs,←intervalIntegral.integral_of_le hT]
  have hp : (fun s : ℝ => (T-s)^2)=(fun s => T^2-(2*T)*s+s^2) := by funext s; ring
  rw [hp,intervalIntegral.integral_add,intervalIntegral.integral_sub,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id,integral_pow]
  · norm_num
    <;> ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integrated_brownian_covariance_determinant (T : ℝ) :
    Matrix.det (!![T,T^2/2;T^2/2,T^3/3] : Matrix (Fin 2) (Fin 2) ℝ)=T^4/12 := by
  rw [Matrix.det_fin_two]
  change T*(T^3/3)-(T^2/2)*(T^2/2)=T^4/12
  ring

end Asakura.Chapter12
