import Chapter4CoefficientPointMoment
import Chapter4EulerEstimates
import Chapter4PathEvaluationMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma coefficient_split_square_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {dim : ℕ}
    (b : (Fin dim → ℝ) → ℝ) (L : ℝ) (hL : 0≤L)
    (hb : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (X Y Z : Ω → Fin dim → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    (∫ w,(b (X w)-b (Z w))^2 ∂P)≤
      2*L*((∫ w,‖X w-Y w‖^2 ∂P)+(∫ w,‖Y w-Z w‖^2 ∂P)) := by
  have hbi := (square_lipschitz_coefficient_memLp P b L hL hb X hX).sub
    (square_lipschitz_coefficient_memLp P b L hL hb Z hZ)
  have hi₁ := (hX.sub hY).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₂ := (hY.sub hZ).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  change Integrable (fun w => ‖X w-Y w‖^2) P at hi₁
  change Integrable (fun w => ‖Y w-Z w‖^2) P at hi₂
  have hpt w : (b (X w)-b (Z w))^2≤2*L*(‖X w-Y w‖^2+‖Y w-Z w‖^2) := by
    have hh := mul_le_mul_of_nonneg_left (split_error_sq (X w) (Y w) (Z w)) hL
    nlinarith only [hb (X w) (Z w),hh]
  have hm := integral_mono ((memLp_two_iff_integrable_sq hbi.aestronglyMeasurable).1 hbi)
    ((hi₁.add hi₂).const_mul (2*L)) hpt
  simpa only [Pi.sub_apply,Pi.add_apply,integral_const_mul,integral_add hi₁ hi₂] using hm

lemma coefficient_prefix_split_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {dim : ℕ}
    (R : ℝ) (hR : 0≤R) (b : (Fin dim → ℝ) → ℝ) (L : ℝ) (hL : 0≤L)
    (hb : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (X V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hXm : Measurable X) (hVm : Measurable V) (hXi : MemLp X 2 P) (hVi : MemLp V 2 P)
    (Z : Ω → Fin dim → ℝ) (hZi : MemLp Z 2 P)
    (r : Icc (0:ℝ) R) (B : ℝ) (hB : (∫ w,‖V w r-Z w‖^2 ∂P)≤B) :
    (∫ w,(b (X w r)-b (Z w))^2 ∂P)≤
      2*L*((∫ w,‖Vector.prefixPath hR (X w-V w) r.val‖^2 ∂P)+B) := by
  have hiX := random_path_evaluation_memLp P X hXm hXi r
  have hiV := random_path_evaluation_memLp P V hVm hVi r
  have hh := coefficient_split_square_moment P b L hL hb (fun w => X w r) (fun w => V w r) Z hiX hiV hZi
  have hpre : MemLp (fun w => Vector.prefixPath hR (X w-V w) r.val) 2 P := by
    apply (hXi.sub hVi).norm.mono' (Vector.prefix_path_measurable hR (fun w => X w-V w) (hXm.sub hVm) r.val).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun w => Vector.prefix_path_norm_le hR (X w-V w) r.val)
  have hp : (∫ w,‖X w r-V w r‖^2 ∂P)≤∫ w,‖Vector.prefixPath hR (X w-V w) r.val‖^2 ∂P := by
    apply integral_mono ((hiX.sub hiV).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (hpre.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    intro w
    simpa only [projIcc_of_mem hR r.property,ContinuousMap.sub_apply,Pi.sub_apply] using
      Vector.evaluation_le_prefix_square hR (X w-V w) r.val
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hp hB) (by positivity))

end Asakura.Chapter4
