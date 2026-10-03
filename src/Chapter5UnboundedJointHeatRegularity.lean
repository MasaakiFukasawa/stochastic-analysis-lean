import Chapter5LinearFamilyAverage
import FullAuditGaussianGrowth
import Mathlib.Analysis.Normed.Operator.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The full joint regularity needed for Ito, proved by first averaging
f(x+s z) and then composing with s=sqrt(t) for t>0. -/
theorem joint_heat_average_C2_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : MemLp (fun z : E => z) 2 ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (p : E × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 2 (fun q : E × ℝ => ∫ z,f (q.1+Real.sqrt q.2 • z) ∂ν) p := by
  let L := fun z : E => (ContinuousLinearMap.fst ℝ E ℝ)+((ContinuousLinearMap.snd ℝ E ℝ).smulRight z)
  have hLc : Continuous L := by dsimp only [L]; fun_prop
  have hLb z : ‖L z‖ ≤ 1+‖z‖ := by
    calc
      _ ≤ ‖ContinuousLinearMap.fst ℝ E ℝ‖+‖(ContinuousLinearMap.snd ℝ E ℝ).smulRight z‖ := norm_add_le _ _
      _ = ‖ContinuousLinearMap.fst ℝ E ℝ‖+‖ContinuousLinearMap.snd ℝ E ℝ‖*‖z‖ := by rw [ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1+1*‖z‖ := add_le_add (ContinuousLinearMap.norm_fst_le ..)
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ..) (norm_nonneg z))
      _ = _ := by ring
  have hb : MemLp (fun z : E => 1+‖z‖) 2 ν := (memLp_const (1:ℝ)).add hi.norm
  have hb2 : Integrable (fun z : E => (1+‖z‖)^2) ν :=
    (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_fderiv_le
    (fun y => (hd y).differentiableAt) (fun y => by
      rw [(hd y).fderiv]
      exact_mod_cast hD y)
  have hFi (q : E × ℝ) : Integrable (fun z => f (L z q)) ν := by
    apply ((integrable_const ‖f 0‖).add ((hb.integrable (by norm_num)).const_mul ((C:ℝ)*‖q‖))).mono'
      (hl.continuous.comp (hLc.clm_apply continuous_const)).aestronglyMeasurable
    apply ae_of_all
    intro z
    change ‖f (L z q)‖ ≤ ‖f 0‖+(C:ℝ)*‖q‖*(1+‖z‖)
    have hh := hl.dist_le_mul (L z q) 0
    simp only [dist_eq_norm,sub_zero] at hh
    calc
      _ ≤ ‖f 0‖+‖f (L z q)-f 0‖ := by
        simpa only [add_sub_cancel] using norm_add_le (f 0) (f (L z q)-f 0)
      _ ≤ ‖f 0‖+(C:ℝ)*‖L z q‖ := by simpa only [Real.norm_eq_abs] using add_le_add_right hh ‖f 0‖
      _ ≤ ‖f 0‖+(C:ℝ)*((1+‖z‖)*‖q‖) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hLb z) (norm_nonneg q))) C.coe_nonneg)
      _ = _ := by ring
  have hA := linear_family_average_C2_of_integrable ν L hLc (fun z => 1+‖z‖) hLb
    (hb.integrable (by norm_num)) hb2 f D DD hd hdd hDc hDDc C K hD hDD hFi
  have hmap : ContDiffAt ℝ 2 (fun q : E × ℝ => (q.1,Real.sqrt q.2)) p :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sqrt hp.ne')
  simpa only [Function.comp_def,L,add_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.coe_snd'] using
    hA.contDiffAt.comp p hmap

end Asakura.Chapter5
