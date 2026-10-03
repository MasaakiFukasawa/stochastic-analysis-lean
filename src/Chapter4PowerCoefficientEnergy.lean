import Chapter4PrefixPowerMoment
import Chapter4IntervalPowerEstimate

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Fubini and the prefix supremum turn a pointwise p-power coefficient
bound into the integral term in Gronwall. -/
theorem coefficient_power_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0≤R) (p : ℝ) (hp : 0<p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hm : Measurable Y) (hi : MemLp Y (ENNReal.ofReal p) P)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H) (K : ℝ) (hK : 0≤K)
    (hb : ∀ w r,r∈Icc 0 R → |H (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p)) :
    Integrable (fun z => |H z|^p) (P.prod (volume.restrict (Ioc (0:ℝ) R))) ∧
    (∫ z,|H z|^p ∂P.prod (volume.restrict (Ioc (0:ℝ) R)))≤
      K*(R+∫ r in 0..R,(∫ w,‖prefixPath hR (Y w) r‖^p ∂P)) := by
  let ν := volume.restrict (Ioc (0:ℝ) R)
  have hYi : Integrable (fun w => ‖Y w‖^p) P := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hi.integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
  have hHp : Measurable (fun z => |H z|^p) := (Real.continuous_rpow_const hp.le).measurable.comp hHm.norm
  have hpoint w r (hr : r∈Icc 0 R) : |H (w,r)|^p≤K*(1+‖Y w‖^p) := by
    apply (hb w r hr).trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply add_le_add le_rfl
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (Y w) (projIcc 0 R hR r)
  have hgood : ∀ᵐ z ∂P.prod ν,z.2∈Icc 0 R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).2
    exact .of_forall (fun w => (ae_restrict_mem measurableSet_Ioc).mono (fun _ h => ⟨h.1.le,h.2⟩))
  have hI : Integrable (fun z => |H z|^p) (P.prod ν) := by
    apply (((integrable_const 1).add hYi).const_mul K).comp_fst ν |>.mono' hHp.aestronglyMeasurable
    filter_upwards [hgood] with z hz
    simpa only [Pi.add_apply,Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hpoint z.1 z.2 hz
  have hprefixi r : Integrable (fun w => ‖prefixPath hR (Y w) r‖^p) P := by
    apply hYi.mono' ((Real.continuous_rpow_const hp.le).measurable.comp (prefix_path_measurable hR Y hm r).norm).aestronglyMeasurable
    exact .of_forall (fun w => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (prefix_path_norm_le hR (Y w) r) hp.le)
  have htime r (hr : r∈Icc 0 R) : (∫ w,|H (w,r)|^p ∂P)≤K*(1+∫ w,‖prefixPath hR (Y w) r‖^p ∂P) := by
    have hHr : Integrable (fun w => |H (w,r)|^p) P := by
      apply (((integrable_const 1).add hYi).const_mul K).mono'
        (hHp.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      exact .of_forall (fun w => by
        simpa only [Pi.add_apply,Function.comp_def,id_eq,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hpoint w r hr)
    calc
      _ ≤ ∫ w,K*(1+‖prefixPath hR (Y w) r‖^p) ∂P := by
        apply integral_mono hHr (((integrable_const 1).add (hprefixi r)).const_mul K)
        intro w
        apply (hb w r hr).trans
        apply mul_le_mul_of_nonneg_left _ hK
        dsimp only [Pi.add_apply]
        apply add_le_add le_rfl
        apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
        have hh := ContinuousMap.norm_coe_le_norm (prefixPath hR (Y w) r) (projIcc 0 R hR r)
        simpa only [prefixPath,ContinuousMap.coe_mk,min_self,Real.norm_eq_abs] using hh
      _ = _ := by rw [integral_const_mul,integral_add (integrable_const 1) (hprefixi r)]; simp
  refine ⟨hI,?_⟩
  rw [integral_prod _ hI,integral_integral_swap hI,← intervalIntegral.integral_of_le hR]
  have hpc := prefix_power_moment_continuous P hR Y hm p hp hi
  calc
    _ ≤ ∫ r in 0..R,K*(1+∫ w,‖prefixPath hR (Y w) r‖^p ∂P) :=
      intervalIntegral.integral_mono_on hR
        ⟨hI.integral_prod_right,by simp [IntegrableOn,Ioc_eq_empty_of_le hR]⟩
        ((continuous_const.mul (continuous_const.add hpc)).intervalIntegrable _ _) htime
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
        (continuous_const.intervalIntegrable _ _) (hpc.intervalIntegrable _ _)]
      simp

end Asakura.Chapter4
