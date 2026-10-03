import FullAuditTimeAverageAE

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem integrated_exponential_decay (κ T : ℝ) (hκ : 0 < κ) :
    (∫ t in (0:ℝ)..T, Real.exp (-κ*t)) = (1-Real.exp (-κ*T))/κ := by
  let F := fun t => -Real.exp (-κ*t)/κ
  have hd (t : ℝ) : HasDerivAt F (Real.exp (-κ*t)) t := by
    have h := ((((hasDerivAt_id t).const_mul (-κ)).exp).neg).div_const κ
    convert h using 1
    · rfl
    · simp only [id_eq]
      field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-κ*t))).intervalIntegrable 0 T)]
  simp only [F,mul_zero,Real.exp_zero]
  ring

/-- Removing the initial transient by the integrated exponential coupling. -/
theorem time_average_coupling_bound (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (C κ T : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ) (hT : 0 < T)
    (hcomp : ∀ t ∈ Icc 0 T, |f t-g t| ≤ C*Real.exp (-κ*t)) :
    |timeAverage f T-timeAverage g T| ≤ C/(κ*T) := by
  have hi : |∫ t in (0:ℝ)..T,f t-g t| ≤ C/κ := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun t => f t-g t)
      (g := fun t => C*Real.exp (-κ*t)) hT.le
      (ae_of_all _ (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hcomp t ⟨ht.1.le,ht.2⟩))
      ((by fun_prop : Continuous (fun t : ℝ => C*Real.exp (-κ*t))).intervalIntegrable 0 T)
    rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul,integrated_exponential_decay κ T hκ] at h
    apply h.trans
    have hh : 1-Real.exp (-κ*T) ≤ 1 := by linarith [Real.exp_pos (-κ*T)]
    have hh' := mul_le_mul_of_nonneg_left hh hC
    apply (le_div_iff₀ hκ).mpr
    convert hh' using 1 <;> field_simp
  have he : timeAverage f T-timeAverage g T = T⁻¹*(∫ t in (0:ℝ)..T,f t-g t) := by
    rw [timeAverage,timeAverage,intervalIntegral.integral_sub (hf.intervalIntegrable 0 T) (hg.intervalIntegrable 0 T)]
    ring
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hT)]
  have h := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hT.le)
  convert h using 1 <;> ring

theorem time_average_coupling_transfer (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (C κ l : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hcomp : ∀ t ≥ 0, |f t-g t| ≤ C*Real.exp (-κ*t))
    (hlim : Tendsto (timeAverage g) atTop (nhds l)) :
    Tendsto (timeAverage f) atTop (nhds l) := by
  have hs : Tendsto (fun T : ℝ => C/(κ*T)) atTop (nhds 0) := by
    have h : Tendsto (fun T : ℝ => (C/κ)/T) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa only [div_div] using h
  have hd : Tendsto (fun T => timeAverage f T-timeAverage g T) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hs
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    simpa only [Real.norm_eq_abs] using time_average_coupling_bound f g hf hg C κ T hC hκ hT
      (fun t ht => hcomp t ht.1)
  simpa only [sub_add_cancel,zero_add] using hd.add hlim

end Asakura.FullAudit
