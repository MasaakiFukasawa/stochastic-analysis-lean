import FullAuditChapter4Gronwall

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2600000

/-- A pathwise Gronwall estimate for additive noise. Its constant is
independent of a stopping level in the drift. -/
theorem additive_growth_path_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y U W : ℝ → E) (x : E) (R K G : ℝ) (hR : 0≤R) (hK : 0≤K) (hG : 0≤G)
    (hY : ContinuousOn Y (Icc 0 R)) (hUi : IntervalIntegrable U volume 0 R)
    (hUb : ∀ r,r∈Icc 0 R → ‖U r‖≤K*(1+‖Y r‖))
    (hWb : ∀ r,r∈Icc 0 R → ‖W r‖≤G)
    (he : ∀ r,r∈Icc 0 R → Y r=x+(∫ s in 0..r,U s)+W r) :
    ∀ r,r∈Icc 0 R → ‖Y r‖≤(‖x‖+K*R+G)*Real.exp ((K+1)*R) := by
  have hun : ContinuousOn (fun r => ‖Y r‖) (Icc 0 R) := hY.norm
  have hi (r : ℝ) (hr : r∈Icc 0 R) : IntervalIntegrable (fun s => ‖Y s‖) volume 0 r :=
    (hun.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1
  have hineq r (hr : r∈Icc 0 R) : ‖Y r‖≤(‖x‖+K*R+G)+(K+1)*(∫ s in 0..r,‖Y s‖) := by
    have hUr : IntervalIntegrable U volume 0 r := hUi.mono_set (by simpa [uIcc_of_le hr.1,uIcc_of_le hR] using Icc_subset_Icc_right hr.2)
    have hInt : ‖∫ s in 0..r,U s‖≤K*r+K*(∫ s in 0..r,‖Y s‖) := by
      apply (intervalIntegral.norm_integral_le_integral_norm hr.1).trans
      have hm := intervalIntegral.integral_mono_on hr.1 hUr.norm
        (((intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 r).add (hi r hr)).const_mul K)
        (fun s hs => hUb s ⟨hs.1,hs.2.trans hr.2⟩)
      change (∫ s in 0..r,‖U s‖)≤∫ s in 0..r,K*(1+‖Y s‖) at hm
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const (hi r hr)] at hm
      simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,mul_add] using hm
    have hnonneg : 0≤∫ s in 0..r,‖Y s‖ := intervalIntegral.integral_nonneg hr.1 (fun _ _ => norm_nonneg _)
    have htri : ‖Y r‖≤‖x‖+‖∫ s in 0..r,U s‖+G := by
      rw [he r hr]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (hWb r hr))
    nlinarith [mul_le_mul_of_nonneg_left hr.2 hK]
  have hg := Asakura.FullAudit.ch4_gronwall_written (fun r => ‖Y r‖) (‖x‖+K*R+G) (K+1) R hR hun (by linarith) hineq
  intro r hr
  exact (hg r hr).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2 (by linarith))) (by positivity))

end Asakura.Chapter6
