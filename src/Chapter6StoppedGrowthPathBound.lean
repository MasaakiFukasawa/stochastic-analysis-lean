import Chapter6AdditiveGrowthPathBound
import Chapter6BrownianEnvelopeBound

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 3200000

lemma euclidean_norm_le_abs_sum {d : ℕ} (x : Fin d → ℝ) :
    ‖WithLp.toLp 2 x‖≤∑ j,|x j| := by
  have hh := sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (x j))
  have hs : ‖WithLp.toLp 2 x‖^2≤(∑ j,|x j|)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [sq_abs] using hh
  nlinarith [norm_nonneg (WithLp.toLp 2 x),sum_nonneg (fun j (_ : j∈Finset.univ) => abs_nonneg (x j))]

/-- Gronwall for the actual stopped drift identity, with a constant
independent of the exit level or the stopping time. -/
theorem stopped_vector_growth_path_bound {d : ℕ}
    (Y V H : ℝ → Fin d → ℝ) (R u K G : ℝ)
    (hR : 0≤R) (hu : u∈Icc 0 R) (hK : 0≤K) (hG : 0≤G)
    (hY : ContinuousOn Y (Icc 0 R)) (hH : ContinuousOn H (Icc 0 R))
    (hHb : ∀ r,r∈Icc 0 R → ‖WithLp.toLp 2 (H r)‖≤K*(1+‖WithLp.toLp 2 (Y r)‖))
    (hVb : ∀ r,r∈Icc 0 R → ‖WithLp.toLp 2 (V r)‖≤G)
    (he : ∀ r,r∈Icc 0 R → ∀ j,Y r j=V r j+∫ s in 0..min u r,H s j) :
    ∀ r,r∈Icc 0 R → ‖WithLp.toLp 2 (Y r)‖≤((d:ℝ)*K*R+G)*Real.exp (((d:ℝ)*K+1)*R) := by
  let f := fun r => ‖WithLp.toLp 2 (Y r)‖
  have hfc : ContinuousOn f (Icc 0 R) :=
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin d => ℝ)).symm.continuous.comp_continuousOn hY).norm)
  have hD : 0≤(d:ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  have hineq r (hr : r∈Icc 0 R) : f r≤((d:ℝ)*K*R+G)+((d:ℝ)*K+1)*(∫ s in 0..r,f s) := by
    have hv : 0≤min u r := le_min hu.1 hr.1
    have hmr : min u r≤r := min_le_right _ _
    have hmc : min u r≤R := hmr.trans hr.2
    have hfi : IntervalIntegrable f volume 0 r := (hfc.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1
    have hgi : IntervalIntegrable (fun s => K*(1+f s)) volume 0 r :=
      (intervalIntegrable_const.add hfi).const_mul K
    have hJi j : IntervalIntegrable (fun s => H s j) volume 0 (min u r) :=
      ((continuous_apply j).comp_continuousOn (hH.mono (Icc_subset_Icc_right hmc))).intervalIntegrable_of_Icc hv
    have hb j : |∫ s in 0..min u r,H s j|≤K*r+K*(∫ s in 0..r,f s) := by
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hv (f := fun s => H s j)
      have h2 := intervalIntegral.integral_mono_on hv (hJi j).norm
        (hgi.mono_set (by simpa only [uIcc_of_le hv,uIcc_of_le hr.1] using Icc_subset_Icc_right hmr))
        (fun s hs => (PiLp.norm_apply_le (WithLp.toLp 2 (H s)) j).trans (hHb s ⟨hs.1,hs.2.trans hmc⟩))
      have h3 : (∫ s in 0..min u r,K*(1+f s))≤∫ s in 0..r,K*(1+f s) :=
        intervalIntegral.integral_mono_interval le_rfl hv hmr
          (ae_of_all _ (fun s => mul_nonneg hK (by dsimp [f]; positivity))) hgi
      have h4 : (∫ s in 0..r,K*(1+f s))=K*r+K*(∫ s in 0..r,f s) := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const hfi]
        simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,mul_add]
      simpa only [Real.norm_eq_abs,h4] using h1.trans (h2.trans h3)
    have heq : WithLp.toLp 2 (Y r)=WithLp.toLp 2 (V r)+WithLp.toLp 2 (fun j => ∫ s in 0..min u r,H s j) := by
      apply WithLp.ofLp_injective
      funext j
      exact he r hr j
    have hn : f r≤G+(d:ℝ)*(K*r+K*(∫ s in 0..r,f s)) := by
      change ‖WithLp.toLp 2 (Y r)‖≤_
      rw [heq]
      apply (norm_add_le _ _).trans
      apply add_le_add (hVb r hr)
      exact (euclidean_norm_le_abs_sum _).trans (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using sum_le_sum (fun j (_ : j∈Finset.univ) => hb j))
    have hpos := intervalIntegral.integral_nonneg (μ := volume) hr.1 (fun s _ => (norm_nonneg (WithLp.toLp 2 (Y s))))
    nlinarith [mul_le_mul_of_nonneg_left hr.2 hD]
  have hg := Asakura.FullAudit.ch4_gronwall_written f ((d:ℝ)*K*R+G) ((d:ℝ)*K+1) R hR hfc (by linarith) hineq
  intro r hr
  exact (hg r hr).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2 (by linarith))) (by positivity))

end Asakura.Chapter6
