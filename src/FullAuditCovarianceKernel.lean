import FullAuditTimeAverageVariance

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Split the square at its diagonal and translate the two interval integrals. -/
theorem covariance_kernel_inner (c : ℝ → ℝ) (hc : Continuous c)
    (T s : ℝ) (hs : s ∈ Icc 0 T) :
    (∫ t in (0:ℝ)..T,c |t-s|) =
      (∫ u in (0:ℝ)..s,c u)+(∫ u in (0:ℝ)..(T-s),c u) := by
  have hi : Continuous (fun t : ℝ => c |t-s|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable 0 s) (hi.intervalIntegrable s T)]
  congr 1
  · have he : (∫ t in (0:ℝ)..s,c |t-s|) = ∫ t in (0:ℝ)..s,c (s-t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs.1] at ht
      dsimp only
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2),neg_sub]
    rw [he,intervalIntegral.integral_comp_sub_left]
    simp
  · have he : (∫ t in s..T,c |t-s|) = ∫ t in s..T,c (t-s) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs.2] at ht
      dsimp only
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    rw [he,intervalIntegral.integral_comp_sub_right]
    simp

/-- The triangular weight T-u follows by an ordinary integration by parts. -/
theorem covariance_kernel_primitive (c : ℝ → ℝ) (hc : Continuous c) (T : ℝ) :
    (∫ s in (0:ℝ)..T,(∫ u in (0:ℝ)..s,c u)) =
      ∫ u in (0:ℝ)..T,(T-u)*c u := by
  let F := fun s => ∫ u in (0:ℝ)..s,c u
  have hd (s : ℝ) : HasDerivAt F (c s) s := (hc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  have hder (s : ℝ) : HasDerivAt (fun u => (T-u)*F u) (-F s+(T-s)*c s) s := by
    have hx := ((hasDerivAt_id s).const_sub T).mul (hd s)
    change HasDerivAt (fun u => (T-u)*F u) ((-1)*F s+(T-s)*c s) s at hx
    convert hx using 1 <;> ring
  have hi : IntervalIntegrable (fun s => -F s+(T-s)*c s) volume 0 T :=
    (hF.neg.add ((continuous_const.sub continuous_id).mul hc)).intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s) hi
  have hz : F 0 = 0 := by simp [F]
  rw [intervalIntegral.integral_add (f := fun s => -F s) (g := fun s => (T-s)*c s) (hF.neg.intervalIntegrable 0 T)
    (((continuous_const.sub continuous_id).mul hc).intervalIntegrable 0 T),
    intervalIntegral.integral_neg,hz,sub_self,zero_mul,mul_zero,sub_zero] at h
  change (∫ s in (0:ℝ)..T,F s) = _
  linarith

/-- The exact double-integral identity printed in the stationary variance proof. -/
theorem covariance_kernel_square (c : ℝ → ℝ) (hc : Continuous c) (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in (0:ℝ)..T,(∫ t in (0:ℝ)..T,c |t-s|)) =
      2*(∫ u in (0:ℝ)..T,(T-u)*c u) := by
  let F := fun s => ∫ u in (0:ℝ)..s,c u
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun s =>
    (hc.integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt)
  have he : (∫ s in (0:ℝ)..T,(∫ t in (0:ℝ)..T,c |t-s|)) =
      ∫ s in (0:ℝ)..T,F s+F (T-s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    exact covariance_kernel_inner c hc T s hs
  rw [he,intervalIntegral.integral_add (f := F) (g := fun s => F (T-s)) (hF.intervalIntegrable 0 T)
    ((hF.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 T),
    intervalIntegral.integral_comp_sub_left,sub_self,sub_zero]
  change (∫ s in (0:ℝ)..T,(∫ u in (0:ℝ)..s,c u)) + _ = _
  rw [covariance_kernel_primitive c hc T]
  ring

end Asakura.FullAudit
