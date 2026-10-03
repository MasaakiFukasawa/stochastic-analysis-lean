import Chapter4VolterraPathLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma prefix_integral_le_full_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℝ) (hR : 0≤R) (Y : Ω → C(Icc (0:ℝ) R,ℝ))
    (hm : Measurable Y) (hi : MemLp Y 2 P) :
    (∫ r in 0..R,(∫ w,‖prefixPath hR (Y w) r‖^2 ∂P))≤R*(∫ w,‖Y w‖^2 ∂P) := by
  have hn := hi.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := prefix_square_moment_continuous P hR Y hm hi
  have hb r : (∫ w,‖prefixPath hR (Y w) r‖^2 ∂P)≤∫ w,‖Y w‖^2 ∂P := by
    have hi' : Integrable (fun w => ‖prefixPath hR (Y w) r‖^2) P := by
      apply hn.mono' ((prefix_path_measurable hR Y hm r).norm.pow_const 2).aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro w
      simpa only [Real.norm_eq_abs,abs_sq] using
        (pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hR (Y w) r) 2)
    exact integral_mono hi' hn (fun w => pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hR (Y w) r) 2)
  have h := intervalIntegral.integral_mono_on (μ := volume) hR (hc.intervalIntegrable 0 R)
    (intervalIntegrable_const) (fun r _ => hb r)
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using h

lemma ae_eq_of_two_L2_limits
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : ℕ → Ω → E) (Y V : Ω → E)
    (hY : Tendsto (fun n => eLpNorm (fun w => Y w-X n w) 2 P) atTop (𝓝 0))
    (hV : Tendsto (fun n => eLpNorm (fun w => X n w-V w) 2 P) atTop (𝓝 0)) :
    Y=ᵐ[P] V := by
  have hb n : eLpNorm (fun w => Y w-V w) 2 P≤
      eLpNorm (fun w => Y w-X n w) 2 P+eLpNorm (fun w => X n w-V w) 2 P := by
    have he : (fun w => Y w-V w)=(fun w => (Y w-X n w)+(X n w-V w)) := by funext w; abel
    rw [he]
    exact eLpNorm_add_le (by norm_num)
  have hz : eLpNorm (fun w => Y w-V w) 2 P=0 := by
    apply le_antisymm _ bot_le
    change eLpNorm (fun w => Y w-V w) 2 P≤(0:ℝ≥0∞)
    exact ge_of_tendsto (by simpa only [add_zero] using hY.add hV) (.of_forall hb)
  have he := (eLpNorm_eq_zero_iff (by norm_num : (2:ℝ≥0∞)≠0)).1 hz
  filter_upwards [he] with w hw
  exact sub_eq_zero.mp hw

end Asakura.Chapter4
