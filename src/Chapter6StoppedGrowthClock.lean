import Chapter6ContinuousVectorCovariance
import Chapter6BrownianLevelStops

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual quadratic variation is bounded at the state exit time. -/
theorem linear_growth_stopped_clock_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (W : Fin d → HalfClosedTime → Ω → ℝ)
    (H : Fin d → Ω × ℝ → ℝ) (hHc : ∀ j w,Continuous (fun r => H j (w,r)))
    (C : HalfClosedTime → Ω → ℝ) (R : ℝ) (hR : 0≤R)
    (hCe : ∀ᵐ w ∂P,∀ r∈Icc 0 R,C (realTimeClamp r) w=∫ s in 0..r,∑ j,(H j (w,s))^2)
    (K level : ℝ) (hK : 0≤K) (hl : 0≤level)
    (hHb : ∀ w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H j (w,r))‖≤K*(1+‖WithLp.toLp 2 (fun j => W j (realTimeClamp r) w)‖))
    (τ : Ω → HalfClosedTime) (hτR : ∀ w,τ w≤realTimeClamp R)
    (hstop : ∀ᵐ w ∂P,∀ (r : ℝ),0≤r → realTimeClamp r≤τ w → ‖WithLp.toLp 2 (fun j => W j (realTimeClamp r) w)‖≤level) :
    ∀ᵐ w ∂P,|C (τ w) w|≤K^2*(1+level)^2*R := by
  filter_upwards [hCe,hstop] with w hc hs
  let u := (finitePrefixTime R hR (τ w)).val
  have hu : u∈Icc 0 R := (finitePrefixTime R hR (τ w)).property
  have heu : realTimeClamp u=τ w := by
    dsimp [u]
    rw [finite_prefix_time_clamp R hR (le_top : (R:EReal)≤⊤),min_eq_right (hτR w)]
  have hcu : C (τ w) w=∫ s in 0..u,∑ j,(H j (w,s))^2 := by rw [←heu]; exact hc u hu
  rw [hcu,abs_of_nonneg (intervalIntegral.integral_nonneg hu.1 (fun s _ => sum_nonneg (fun j _ => sq_nonneg _)))]
  have hi : IntervalIntegrable (fun s => ∑ j,(H j (w,s))^2) volume 0 u :=
    (continuous_finsetSum _ (fun j _ => (hHc j w).pow 2)).continuousOn.intervalIntegrable_of_Icc hu.1
  calc
    _ ≤ ∫ s in 0..u,K^2*(1+level)^2 := by
      apply intervalIntegral.integral_mono_on hu.1 hi intervalIntegrable_const
      intro s hsu
      have hsr : s∈Icc 0 R := ⟨hsu.1,hsu.2.trans hu.2⟩
      have hn : ‖WithLp.toLp 2 (fun j => H j (w,s))‖≤K*(1+level) := (hHb w s hsr).trans (mul_le_mul_of_nonneg_left
        (by linarith [hs s hsu.1 ((real_time_clamp_mono hsu.2).trans_eq heu)]) hK)
      have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
      simpa only [EuclideanSpace.real_norm_sq_eq,mul_pow] using hh
    _ = K^2*(1+level)^2*u := by simp [mul_comm,mul_assoc]
    _ ≤ K^2*(1+level)^2*R := mul_le_mul_of_nonneg_left hu.2 (by positivity)

end Asakura.Chapter6
