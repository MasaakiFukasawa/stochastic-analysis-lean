import Chapter7BrownianClockVariance

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

lemma brownian_cell_clock_error_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T t : ℝ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (n : ℕ) :
    (∫ w,(brownianCellClock B u T t (n+1) w-(2*(∑ j,u j^2)/T)*t)^2 ∂P) ≤
      32*(∑ j,u j^2)^2/((n:ℝ)+1)+4*(∑ j,u j^2)^2/((n:ℝ)+1)^2 := by
  let q := ∑ j,u j^2
  let c := (2*q/T)*t
  have hq : 0 ≤ q := sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := brownian_cell_clock_mean P B u T t (n+1) hT ht0 htT (Nat.succ_pos _)
  have hv := brownian_cell_clock_variance P B u T t (n+1) hT ht0 htT (Nat.succ_pos _)
  rw [mean_square_from_bias_variance P _ hm.1 c]
  have hb : ((∫ w,brownianCellClock B u T t (n+1) w ∂P)-c)^2 ≤ (2*q/((n+1:ℕ):ℝ))^2 := by
    have he := (sq_le_sq₀ (abs_nonneg ((∫ w,brownianCellClock B u T t (n+1) w ∂P)-c))
      (div_nonneg (mul_nonneg (by norm_num) hq) (Nat.cast_nonneg _))).mpr hm.2
    simpa only [sq_abs] using he
  have he : (2*q/((n+1:ℕ):ℝ))^2=4*q^2/((n:ℝ)+1)^2 := by push_cast; rw [div_pow]; ring
  rw [he] at hb
  simp only [Nat.cast_add,Nat.cast_one] at hv
  exact add_le_add hv hb

/-- Each projected-square clock converges from its actual Brownian block
integrals; no moment or independence condition on the blocks is assumed. -/
theorem brownian_cell_clock_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T t : ℝ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) :
    TendstoInMeasure P (fun n => brownianCellClock B u T t (n+1)) atTop
      (fun _ => (2*(∑ j,u j^2)/T)*t) := by
  let q := ∑ j,u j^2
  let c := (2*q/T)*t
  have hq : 0 ≤ q := sum_nonneg (fun _ _ => sq_nonneg _)
  apply mean_square_rate_probability P _ c (32*q^2) (4*q^2)
  · intro n
    exact (brownian_cell_clock_mean P B u T t (n+1) hT ht0 htT (Nat.succ_pos _)).1.sub (memLp_const c)
  · intro n
    have hm := brownian_cell_clock_mean P B u T t (n+1) hT ht0 htT (Nat.succ_pos _)
    have hv := brownian_cell_clock_variance P B u T t (n+1) hT ht0 htT (Nat.succ_pos _)
    rw [mean_square_from_bias_variance P _ hm.1 c]
    have hb : ((∫ w,brownianCellClock B u T t (n+1) w ∂P)-c)^2 ≤ (2*q/((n+1:ℕ):ℝ))^2 := by
      have he := (sq_le_sq₀ (abs_nonneg ((∫ w,brownianCellClock B u T t (n+1) w ∂P)-c))
        (div_nonneg (mul_nonneg (by norm_num) hq) (Nat.cast_nonneg _))).mpr hm.2
      simpa only [sq_abs] using he
    have he : (2*q/((n+1:ℕ):ℝ))^2=4*q^2/((n:ℝ)+1)^2 := by push_cast; rw [div_pow]; ring
    rw [he] at hb
    simp only [Nat.cast_add,Nat.cast_one] at hv
    exact add_le_add hv hb

end Asakura.Chapter7
