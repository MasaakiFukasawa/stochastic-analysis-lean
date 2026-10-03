import Chapter6BridgeGridSum

open Finset
open scoped BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1600000

theorem bridge_bound_sum (n d : ℕ) (hn : 0<n) (h K R : ℝ) (hh : 0<h) (hK : 0≤K) :
    (∑ k ∈ range n,h/((n:ℝ)*h-(k:ℝ)*h)*K*
      (((n:ℝ)*h-(k:ℝ)*h)/((n:ℝ)*h)*R+Real.sqrt ((d:ℝ)*((n:ℝ)*h-(k:ℝ)*h))))
    ≤K*(R+2*Real.sqrt ((d:ℝ)*((n:ℝ)*h))) := by
  have hnt : 0<(n:ℝ)*h := mul_pos (Nat.cast_pos.mpr hn) hh
  have he k (hk : k∈range n) :
      h/((n:ℝ)*h-(k:ℝ)*h)*K*
      (((n:ℝ)*h-(k:ℝ)*h)/((n:ℝ)*h)*R+Real.sqrt ((d:ℝ)*((n:ℝ)*h-(k:ℝ)*h)))
      =K*h/((n:ℝ)*h)*R+K*Real.sqrt (d:ℝ)*(h/Real.sqrt ((n:ℝ)*h-(k:ℝ)*h)) := by
    have hp : 0<(n:ℝ)*h-(k:ℝ)*h := sub_pos.mpr (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr (mem_range.mp hk)) hh)
    have hs := Real.sq_sqrt hp.le
    have hsp : 0<Real.sqrt ((n:ℝ)*h-(k:ℝ)*h) := Real.sqrt_pos.2 hp
    rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    generalize hq : (n:ℝ)*h-(k:ℝ)*h=q at hp hs hsp ⊢
    generalize ht : (n:ℝ)*h=t at hnt ⊢
    have hsq : Real.sqrt q/q=1/Real.sqrt q := by
      apply (div_eq_div_iff hp.ne' hsp.ne').2
      nlinarith
    calc
      h/q*K*(q/t*R+Real.sqrt (d:ℝ)*Real.sqrt q) =
          K*h/t*R+K*Real.sqrt (d:ℝ)*h*(Real.sqrt q/q) := by
        field_simp
        <;> ring
      _ = K*h/t*R+K*Real.sqrt (d:ℝ)*(h/Real.sqrt q) := by rw [hsq]; ring
  rw [sum_congr rfl he,sum_add_distrib]
  rw [←mul_sum]
  simp only [sum_const,card_range,nsmul_eq_mul]
  have hc : K*h/((n:ℝ)*h)*((n:ℝ)*R)=K*R := by field_simp
  rw [hc,←mul_sum]
  have hb := mul_le_mul_of_nonneg_left (bridge_grid_singular_sum n h hh)
    (mul_nonneg hK (Real.sqrt_nonneg (d:ℝ)))
  rw [Real.sqrt_mul (Nat.cast_nonneg d)]
  nlinarith

end Asakura.Chapter6
