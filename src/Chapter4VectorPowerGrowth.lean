import Chapter4PowerGrowth
import Chapter4VectorPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1600000

lemma vector_square_growth_norm {dim : ℕ} (x : Fin dim → ℝ) (u L : ℝ)
    (hL : 0≤L) (h : u^2≤L*(1+∑ i,(x i)^2)) :
    u^2≤(L*(dim+1))*(1+‖x‖^2) := by
  have hs : (∑ i,(x i)^2)≤(dim:ℝ)*‖x‖^2 := by
    calc
      _ ≤ ∑ _i : Fin dim,‖x‖^2 := Finset.sum_le_sum (fun i _ => by
        have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
        simpa only [Real.norm_eq_abs,sq_abs] using hh)
      _ = _ := by simp
  have hdom : 1+(∑ i,(x i)^2)≤((dim:ℝ)+1)*(1+‖x‖^2) := by
    nlinarith only [hs,sq_nonneg ‖x‖,Nat.cast_nonneg (α := ℝ) dim]
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdom hL)

lemma vector_square_growth_power_bound {dim : ℕ} (x : Fin dim → ℝ) (u L p : ℝ)
    (hL : 0≤L) (hp : 0≤p) (h : u^2≤L*(1+∑ i,(x i)^2)) :
    |u|^p≤((L*(dim+1))^(p/2)*(2:ℝ)^(p/2))*(1+‖x‖^p) := by
  have hs : (∑ i,(x i)^2)≤(dim:ℝ)*‖x‖^2 := by
    calc
      _ ≤ ∑ _i : Fin dim,‖x‖^2 := Finset.sum_le_sum (fun i _ => by
        have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
        simpa only [Real.norm_eq_abs,sq_abs] using hh)
      _ = _ := by simp
  have hdom : 1+(∑ i,(x i)^2)≤((dim:ℝ)+1)*(1+‖x‖^2) := by
    nlinarith only [hs,sq_nonneg ‖x‖,Nat.cast_nonneg (α := ℝ) dim]
  have hu : u^2≤(L*(dim+1))*(1+‖x‖^2) :=
    h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdom hL)
  simpa only [abs_norm] using square_growth_power_bound u ‖x‖ (L*(dim+1)) p (by positivity) hp hu

end Asakura.Chapter4
