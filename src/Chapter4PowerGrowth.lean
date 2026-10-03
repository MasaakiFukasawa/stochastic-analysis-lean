import Chapter4TimePowerHolder
import Mathlib.Analysis.MeanInequalities

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1500000

lemma nonnegative_sum_power_bound (a b q : ℝ) (ha : 0≤a) (hb : 0≤b) (hq : 0≤q) :
    (a+b)^q≤(2:ℝ)^q*(a^q+b^q) := by
  have hp : (a+b)^q≤(2*max a b)^q := Real.rpow_le_rpow (add_nonneg ha hb)
    (by have h₁ := le_max_left a b; have h₂ := le_max_right a b; linarith only [h₁,h₂]) hq
  rw [Real.mul_rpow (by norm_num) (ha.trans (le_max_left a b))] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) q)
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (Real.rpow_nonneg ha q)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hb q)

lemma square_power_half (x p : ℝ) : (x^2)^(p/2)=|x|^p := by
  rw [← sq_abs,← Real.rpow_natCast_mul (abs_nonneg x)]
  congr 1
  ring

/-- Linear growth of squared coefficients gives the p-power bound used
inside both the drift and BDG estimates. -/
theorem square_growth_power_bound (u x L p : ℝ) (hL : 0≤L) (hp : 0≤p)
    (h : u^2≤L*(1+x^2)) :
    |u|^p≤(L^(p/2)*(2:ℝ)^(p/2))*(1+|x|^p) := by
  have hq : 0≤p/2 := by positivity
  have hh := Real.rpow_le_rpow (sq_nonneg u) h hq
  rw [square_power_half,Real.mul_rpow hL (by positivity)] at hh
  have hb := nonnegative_sum_power_bound 1 (x^2) (p/2) zero_le_one (sq_nonneg _) hq
  rw [Real.one_rpow,square_power_half] at hb
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL _))

/-- The finite-sum inequality used to combine initial value, drift and
martingale terms, with no positivity restrictions on the summands. -/
theorem finite_sum_norm_power {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (x : Fin n → E) (p : ℝ) (hp : 1≤p) :
    ‖∑ i,x i‖^p≤(n:ℝ)^(p-1)*∑ i,‖x i‖^p := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ (f := fun i => ‖x i‖) hp
    (fun _ _ => norm_nonneg _)
  simpa only [Finset.card_univ,Fintype.card_fin] using
    (Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le _ _) (zero_le_one.trans hp)).trans h

end Asakura.Chapter4
