import Chapter7DriftIntervalRemainder
import Chapter7ProbabilityErrorAssembly

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1200000

lemma bounded_drift_increment (b : ℝ → ℝ) (s t K : ℝ) (hst : s≤t)
    (hb : ∀ r∈Icc s t,|b r|≤K) :
    |∫ r in s..t,b r|≤K*(t-s) := by
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (f := b) (C := K)
    (fun r hr => by
      rw [uIoc_of_le hst] at hr
      simpa only [Real.norm_eq_abs] using hb r ⟨hr.1.le,hr.2⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using he

lemma drift_square_grid_bound {n : ℕ} (hn : 0<n) (A B : Fin n → ℝ) (T K : ℝ)
    (hT : 0≤T) (hK : 0≤K)
    (hA : ∀ k,|A k|≤K*(T/n)) (hB : ∀ k,|B k|≤K*(T/n)) :
    Real.sqrt (n:ℝ)*|∑ k,A k*B k|≤K^2*T^2/Real.sqrt (n:ℝ) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnR
  have hsq := Real.sq_sqrt hnR.le
  have hh : 0≤K*(T/(n:ℝ)) := mul_nonneg hK (div_nonneg hT hnR.le)
  have hb : |∑ k,A k*B k|≤(n:ℝ)*(K*(T/n))^2 := by
    calc
      _ ≤ ∑ k,|A k*B k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n,(K*(T/n))^2 := sum_le_sum (fun k _ => by
        rw [abs_mul,pow_two]
        exact mul_le_mul (hA k) (hB k) (abs_nonneg _) hh)
      _ = _ := by simp
  apply (mul_le_mul_of_nonneg_left hb hs.le).trans_eq
  apply (eq_div_iff hs.ne').mpr
  field_simp
  rw [hsq]

end Asakura.Chapter7
