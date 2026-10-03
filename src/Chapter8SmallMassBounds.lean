import FullAuditTimeAverageCoupling
import FullAuditChapter4Gronwall

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- Exact mass dependence of the decaying convolution kernel. -/
theorem small_mass_kernel_integral (α m t : ℝ) (hα : 0 < α) (hm : 0 < m) :
    (∫ s in (0:ℝ)..t, Real.exp (-α*(t-s)/m)) =
      m/α*(1-Real.exp (-α*t/m)) := by
  have he : (fun s : ℝ => Real.exp (-α*(t-s)/m)) =
      (fun s => Real.exp (-(α/m)*(t-s))) := by
    funext s; congr 1; ring
  rw [he,intervalIntegral.integral_comp_sub_left (fun s : ℝ => Real.exp (-(α/m)*s)) t]
  simp only [sub_self,sub_zero]
  rw [integrated_exponential_decay (α/m) t (div_pos hα hm)]
  congr 1 <;> field_simp <;> ring

/-- The drift convolution has an O(m) kernel mass uniformly in t≥0. -/
theorem small_mass_kernel_bound (α m t : ℝ) (hα : 0 < α) (hm : 0 < m) (ht : 0 ≤ t) :
    0 ≤ (∫ s in (0:ℝ)..t, Real.exp (-α*(t-s)/m)) ∧
      (∫ s in (0:ℝ)..t, Real.exp (-α*(t-s)/m)) ≤ m/α := by
  constructor
  · exact intervalIntegral.integral_nonneg ht (fun s _ => (Real.exp_pos _).le)
  · rw [small_mass_kernel_integral α m t hα hm]
    exact mul_le_of_le_one_right (div_nonneg hm.le hα.le) (by linarith [Real.exp_pos (-α*t/m)])

/-- Ito isometry uses the squared kernel, whose integral is O(m), not O(m²). -/
theorem small_mass_squared_kernel_bound (α m t : ℝ) (hα : 0 < α) (hm : 0 < m) (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, (Real.exp (-α*(t-s)/m))^2) ≤ m/(2*α) := by
  have he (s : ℝ) : (Real.exp (-α*(t-s)/m))^2 = Real.exp (-(2*α)*(t-s)/m) := by
    rw [pow_two,← Real.exp_add]
    congr 1; ring
  simp_rw [he]
  exact (small_mass_kernel_bound (2*α) m t (by positivity) hm ht).2

/-- The last Gronwall step gives a uniform-in-time mean-square rate from
precisely the remainder estimate appearing in the manuscript. -/
theorem small_mass_uniform_gronwall (u : ℝ → ℝ → ℝ) (C B T : ℝ)
    (hC : 0 ≤ C) (hB : 0 < B) (hT : 0 ≤ T)
    (hc : ∀ m > 0, ContinuousOn (u m) (Icc 0 T))
    (hi : ∀ m > 0, ∀ t ∈ Icc 0 T, u m t ≤ C*m+B*∫ s in (0:ℝ)..t,u m s) :
    ∀ m > 0, ∀ t ∈ Icc 0 T, u m t ≤ C*Real.exp (B*T)*m := by
  intro m hm t ht
  have hh := ch4_gronwall_written (u m) (C*m) B T hT (hc m hm) hB (hi m hm) t ht
  have he : Real.exp (B*t) ≤ Real.exp (B*T) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ht.2 hB.le)
  have hb := hh.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hC hm.le))
  convert hb using 1 <;> ring

end Asakura.Chapter8
