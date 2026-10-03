import FullAuditPositivePartLimit
import Mathlib.Topology.Instances.Rat

open Set
namespace Asakura.FullAudit

/-- Rational coefficients suffice by closedness and density. -/
theorem quadratic_nonnegative_of_rationals (a b c : ℝ)
    (h : ∀ q : ℚ, 0 ≤ a*(q:ℝ)^2+2*b*(q:ℝ)+c) :
    ∀ x : ℝ, 0 ≤ a*x^2+2*b*x+c := by
  have hc : IsClosed {x : ℝ | 0 ≤ a*x^2+2*b*x+c} :=
    isClosed_le continuous_const (((continuous_const.mul (continuous_id.pow 2)).add
      (continuous_const.mul continuous_id)).add continuous_const)
  have hs : range (fun q : ℚ => (q:ℝ)) ⊆ {x : ℝ | 0 ≤ a*x^2+2*b*x+c} := by
    rintro x ⟨q,rfl⟩; exact h q
  have hcl := hc.closure_subset_iff.mpr hs
  rw [Rat.denseRange_cast.closure_range] at hcl
  exact fun x => hcl (mem_univ x)

/-- The degenerate a=0 case is included in the discriminant argument. -/
theorem quadratic_interval_cs (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ q : ℚ, 0 ≤ a*(q:ℝ)^2+2*b*(q:ℝ)+c) :
    |b| ≤ Real.sqrt a*Real.sqrt c := by
  have hp := quadratic_nonnegative_of_rationals a b c h
  have hdisc : b^2 ≤ a*c := by
    by_cases haz : a = 0
    · by_cases hb : b = 0
      · simp [hb,haz]
      · have hr := hp (-(c+1)/(2*b))
        have he : 2*b*(-(c+1)/(2*b))+c = -1 := by field_simp; ring
        rw [haz,zero_mul,zero_add,he] at hr
        norm_num at hr
    · have hr := mul_nonneg ha (hp (-b/a))
      have he : a*(a*(-b/a)^2+2*b*(-b/a)+c) = a*c-b^2 := by field_simp; ring
      rw [he] at hr
      linarith
  apply (sq_le_sq₀ (abs_nonneg b) (mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c))).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hc]
  exact hdisc

end Asakura.FullAudit
