import Chapter10VarianceTransform
import Chapter10KyleCoefficients

namespace Asakura.Chapter10

/-- Substituting the transformed model's actual coefficients into the scalar
Kalman formulas gives both the gain and the Riccati equation used in the text. -/
theorem kyle_scalar_model_coefficients (L l b S σ γ : ℝ)
    (hL : L≠0) (hl : l≠0) (hσ : σ≠0) :
    (S*(l*b)/(L*l*σ)^2)*l=b*(S/L^2)/σ^2 ∧
    (l*b)*S+S*(l*b)+(L*γ)^2-S*(l*b)^2*S/(L*l*σ)^2=
      2*l*b*S+L^2*γ^2-b^2*S^2/(L^2*σ^2) := by
  constructor <;> field_simp <;> ring

/-- Increasing uninformative order noise lowers lambda and raises expected
profit, with initial uncertainty and maturity fixed. -/
theorem kyle_noise_comparative_statics (S T σ₁ σ₂ : ℝ)
    (hS : 0<S) (hT : 0<T) (hσ : 0<σ₁) (hlt : σ₁<σ₂) :
    Real.sqrt S/(σ₂*Real.sqrt T)<Real.sqrt S/(σ₁*Real.sqrt T) ∧
      σ₁*Real.sqrt (S*T)<σ₂*Real.sqrt (S*T) := by
  have hs := Real.sqrt_pos.mpr hS
  have ht := Real.sqrt_pos.mpr hT
  exact ⟨div_lt_div_of_pos_left hs (mul_pos hσ ht) (mul_lt_mul_of_pos_right hlt ht),
    mul_lt_mul_of_pos_right hlt (Real.sqrt_pos.mpr (mul_pos hS hT))⟩

/-- Increasing private uncertainty increases both price impact and the
unconditional expected profit. -/
theorem kyle_uncertainty_comparative_statics (S₁ S₂ T σ : ℝ)
    (hS : 0≤S₁) (hlt : S₁<S₂) (hT : 0<T) (hσ : 0<σ) :
    Real.sqrt S₁/(σ*Real.sqrt T)<Real.sqrt S₂/(σ*Real.sqrt T) ∧
      σ*Real.sqrt (S₁*T)<σ*Real.sqrt (S₂*T) := by
  exact ⟨div_lt_div_of_pos_right (Real.sqrt_lt_sqrt hS hlt) (mul_pos hσ (Real.sqrt_pos.mpr hT)),
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (mul_nonneg hS hT.le)
      (mul_lt_mul_of_pos_right hlt hT)) hσ⟩

end Asakura.Chapter10
