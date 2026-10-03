import Chapter5FrozenProgressive

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Uniform Lipschitz constant for f0 + epsilon f1. This checks the
parameter-uniform hypothesis needed before applying the a-priori theorem. -/
theorem perturbed_generator_lipschitz
    {E : Type*} (f₀ f₁ : E × (ℝ × ℝ) → ℝ) (C₀ C₁ ε ε₀ : ℝ)
    (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (he : |ε|≤ε₀)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|)) :
    ∀ z y₁ z₁ y₂ z₂,
      |(f₀ (z,y₁,z₁)+ε*f₁ (z,y₁,z₁))-(f₀ (z,y₂,z₂)+ε*f₁ (z,y₂,z₂))|≤
        (C₀+ε₀*C₁)*(|y₁-y₂|+|z₁-z₂|) := by
  intro z y₁ z₁ y₂ z₂
  rw [show (f₀ (z,y₁,z₁)+ε*f₁ (z,y₁,z₁))-(f₀ (z,y₂,z₂)+ε*f₁ (z,y₂,z₂))=
    (f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂))+ε*(f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)) by ring]
  calc
    _ ≤ |f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|+|ε| *|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)| := by
      simpa only [abs_mul] using abs_add_le (f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)) (ε*(f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)))
    _ ≤ C₀*(|y₁-y₂|+|z₁-z₂|)+ε₀*(C₁*(|y₁-y₂|+|z₁-z₂|)) :=
      add_le_add (hl₀ z _ _ _ _) (mul_le_mul he (hl₁ z _ _ _ _) (abs_nonneg _) (he.trans' (abs_nonneg ε)))
    _ = _ := by ring

lemma frozen_perturbed_generator_lipschitz
    {E : Type*} (f₀ : E × (ℝ × ℝ) → ℝ) (G : E → ℝ) (C₀ ε : ℝ)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|)) :
    ∀ z y₁ z₁ y₂ z₂,
      |(f₀ (z,y₁,z₁)+ε*G z)-(f₀ (z,y₂,z₂)+ε*G z)|≤C₀*(|y₁-y₂|+|z₁-z₂|) := by
  intro z y₁ z₁ y₂ z₂
  simpa only [add_sub_add_right_eq_sub] using hl₀ z y₁ z₁ y₂ z₂

end Asakura.Chapter5
