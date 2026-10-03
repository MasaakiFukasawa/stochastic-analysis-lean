import Chapter8ForcedLinearIntegral

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Integrating the velocity equation and applying the inverse resistance
identifies the position and its exact finite-mass correction. -/
theorem newton_position_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : E ≃L[ℝ] E) (m : ℝ) (hm : m≠0) (q v Q V F W IV : E)
    (hQ : Q=q+IV) (hV : V=v-m⁻¹ • Γ IV-m⁻¹ • F+m⁻¹ • W) :
    Q=q-Γ.symm F+Γ.symm W-m • Γ.symm (V-v) := by
  rw [hQ,hV]
  simp only [map_add,map_sub,map_smul,Γ.symm_apply_apply,smul_add,smul_sub,smul_smul,
    mul_inv_cancel₀ hm,one_smul]
  module

/-- The damped velocity formula gives precisely the initial-velocity,
drift-convolution and noise-convolution terms of the remainder. -/
theorem newton_position_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E →L[ℝ] E) (m : ℝ) (hm : m≠0) (v V Ev F N : E)
    (hV : V=Ev-m⁻¹ • F+N) :
    -m • M (V-v)=m • M (v-Ev)+M F-m • M N := by
  rw [hV]
  simp only [map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul]
  have he : (-m)*m⁻¹= -1 := by field_simp
  rw [he]
  module
end Asakura.Chapter8
