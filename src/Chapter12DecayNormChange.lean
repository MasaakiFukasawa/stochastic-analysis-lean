import Chapter12CharacteristicDecay

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Polynomial decay is preserved when replacing a finite-dimensional
coordinate norm by the Euclidean norm used in Fourier integration. -/
theorem decay_under_linear_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (φ : F → ℂ) (k : ℕ)
    (h : ∃ A : ℝ,0≤A ∧ ∀ x,‖φ (e x)‖≤A/(1+‖x‖)^k) :
    ∃ A : ℝ,0≤A ∧ ∀ y,‖φ y‖≤A/(1+‖y‖)^k := by
  obtain ⟨A,hA,h⟩ := h
  let C : ℝ := max 1 ‖e.toContinuousLinearMap‖
  have hC : 1≤C := le_max_left _ _
  refine ⟨A*C^k,mul_nonneg hA (pow_nonneg (by linarith) _),?_⟩
  intro y
  have hn : 1+‖y‖≤C*(1+‖e.symm y‖) := by
    have he := e.toContinuousLinearMap.le_opNorm (e.symm y)
    change ‖e (e.symm y)‖≤‖e.toContinuousLinearMap‖*‖e.symm y‖ at he
    rw [e.apply_symm_apply] at he
    have hh := mul_le_mul_of_nonneg_right (le_max_right 1 ‖e.toContinuousLinearMap‖) (norm_nonneg (e.symm y))
    dsimp [C]
    nlinarith
  have hf := h (e.symm y)
  rw [e.apply_symm_apply] at hf
  apply (le_div_iff₀ (by positivity : 0<(1+‖y‖)^k)).mpr
  calc
    ‖φ y‖*(1+‖y‖)^k≤‖φ y‖*(C*(1+‖e.symm y‖))^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn k) (norm_nonneg _)
    _ = (‖φ y‖*(1+‖e.symm y‖)^k)*C^k := by rw [mul_pow];ring
    _ ≤ A*C^k := mul_le_mul_of_nonneg_right
      ((le_div_iff₀ (by positivity)).mp hf) (pow_nonneg (by linarith) _)

end Asakura.Chapter12
