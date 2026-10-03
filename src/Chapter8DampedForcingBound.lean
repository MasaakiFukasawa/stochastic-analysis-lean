import Chapter8DampedSemigroup
import Chapter8SmallMassBounds

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The same estimate applies to continuous functions with values in L²;
it is the drift-remainder estimate before taking its squared norm. -/
theorem exponential_convolution_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Continuous f) (α m T C : ℝ)
    (hα : 0<α) (hm : 0<m) (hT : 0≤T) (hC : 0≤C)
    (hb : ∀ s∈Icc 0 T,‖f s‖≤C) :
    ‖∫ s in 0..T,Real.exp (-α*(T-s)/m) • f s‖≤C*m/α := by
  have he : Continuous (fun s : ℝ => Real.exp (-α*(T-s)/m)) := by fun_prop
  calc
    _ ≤ ∫ s in 0..T,Real.exp (-α*(T-s)/m)*C := by
      apply intervalIntegral.norm_integral_le_of_norm_le hT
      · apply ae_of_all
        intro s hs
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hb s ⟨hs.1.le,hs.2⟩) (Real.exp_pos _).le
      · exact (he.mul continuous_const).intervalIntegrable _ _
    _ = C*(∫ s in 0..T,Real.exp (-α*(T-s)/m)) := by
      rw [intervalIntegral.integral_mul_const,mul_comm]
    _ ≤ C*(m/α) := mul_le_mul_of_nonneg_left (small_mass_kernel_bound α m T hα hm hT).2 hC
    _ = _ := by ring

theorem operator_convolution_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (K : ℝ → E →L[ℝ] E) (hK : Continuous K) (f : ℝ → E) (hf : Continuous f)
    (α m T C : ℝ) (hα : 0<α) (hm : 0<m) (hT : 0≤T) (hC : 0≤C)
    (hb : ∀ s∈Icc 0 T,‖f s‖≤C)
    (hKb : ∀ s∈Icc 0 T,‖K s‖≤Real.exp (-α*(T-s)/m)) :
    ‖∫ s in 0..T,K s (f s)‖≤C*m/α := by
  have he : Continuous (fun s : ℝ => Real.exp (-α*(T-s)/m)*C) := by fun_prop
  calc
    _ ≤ ∫ s in 0..T,Real.exp (-α*(T-s)/m)*C := by
      apply intervalIntegral.norm_integral_le_of_norm_le hT
      · apply ae_of_all
        intro s hs
        exact ((K s).le_opNorm (f s)).trans
          (mul_le_mul (hKb s ⟨hs.1.le,hs.2⟩) (hb s ⟨hs.1.le,hs.2⟩) (norm_nonneg _) (Real.exp_pos _).le)
      · exact he.intervalIntegrable _ _
    _ = C*(∫ s in 0..T,Real.exp (-α*(T-s)/m)) := by
      rw [intervalIntegral.integral_mul_const,mul_comm]
    _ ≤ C*(m/α) := mul_le_mul_of_nonneg_left (small_mass_kernel_bound α m T hα hm hT).2 hC
    _ = _ := by ring
end Asakura.Chapter8
