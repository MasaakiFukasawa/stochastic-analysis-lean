import Chapter12DerivativeGrowthAlgebra

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Finitely many polynomial bounds admit one common envelope whose
constant is at least one. -/
theorem finite_polynomial_envelope {E : Type*} [NormedAddCommGroup E]
    (b : ℕ → E → ℝ)
    (hb : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x, b i x ≤ C*(1+‖x‖)^a) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ a : ℕ, ∀ i, i ≤ k → ∀ x, b i x ≤ C*(1+‖x‖)^a := by
  classical
  choose C hC a hbound using hb
  let J := Finset.range (k+1)
  let D := 1+∑ i ∈ J,C i
  let A := ∑ i ∈ J,a i
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [Finset.sum_nonneg (s := J) (fun i _ => hC i)]
  refine ⟨D,hD,A,fun i hi x => ?_⟩
  have hiJ : i ∈ J := Finset.mem_range.mpr (by omega)
  have hCi : C i ≤ D := by
    have hh := Finset.single_le_sum (s := J) (f := C) (fun j _ => hC j) hiJ
    dsimp only [D]
    linarith
  have hai : a i ≤ A := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hiJ
  apply (hbound i x).trans
  apply mul_le_mul hCi (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hai)
    (by positivity) (by linarith)

end Asakura.Chapter12
