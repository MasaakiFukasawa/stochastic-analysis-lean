import Chapter12PolynomialEnvelope
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The full cylinder growth condition is stable under smooth composition.
The finite-order chain-rule bound is given a common polynomial envelope. -/
theorem iterated_polynomial_growth_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C*(1+‖x‖)^a)
    (hgB : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C*(1+‖x‖)^a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ C*(1+‖x‖)^a := by
  obtain ⟨C,hC,a,hfb⟩ := finite_polynomial_envelope (fun i x => ‖iteratedFDeriv ℝ i f x‖) hfB k
  obtain ⟨K,hK,b,hgb⟩ := finite_polynomial_envelope (fun i y => ‖iteratedFDeriv ℝ i g y‖) hgB k
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨(k.factorial:ℝ)*K*2^b*C^(b+k),by positivity,a*(b+k),fun x => ?_⟩
  let D := C*(1+‖x‖)^a
  have hbase : 1 ≤ 1+‖x‖ := by linarith [norm_nonneg x]
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hbase)
  have hfx : 1+‖f x‖ ≤ 2*D := by
    have hh := hfb 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at hh
    change ‖f x‖ ≤ D at hh
    linarith
  have houter (i : ℕ) (hi : i ≤ k) : ‖iteratedFDeriv ℝ i g (f x)‖ ≤ K*(2*D)^b :=
    (hgb i hi (f x)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hfx b) hK0)
  have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) : ‖iteratedFDeriv ℝ i f x‖ ≤ D^i :=
    (hfb i hik x).trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hi)
  have hb := norm_iteratedFDeriv_comp_le hg hf (by simp : (k:ℕ∞ω) ≤ ∞) x houter hinner
  apply hb.trans_eq
  dsimp only [D]
  simp only [mul_pow,Nat.mul_add,pow_add,pow_mul]
  ring

end Asakura.Chapter12
