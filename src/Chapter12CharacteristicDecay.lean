import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Chapter12HigherChainPartitions

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The coordinate selected in the characteristic-function proof can be
chosen to attain the product-space norm. Equivalent Euclidean norms change
only the constant in the resulting decay estimate. -/
theorem coordinate_power_decay {d k : ℕ} (φ : (Fin (d+1) → ℝ) → ℂ)
    (C : ℝ) (hφ : ∀ ξ,‖φ ξ‖≤1)
    (hcoord : ∀ ξ i,|ξ i|^k*‖φ ξ‖≤C) :
    ∃ A : ℝ,0≤A ∧ ∀ ξ,‖φ ξ‖≤A/(1+‖ξ‖)^k := by
  classical
  let A := (2:ℝ)^k*max 1 C
  refine ⟨A,by dsimp [A];positivity,?_⟩
  intro ξ
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin (d+1) => ‖ξ i‖)
    Finset.univ_nonempty
  have hnorm : ‖ξ‖=|ξ i| := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j))
    · exact norm_le_pi_norm ξ i
  have hc : ‖ξ‖^k*‖φ ξ‖≤C := by rw [hnorm];exact hcoord ξ i
  have hh : (1+‖ξ‖)^k*‖φ ξ‖≤A := by
    by_cases hsmall : ‖ξ‖≤1
    · calc
        _ ≤ (2:ℝ)^k*1 := mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) k)
          (hφ ξ) (norm_nonneg _) (by positivity)
        _ ≤ A := mul_le_mul_of_nonneg_left (le_max_left 1 C) (by positivity)
    · have hlarge : 1≤‖ξ‖ := (lt_of_not_ge hsmall).le
      calc
        _ ≤ (2*‖ξ‖)^k*‖φ ξ‖ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) k) (norm_nonneg _)
        _ = (2:ℝ)^k*(‖ξ‖^k*‖φ ξ‖) := by rw [mul_pow];ring
        _ ≤ (2:ℝ)^k*C := mul_le_mul_of_nonneg_left hc (by positivity)
        _ ≤ A := mul_le_mul_of_nonneg_left (le_max_right 1 C) (by positivity)
  exact (le_div_iff₀ (by positivity : 0<(1+‖ξ‖)^k)).mpr (by simpa only [mul_comm] using hh)

end Asakura.Chapter12
