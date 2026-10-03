import Chapter5GaussianRecursion
import Chapter5ObservationPrefix

open Set
namespace Asakura.Chapter5

/-- A grid observation is either already in the past or still follows the
current Brownian increment. This supplies the hypotheses of each actual
Gaussian step without changing the dimension of the observation vector. -/
theorem grid_clipped_observation_step {k : ℕ}
    (q : ℕ → ℝ) (hq : Monotone q) (obs : Fin k → ℕ) (j : ℕ) :
    (∀ i,j+1≤obs i → min (q (obs i)) (q (j+1))=q (j+1)) ∧
      (∀ i,¬j+1≤obs i → min (q (obs i)) (q (j+1))≤q j) := by
  constructor
  · intro i hi
    exact min_eq_right (hq hi)
  · intro i hi
    exact (min_le_left _ _).trans (hq (by omega))

theorem grid_clipped_observation_previous {k : ℕ}
    (q : ℕ → ℝ) (hq : Monotone q) (obs : Fin k → ℕ) (j : ℕ) (i : Fin k) :
    min (min (q (obs i)) (q (j+1))) (q j)=min (q (obs i)) (q j) := by
  rw [min_assoc,min_eq_right (hq (by omega))]

theorem grid_clipped_observation_zero {k : ℕ}
    (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0=0) (obs : Fin k → ℕ) (i : Fin k) :
    min (q (obs i)) (q 0)=0 := by
  rw [min_eq_right (hq (Nat.zero_le _)),hq0]

end Asakura.Chapter5
