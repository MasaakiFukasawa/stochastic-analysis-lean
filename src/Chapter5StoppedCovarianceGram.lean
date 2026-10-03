import Chapter5StoppedBrownianFamily
import Chapter5CoordinateGenerator

open Set
open scoped BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- The covariance density of repeated stopped Brownian observations is
exactly the Gram matrix of their active noise directions. -/
theorem stopped_covariance_density_gram {d k : ℕ}
    (index : Fin k → Fin d) (τ : Fin k → ℝ) (r : ℝ) (i j : Fin k) :
    (if index i=index j then (Iio (min (τ i) (τ j))).indicator (fun _ => (1:ℝ)) r else 0)=
      ∑ l : Fin d,(if r<τ i ∧ index i=l then (1:ℝ) else 0)*
        (if r<τ j ∧ index j=l then (1:ℝ) else 0) := by
  classical
  have hs : (∑ l : Fin d,(if r<τ i ∧ index i=l then (1:ℝ) else 0)*
        (if r<τ j ∧ index j=l then (1:ℝ) else 0))=
      (if r<τ i then (1:ℝ) else 0)*(if r<τ j ∧ index j=index i then (1:ℝ) else 0) := by
    rw [Finset.sum_eq_single (index i)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  rw [hs]
  by_cases hi : r<τ i <;> by_cases hj : r<τ j <;> by_cases hij : index i=index j <;>
    simp [hi,hj,hij,eq_comm,indicator,lt_min_iff]

end Asakura.Chapter5
