import Chapter6LikelihoodQuadratic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2800000

/-- Expansion of the actual quadratic-variation time integral into the
information matrix. The entries are time integrals of coefficient products. -/
theorem likelihood_energy_gram {n d : ℕ} (H : Fin n → Fin d → ℝ → ℝ)
    (R : ℝ) (hR : 0≤R) (hH : ∀ k j,ContinuousOn (H k j) (Icc 0 R))
    (θ : Fin n → ℝ) :
    (∫ r in 0..R,∑ j,(∑ k,θ k*H k j r)^2)=
      θ ⬝ᵥ ((fun k l => ∫ r in 0..R,∑ j,H k j r*H l j r) *ᵥ θ) := by
  have hi k l j : IntervalIntegrable (fun r => H k j r*H l j r) volume 0 R :=
    ((hH k j).mul (hH l j)).intervalIntegrable_of_Icc hR
  have his k l : IntervalIntegrable (fun r => ∑ j,H k j r*H l j r) volume 0 R := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum univ (fun j _ => hi k l j)
  have he r : (∑ j,(∑ k,θ k*H k j r)^2)=∑ k,∑ l,θ k*((∑ j,H k j r*H l j r)*θ l) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finset_sum]
  · unfold dotProduct Matrix.mulVec
    apply sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_finset_sum]
    · simp_rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_mul_const]
      simp only [dotProduct,mul_sum]
    · intro l _
      exact ((his k l).mul_const (θ l)).const_mul (θ k)
  · intro k _
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum univ
      (fun l _ => ((his k l).mul_const (θ l)).const_mul (θ k))

end Asakura.Chapter6
