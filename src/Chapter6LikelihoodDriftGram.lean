import Chapter6LikelihoodEnergy

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000

lemma likelihood_score_drift_gram {n d : ℕ} (H : Fin n → Fin d → ℝ → ℝ)
    (R : ℝ) (hR : 0≤R) (hH : ∀ k j,ContinuousOn (H k j) (Icc 0 R))
    (θ : Fin n → ℝ) (k : Fin n) :
    (∑ j,∫ r in 0..R,H k j r*(∑ l,θ l*H l j r))=
      ((fun k l => ∫ r in 0..R,∑ j,H k j r*H l j r) *ᵥ θ) k := by
  have hi l j : IntervalIntegrable (fun r => H k j r*H l j r) volume 0 R :=
    ((hH k j).mul (hH l j)).intervalIntegrable_of_Icc hR
  change (∑ j,∫ r in 0..R,H k j r*(∑ l,θ l*H l j r))=∑ l,(∫ r in 0..R,∑ j,H k j r*H l j r)*θ l
  have he j : (∫ r in 0..R,H k j r*(∑ l,θ l*H l j r))=∑ l,(∫ r in 0..R,H k j r*H l j r)*θ l := by
    simp_rw [mul_sum,show ∀ r l,H k j r*(θ l*H l j r)=(H k j r*H l j r)*θ l from fun r l => by ring]
    rw [intervalIntegral.integral_finsetSum (fun l _ => (hi l j).mul_const (θ l))]
    simp only [intervalIntegral.integral_mul_const]
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  rw [intervalIntegral.integral_finsetSum (fun j _ => hi l j),sum_mul]

end Asakura.Chapter6
