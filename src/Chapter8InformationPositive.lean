import Chapter6LikelihoodEnergy
import Chapter8NonsingularEvent

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter6
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Empirical information is automatically positive semidefinite; this
also identifies its nonsingular event with its positive-definite event. -/
theorem information_gram_posSemidef {p d : ℕ} (H : Fin p → Fin d → ℝ → ℝ)
    (T : ℝ) (hT : 0≤T) (hH : ∀ k j,ContinuousOn (H k j) (Icc 0 T)) :
    (show Matrix (Fin p) (Fin p) ℝ from fun k l => ∫ r in 0..T,∑ j,H k j r*H l j r).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext k l
    simp only [Matrix.conjTranspose_apply,star_trivial]
    congr 1
    funext r
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro v
    simpa only [star_trivial] using
      (show 0 ≤ v ⬝ᵥ ((fun k l => ∫ r in 0..T,∑ j,H k j r*H l j r) *ᵥ v) from by
        rw [← likelihood_energy_gram H T hT hH v]
        exact intervalIntegral.integral_nonneg hT (fun r _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem information_posDef_iff_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hJ : J.PosSemidef) : J.PosDef ↔ J.det ≠ 0 := by
  rw [hJ.posDef_iff_isUnit,J.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]

end Asakura.Chapter8
