import Chapter7ShiftedBlockMoments

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma brownian_block_grid_mean {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (s ell : Fin n → ℝ) (hs : ∀ k,0 ≤ s k) (hl : ∀ k,0 ≤ ell k) :
    let U := fun (k : Fin n) w => ∫ r in 0..ell k,
      (∑ j,u j*(B.W j (realTimeClamp (s k+r)) w-B.W j (realTimeClamp (s k)) w))*
      (∑ j,v j*(B.W j (realTimeClamp (s k+r)) w-B.W j (realTimeClamp (s k)) w))
    MemLp (fun w => ∑ k,U k w) 2 P ∧
      (∫ w,∑ k,U k w ∂P)=(∑ k,(ell k)^2)*(∑ j,u j*v j)/2 := by
  dsimp only
  let U := fun (k : Fin n) w => ∫ r in 0..ell k,
      (∑ j,u j*(B.W j (realTimeClamp (s k+r)) w-B.W j (realTimeClamp (s k)) w))*
      (∑ j,v j*(B.W j (realTimeClamp (s k+r)) w-B.W j (realTimeClamp (s k)) w))
  have hmom k := shifted_brownian_block_moments P B u v (s k) (ell k) (hs k) (hl k)
  refine ⟨memLp_finsetSum _ (fun k _ => (hmom k).1),?_⟩
  rw [integral_finsetSum _ (fun k _ => (hmom k).1.integrable (by norm_num))]
  simp only [(hmom _).2.1]
  rw [← Finset.sum_div,← Finset.sum_mul]

end Asakura.Chapter7
