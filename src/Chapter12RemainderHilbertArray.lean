import Chapter12BanachArrayNorm
import Chapter12PartitionArrayBound
import Chapter12HigherChainRemainder

open scoped ContDiff BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem remainder_hilbert_array_bound {N G E F : Type*} [Fintype N]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : G → E) (b : E → F) (k : ℕ) (z : G) (e : N → G)
    (B C : ℕ → ℝ) (hB : ∀j,0≤B j) (hC : ∀j,0≤C j)
    (hb : ∀j,2≤j → j≤k → ‖iteratedFDeriv ℝ j b (f z)‖≤B j)
    (hf : ∀j,0<j → j<k → Real.sqrt (∑a : Fin j → N,‖iteratedFDeriv ℝ j f z (e ∘ a)‖^2)≤C j) :
    Real.sqrt (∑a : Fin k → N,‖higherChainRemainder f b k z (e ∘ a)‖^2) ≤
      ∑c : OrderedFinpartition k with 2≤c.length,B c.length*∏i,C (c.partSize i) := by
  classical
  let term := fun (c : OrderedFinpartition k) (a : Fin k → N) =>
    iteratedFDeriv ℝ c.length b (f z)
      (fun i => iteratedFDeriv ℝ (c.partSize i) f z (e ∘ a ∘ c.emb i))
  have he (a : Fin k → N) : higherChainRemainder f b k z (e ∘ a)=
      ∑c : OrderedFinpartition k with 2≤c.length,term c a := by
    simp only [higherChainRemainder,ContinuousMultilinearMap.sum_apply,
      FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries,term]
    rfl
  simp_rw [he]
  apply (banach_array_norm_finset_sum _ term).trans
  apply Finset.sum_le_sum
  intro c hc
  have hc2 := (Finset.mem_filter.mp hc).2
  have hh := partition_array_norm_bound c (iteratedFDeriv ℝ c.length b (f z))
    (fun i a => iteratedFDeriv ℝ (c.partSize i) f z (e ∘ a))
  change Real.sqrt (∑a : Fin k → N,‖term c a‖^2)≤_ at hh
  apply hh.trans
  apply mul_le_mul (hb _ hc2 c.length_le)
  · apply Finset.prod_le_prod₀
    · intro i _;exact Real.sqrt_nonneg _
    · intro i _;exact hf _ (c.partSize_pos i) (nonlinear_partition_lower_orders c hc2 i)
  · exact Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  · exact hB _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.remainder_hilbert_array_bound
