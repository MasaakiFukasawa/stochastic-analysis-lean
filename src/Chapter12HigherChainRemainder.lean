import Chapter12HigherChainPartitions

open Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def higherChainRemainder {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (n : ℕ) (x : E) : E [×n]→L[ℝ] G :=
  ∑ c : OrderedFinpartition n with 2≤c.length,
    (ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c

/-- The nonlinear remainder has a bound depending only on lower
inner derivatives and the stated bounds on the drift derivatives. -/
theorem higher_chain_remainder_bound {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (n : ℕ) (x : E) (B C : ℕ → ℝ)
    (hB : ∀ j,0≤B j) (hC : ∀ j,0≤C j)
    (hg : ∀ j,2≤j → j≤n → ‖iteratedFDeriv ℝ j g (f x)‖≤B j)
    (hf : ∀ j,0<j → j<n → ‖iteratedFDeriv ℝ j f x‖≤C j) :
    ‖higherChainRemainder f g n x‖≤
      ∑ c : OrderedFinpartition n with 2≤c.length,B c.length*∏ i,C (c.partSize i) := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  have hc2 := (Finset.mem_filter.mp hc).2
  have hterm := c.norm_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ c.length g (f x)) (fun i => iteratedFDeriv ℝ (c.partSize i) f x)
  apply hterm.trans
  apply mul_le_mul (hg c.length hc2 c.length_le)
  · apply Finset.prod_le_prod₀
    · intro i _
      exact norm_nonneg _
    · intro i _
      exact hf (c.partSize i) (c.partSize_pos i) (nonlinear_partition_lower_orders c hc2 i)
  · positivity
  · exact hB _

end Asakura.Chapter12
