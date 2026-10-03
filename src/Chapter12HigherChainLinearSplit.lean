import Chapter12OneBlockPartition
import Chapter12HigherChainRemainder

open Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The highest inner derivative occurs only linearly. This is the term
moved to the linear Volterra equation in the SDE proof. -/
theorem higher_chain_linear_split {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : E) (v : Fin (n+1) → E) :
    iteratedFDeriv ℝ (n+1) (g ∘ f) x v =
      fderiv ℝ g (f x) (iteratedFDeriv ℝ (n+1) f x v)+higherChainRemainder f g (n+1) x v := by
  classical
  let term := fun c : OrderedFinpartition (n+1) =>
    iteratedFDeriv ℝ c.length g (f x)
      (fun i => iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i))
  have hone : term (oneBlockPartition n)=fderiv ℝ g (f x) (iteratedFDeriv ℝ (n+1) f x v) := by
    simp [term,oneBlockPartition,iteratedFDeriv_one_apply,Function.comp_def]
  have hset : Finset.univ.erase (oneBlockPartition n)=
      Finset.univ.filter (fun c : OrderedFinpartition (n+1) => 2≤c.length) := by
    ext c
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.mem_filter,true_and]
    exact partition_ne_oneBlock c
  rw [higher_chain_partition_formula f g hf hg (n+1) x v]
  change (∑ c,term c)=_
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (oneBlockPartition n)),hone,hset,add_comm]
  congr 1
  simp only [higherChainRemainder,ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries]
  rfl

end Asakura.Chapter12
