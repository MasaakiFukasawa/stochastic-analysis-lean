import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- In every nonlinear partition term, every inner derivative has
strictly smaller order than the derivative being computed. -/
theorem nonlinear_partition_lower_orders {n : ℕ} (c : OrderedFinpartition n)
    (hc : 2≤c.length) (i : Fin c.length) : c.partSize i<n := by
  classical
  letI : Nontrivial (Fin c.length) := Fin.nontrivial_iff_two_le.mpr hc
  obtain ⟨j,hji⟩ := exists_ne i
  have hsum : (∑ m,c.partSize m)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr c.equivSigma
  have hpair : c.partSize i+c.partSize j≤∑ m,c.partSize m := by
    have hh := Finset.sum_le_sum_of_subset (f := c.partSize)
      (show ({i,j} : Finset (Fin c.length))⊆Finset.univ from Finset.subset_univ _)
    simpa [Finset.sum_pair hji.symm] using hh
  have hpos := c.partSize_pos j
  omega

/-- The higher chain rule in the exact partition form used in the
Volterra induction for additive-noise SDE approximations. -/
theorem higher_chain_partition_formula {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (g ∘ f) x v =
      ∑ c : OrderedFinpartition n,iteratedFDeriv ℝ c.length g (f x)
        (fun i => iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)) := by
  have he := congrArg (fun A : E [×n]→L[ℝ] G => A v)
    (iteratedFDeriv_comp (x := x) hg.contDiffAt hf.contDiffAt (show (n : ℕ∞ω)≤∞ by simp))
  simp only [FormalMultilinearSeries.taylorComp,ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries] at he
  exact he

end Asakura.Chapter12
