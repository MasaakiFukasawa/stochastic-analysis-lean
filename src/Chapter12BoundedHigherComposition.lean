import Chapter12HigherChainPartitions

open scoped ContDiff BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem bounded_higher_composition {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (B C : ℕ → ℝ) (hB : ∀j,0≤B j) (hC : ∀j,0≤C j)
    (hb : ∀j,0<j → ∀x,‖iteratedFDeriv ℝ j f x‖≤B j)
    (hc : ∀j,0<j → ∀x,‖iteratedFDeriv ℝ j g x‖≤C j)
    (k : ℕ) (hk : 0<k) (x : E) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤
      ∑c : OrderedFinpartition k,C c.length*∏i,B (c.partSize i) := by
  classical
  rw [iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt (show (k:ℕ∞ω)≤∞ by simp)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  exact (c.norm_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ c.length g (f x)) (fun i => iteratedFDeriv ℝ (c.partSize i) f x)).trans
    (mul_le_mul (hc _ (c.length_pos hk) _)
      (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hb _ (c.partSize_pos i) x))
      (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (hC _))

theorem all_higher_bounds_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hb : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k f x‖≤C)
    (hc : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k g x‖≤C) :
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k (g ∘ f) x‖≤C := by
  classical
  have hb' : ∀k:ℕ,∃C:ℝ,0≤C ∧ (0<k → ∀x,‖iteratedFDeriv ℝ k f x‖≤C) := by
    intro k
    by_cases hk : 0<k
    · obtain ⟨C,hC,h⟩ := hb k hk
      exact ⟨C,hC,fun _ => h⟩
    · exact ⟨0,le_rfl,fun h => (hk h).elim⟩
  have hc' : ∀k:ℕ,∃C:ℝ,0≤C ∧ (0<k → ∀x,‖iteratedFDeriv ℝ k g x‖≤C) := by
    intro k
    by_cases hk : 0<k
    · obtain ⟨C,hC,h⟩ := hc k hk
      exact ⟨C,hC,fun _ => h⟩
    · exact ⟨0,le_rfl,fun h => (hk h).elim⟩
  choose B hB hbB using hb'
  choose C hC hbC using hc'
  intro k hk
  refine ⟨∑c : OrderedFinpartition k,C c.length*∏i,B (c.partSize i),?_,?_⟩
  · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hC _) (Finset.prod_nonneg (fun i _ => hB _)))
  · exact fun x => bounded_higher_composition f g hf hg B C hB hC hbB hbC k hk x
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_higher_bounds_comp
