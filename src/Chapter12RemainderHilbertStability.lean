import Chapter12RemainderHilbertArray
import Chapter12PartitionArrayStability

open scoped ContDiff BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem remainder_hilbert_stability {N G E F : Type*} [Fintype N]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : G → E) (b : E → F) (k : ℕ) (z : G) (e : N → G)
    (A B C D : ℕ → ℝ) (hA : ∀j,0≤A j) (hB : ∀j,0≤B j)
    (hC : ∀j,0≤C j) (hD : ∀j,0≤D j) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀j,2≤j → j≤k → ‖iteratedFDeriv ℝ j b (g z)‖≤B j)
    (hab : ∀j,2≤j → j≤k → ‖iteratedFDeriv ℝ j b (f z)-iteratedFDeriv ℝ j b (g z)‖≤A j*ε)
    (hf : ∀j,0<j → j<k → Real.sqrt (∑a : Fin j → N,‖iteratedFDeriv ℝ j f z (e ∘ a)‖^2)≤C j)
    (hg : ∀j,0<j → j<k → Real.sqrt (∑a : Fin j → N,‖iteratedFDeriv ℝ j g z (e ∘ a)‖^2)≤C j)
    (hfg : ∀j,0<j → j<k → Real.sqrt (∑a : Fin j → N,
      ‖iteratedFDeriv ℝ j f z (e ∘ a)-iteratedFDeriv ℝ j g z (e ∘ a)‖^2)≤D j*ε) :
    Real.sqrt (∑a : Fin k → N,
      ‖higherChainRemainder f b k z (e ∘ a)-higherChainRemainder g b k z (e ∘ a)‖^2)≤
      ε*(∑c : OrderedFinpartition k with 2≤c.length,
        (A c.length*(∏i,C (c.partSize i))+
          ∑i,B c.length*(D (c.partSize i)*∏j∈Finset.univ.erase i,C (c.partSize j)))) := by
  classical
  let term := fun (h : G → E) (c : OrderedFinpartition k) (a : Fin k → N) =>
    iteratedFDeriv ℝ c.length b (h z)
      (fun i => iteratedFDeriv ℝ (c.partSize i) h z (e ∘ a ∘ c.emb i))
  have he (h : G → E) (a : Fin k → N) : higherChainRemainder h b k z (e ∘ a)=
      ∑c : OrderedFinpartition k with 2≤c.length,term h c a := by
    simp only [higherChainRemainder,ContinuousMultilinearMap.sum_apply,
      FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries,term]
    rfl
  simp_rw [he,←Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply (banach_array_norm_finset_sum (I:=Fin k → N) (E:=F) _ (fun c a => term f c a-term g c a)).trans
  apply Finset.sum_le_sum
  intro c hc
  have hc2 := (Finset.mem_filter.mp hc).2
  have hh := partition_array_stability c (iteratedFDeriv ℝ c.length b (f z)) (iteratedFDeriv ℝ c.length b (g z))
    (fun i a => iteratedFDeriv ℝ (c.partSize i) f z (e ∘ a))
    (fun i a => iteratedFDeriv ℝ (c.partSize i) g z (e ∘ a))
    (fun i => C (c.partSize i)) (fun i => D (c.partSize i)*ε)
    (fun i => hC _) (fun i => mul_nonneg (hD _) hε)
    (fun i => hf _ (c.partSize_pos i) (nonlinear_partition_lower_orders c hc2 i))
    (fun i => hg _ (c.partSize_pos i) (nonlinear_partition_lower_orders c hc2 i))
    (fun i => hfg _ (c.partSize_pos i) (nonlinear_partition_lower_orders c hc2 i))
  apply hh.trans
  calc
    _ ≤ (A c.length*ε)*(∏i,C (c.partSize i))+
        ∑i,B c.length*((D (c.partSize i)*ε)*∏j∈Finset.univ.erase i,C (c.partSize j)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (hab _ hc2 c.length_le) (Finset.prod_nonneg (fun i _ => hC _))
      · apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hb _ hc2 c.length_le)
          (mul_nonneg (mul_nonneg (hD _) hε) (Finset.prod_nonneg (fun j _ => hC _)))
    _ = _ := by
      rw [mul_add,Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i _
        ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.remainder_hilbert_stability
