import Chapter12CompletedHilbertTensor

open UniformSpace Set TopologicalSpace
open scoped TensorProduct
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The Hilbert tensor completion has a countable dense set when its
factors do, allowing a single exceptional null set for directional tests. -/
theorem completed_hilbert_tensor_separable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [SeparableSpace F] :
    SeparableSpace (CompletedHilbertTensor E F) := by
  let V := Submodule.span ℝ (range (fun x : E × F => hilbertPureTensor x.1 x.2))
  have ha (v : E ⊗[ℝ] F) : (v : CompletedHilbertTensor E F)∈V := by
    induction v using TensorProduct.induction_on with
    | zero => rw [Completion.coe_zero]; exact V.zero_mem
    | tmul e f => exact Submodule.subset_span (mem_range_self (e,f))
    | add a b ha hb => rw [Completion.coe_add]; exact V.add_mem ha hb
  have hd : Dense (V : Set (CompletedHilbertTensor E F)) :=
    Completion.denseRange_coe.mono (by rintro _ ⟨v,rfl⟩; exact ha v)
  have hc : Continuous (fun x : E × F => hilbertPureTensor x.1 x.2) :=
    (Completion.continuous_coe (E ⊗[ℝ] F)).comp TensorProduct.continuous_tmul
  have hs := (isSeparable_range hc).span (R := ℝ) |>.closure
  change IsSeparable (closure (V : Set (CompletedHilbertTensor E F))) at hs
  rw [hd.closure_eq] at hs
  exact isSeparable_univ_iff.mp hs

end Asakura.Chapter12
