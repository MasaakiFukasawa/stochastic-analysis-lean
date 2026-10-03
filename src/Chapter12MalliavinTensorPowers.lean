import Chapter12HilbertTensorSeparable

open UniformSpace TopologicalSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Complete, separable real Hilbert spaces, bundled to construct all
orders of the derivative value space without circular instance assumptions. -/
structure RealHilbertSpaceData where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℝ carrier]
  [complete : CompleteSpace carrier]
  [separable : SeparableSpace carrier]

attribute [instance] RealHilbertSpaceData.normed RealHilbertSpaceData.inner
  RealHilbertSpaceData.complete RealHilbertSpaceData.separable

instance : CoeSort RealHilbertSpaceData Type := ⟨RealHilbertSpaceData.carrier⟩

noncomputable def hilbertTensorData (H E : RealHilbertSpaceData) : RealHilbertSpaceData where
  carrier := CompletedHilbertTensor H E
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  separable := completed_hilbert_tensor_separable

/-- Index n denotes H^{⊗(n+1)}. Order zero of a Sobolev jet is the scalar
value and is kept separately, matching the manuscript's norm. -/
noncomputable def positiveMalliavinTensorPower (H : RealHilbertSpaceData) : ℕ → RealHilbertSpaceData
  | 0 => H
  | n+1 => hilbertTensorData H (positiveMalliavinTensorPower H n)

example (H : RealHilbertSpaceData) (n : ℕ) : CompleteSpace (positiveMalliavinTensorPower H n) := inferInstance
example (H : RealHilbertSpaceData) (n : ℕ) : SeparableSpace (positiveMalliavinTensorPower H n) := inferInstance

end Asakura.Chapter12
