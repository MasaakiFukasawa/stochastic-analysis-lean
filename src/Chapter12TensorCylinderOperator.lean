import Chapter12TensorLpSeparation
import Chapter12CylinderGraph

open MeasureTheory Set Filter ENNReal
open TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Hilbert-valued cylindrical functions have a closable tensor-valued
derivative, using exactly the scalar Gaussian integration-by-parts tests. -/
theorem tensor_Lp_operator_from_cylinder_pairs {Ω H E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SeparableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (value : ι → Lp E p P) (derivative : ι → Lp (CompletedHilbertTensor H E) p P)
    (tests : Set (Lp ℝ q P)) (htests : Dense tests)
    (B : tests → H → Lp ℝ q P)
    (hIBP : ∀ i (v : tests) h e,
      (∫ w,inner ℝ (hilbertPureTensor h e) (derivative i w)*v.val w ∂P)=
      ∫ w,inner ℝ e (value i w)*B v h w ∂P) :
    ∃ D : Lp E p P →ₗ.[ℝ] Lp (CompletedHilbertTensor H E) p P,
      D.graph=Submodule.span ℝ (range (fun i => (value i,derivative i))) ∧
      D.IsClosable ∧ ∀ i,(value i,derivative i)∈D.graph := by
  let pairing := (ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q
  let left : tests × H × E → Lp (CompletedHilbertTensor H E) p P →L[ℝ] ℝ := fun i =>
    (pairing.flip i.1.val).comp ((innerSL ℝ (hilbertPureTensor i.2.1 i.2.2)).compLpL p P)
  let right : tests × H × E → Lp E p P →L[ℝ] ℝ := fun i =>
    (pairing.flip (B i.1 i.2.1)).comp ((innerSL ℝ i.2.2).compLpL p P)
  have hl (i : tests × H × E) (u : Lp (CompletedHilbertTensor H E) p P) :
      left i u=∫ w,inner ℝ (hilbertPureTensor i.2.1 i.2.2) (u w)*i.1.val w ∂P := by
    change pairing ((innerSL ℝ _).compLp u) i.1.val=_
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(innerSL ℝ (hilbertPureTensor i.2.1 i.2.2)).coeFn_compLp u] with w hw
    rw [hw]
    rfl
  have hr (i : tests × H × E) (u : Lp E p P) :
      right i u=∫ w,inner ℝ i.2.2 (u w)*B i.1 i.2.1 w ∂P := by
    change pairing ((innerSL ℝ i.2.2).compLp u) (B i.1 i.2.1)=_
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(innerSL ℝ i.2.2).coeFn_compLp u] with w hw
    rw [hw]
    rfl
  apply operator_from_dual_pairs value derivative left right
  · intro i k
    rw [hl,hr]
    exact hIBP i k.1 k.2.1 k.2.2
  · intro u hu
    apply tensor_Lp_separated_by_pure_tests P p q tests htests u
    intro h e v hv
    simpa only [hl] using hu (⟨v,hv⟩,h,e)

end Asakura.Chapter12
