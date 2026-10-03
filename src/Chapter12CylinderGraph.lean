import Chapter12LpClosability

open MeasureTheory Set Filter ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A family of cylinder values and derivatives defines a linear operator
on their linear span. Duality proves single-valuedness and closability;
no boundedness of the derivative is assumed. -/
theorem operator_from_dual_pairs
    {E F ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (value : ι → E) (derivative : ι → F)
    (left : κ → F →L[ℝ] ℝ) (right : κ → E →L[ℝ] ℝ)
    (hdual : ∀ i k, left k (derivative i) = right k (value i))
    (hsep : ∀ y, (∀ k, left k y = 0) → y = 0) :
    ∃ D : E →ₗ.[ℝ] F,
      D.graph = Submodule.span ℝ (range (fun i => (value i,derivative i))) ∧
      D.IsClosable ∧ ∀ i, (value i,derivative i) ∈ D.graph := by
  let G := Submodule.span ℝ (range (fun i => (value i,derivative i)))
  have hG : ∀ z ∈ G, ∀ k, left k z.2 = right k z.1 := by
    intro z hz k
    let L : E × F →L[ℝ] ℝ := (left k).comp (ContinuousLinearMap.snd ℝ E F)-
      (right k).comp (ContinuousLinearMap.fst ℝ E F)
    have hs : G ≤ LinearMap.ker L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change left k (derivative i)-right k (value i) = 0
      exact sub_eq_zero.mpr (hdual i k)
    have he := hs hz
    change left k z.2-right k z.1 = 0 at he
    exact sub_eq_zero.mp he
  have hg : G.toLinearPMap.graph = G := by
    apply Submodule.toLinearPMap_graph_eq
    intro z hz hz0
    apply hsep
    intro k
    simpa only [hz0,map_zero] using hG z hz k
  refine ⟨G.toLinearPMap,hg,?_,?_⟩
  · apply closable_of_duality G.toLinearPMap left right
    · intro k x
      have hx := G.toLinearPMap.mem_graph x
      rw [hg] at hx
      exact hG _ hx k
    · exact hsep
  · intro i
    rw [hg]
    exact Submodule.subset_span (mem_range_self i)

/-- In the actual Lp spaces, dense scalar cylinder tests give all separation
needed for the cylinder graph construction. -/
theorem Lp_operator_from_cylinder_pairs {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (value : ι → Lp ℝ p P) (derivative : ι → Lp H p P)
    (tests : Set (Lp ℝ q P)) (htests : Dense tests)
    (B : tests → H → Lp ℝ q P)
    (hIBP : ∀ i (v : tests) h,
      ∫ w, (inner ℝ h (derivative i w))*v.val w ∂P =
      ∫ w, value i w*B v h w ∂P) :
    ∃ D : Lp ℝ p P →ₗ.[ℝ] Lp H p P,
      D.graph = Submodule.span ℝ (range (fun i => (value i,derivative i))) ∧
      D.IsClosable ∧ ∀ i, (value i,derivative i) ∈ D.graph := by
  let pairing := (ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q
  let left : tests × H → Lp H p P →L[ℝ] ℝ := fun i =>
    (pairing.flip i.1.val).comp ((innerSL ℝ i.2).compLpL p P)
  let right : tests × H → Lp ℝ p P →L[ℝ] ℝ := fun i => pairing.flip (B i.1 i.2)
  have hleft (i : tests × H) (u : Lp H p P) :
      left i u = ∫ w, (inner ℝ i.2 (u w))*i.1.val w ∂P := by
    change pairing ((innerSL ℝ i.2).compLp u) i.1.val = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(innerSL ℝ i.2).coeFn_compLp u] with w hw
    rw [hw]; rfl
  apply operator_from_dual_pairs value derivative left right
  · intro i k
    rw [hleft]
    change _ = pairing (value i) (B k.1 k.2)
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    exact hIBP i k.1 k.2
  · intro u hu
    apply hilbert_Lp_separated_by_dense_tests P p q tests htests u
    intro h v hv
    simpa only [hleft] using hu (⟨v,hv⟩,h)

end Asakura.Chapter12
