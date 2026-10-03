import Chapter12DivergenceProductPairing
import Chapter12DivergenceRawCoreTests
import Chapter12ClosedProductRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3800000

/-- Product formula for the actual closed divergence. Holder assumptions
provide all L2 products; no bounded multiplier or assumed product-duality
formula is used. -/
theorem closed_divergence_product_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (q : ℝ≥0∞) [Fact (1≤q)] [ENNReal.HolderTriple q q 2] (hq : q≠⊤) (hq2 : 2≤q)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (G Z : Ω → ℝ) (DG U : Ω → H)
    (hG : MemLp G q P) (hZ : MemLp Z q P) (hDG : MemLp DG q P) (hU : MemLp U q P)
    (hGDG : (hG.toLp _,hDG.toLp _)∈Dq.graph)
    (hUZ : IsDivergence D ((hU.mono_exponent hq2).toLp _) ((hZ.mono_exponent hq2).toLp _)) :
    ∃ hi : MemLp (fun w => G w • U w) 2 P,
    ∃ hz : MemLp (fun w => G w*Z w-inner ℝ (DG w) (U w)) 2 P,
      IsDivergence D (hi.toLp _) (hz.toLp _) := by
  have hi : MemLp (fun w => G w • U w) 2 P := hG.smul hU
  have hGZ : MemLp (fun w => G w*Z w) 2 P := hG.mul hZ
  have hDU : MemLp (fun w => inner ℝ (DG w) (U w)) 2 P :=
    (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).memLp_of_bilin 2 hDG hU
  have hz := hGZ.sub hDU
  refine ⟨hi,hz,?_⟩
  apply divergence_of_raw_cylinder_tests P W S hS hcore D hg _ _ hi hz
  intro c
  have hcq : (c.valueLp P W S hS hcore q hq,c.gradientLp P W S hS hcore q hq)∈Dq.graph := by
    change cylinderPair P W S hS hcore q hq c∈(Dq.graph : Set _)
    rw [hgq]
    exact subset_closure (mem_range_self c)
  have hclosed : D.IsClosed := by
    change IsClosed (D.graph : Set (Lp ℝ 2 P × Lp H 2 P))
    rw [hg]
    exact isClosed_closure
  obtain ⟨hFG,hprod,hpair⟩ := closed_malliavin_product_raw P W S hS hcore 2 q (by simp) hq
    D Dq hclosed hg hgq (c.value P W) G (c.gradient P W) DG
    (c.value_memLp P W S hS hcore q hq) hG (c.gradient_memLp P W S hS hcore q hq) hDG hcq hGDG
  have hp := divergence_pairing_raw P D (fun w => c.value P W w*G w) Z
    (fun w => G w • c.gradient P W w+c.value P W w • DG w) U
    hFG (hZ.mono_exponent hq2) hprod (hU.mono_exponent hq2) hpair hUZ
  exact divergence_product_pairing P (c.value P W) G Z (c.gradient P W) DG U
    (c.value_memLp P W S hS hcore 2 (by simp)) (c.gradient_memLp P W S hS hcore 2 (by simp))
    hi hGZ hDU hp

end Asakura.Chapter12
