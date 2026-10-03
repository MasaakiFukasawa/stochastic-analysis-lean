import Chapter12CylinderDirectionDivergence
import Chapter12DivergenceClosedGraph
import Chapter12LpInclusion
import Chapter12LinearCylinder
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Extension of delta(G h)=G W(h)-<DG,h> from cylinders to the closed
Lq graph, with Holder providing the required L2 convergence. -/
theorem closed_direction_divergence {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [ENNReal.HolderTriple q q 2] (hq : q ≠ ⊤) (hq2 : 2 ≤ q)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F : Lp ℝ q P) (U : Lp H q P) (hFU : (F,U) ∈ Dq.graph) (h : H) :
    IsDivergence D
      ((ContinuousLinearMap.toSpanSingleton ℝ h).compLp (probabilityLpInclusion P 2 q hq2 F))
      ((ContinuousLinearMap.mul ℝ ℝ).holderL P q q 2 F
        ((linearSmoothCylinder h).valueLp P W S hS hcore q hq) -
        (innerSL ℝ h).compLp (probabilityLpInclusion P 2 q hq2 U)) := by
  let J := probabilityLpInclusion (E := ℝ) P 2 q hq2
  let K := probabilityLpInclusion (E := H) P 2 q hq2
  let A := ContinuousLinearMap.toSpanSingleton ℝ h
  let L := innerSL ℝ h
  let B := (ContinuousLinearMap.mul ℝ ℝ).holderL P q q 2
  let wh := (linearSmoothCylinder h).valueLp P W S hS hcore q hq
  let Φ := fun z : Lp ℝ q P × Lp H q P =>
    (A.compLp (J z.1),B z.1 wh-L.compLp (K z.2))
  have hΦ : Continuous Φ :=
    ((A.compLpL 2 P).continuous.comp (J.continuous.comp continuous_fst)).prodMk
      ((B.continuous₂.comp (continuous_fst.prodMk continuous_const)).sub
        ((L.compLpL 2 P).continuous.comp (K.continuous.comp continuous_snd)))
  have hc (c : SmoothCylinder H) : Φ (cylinderPair P W S hS hcore q hq c) ∈
      (divergenceGraph D : Set _) := by
    obtain ⟨hi,hd⟩ := cylinder_direction_divergence P W S hS hcore D hg c h
    have hv : A.compLp (J (c.valueLp P W S hS hcore q hq)) = hi.toLp _ := by
      apply Lp.ext
      filter_upwards [A.coeFn_compLp (J (c.valueLp P W S hS hcore q hq)),
        probabilityLpInclusion_coe P 2 q hq2 (c.valueLp P W S hS hcore q hq),
        (c.value_memLp P W S hS hcore q hq).coeFn_toLp,hi.coeFn_toLp] with w h1 h2 h3 h4
      rw [h1,h4]
      change (J (c.valueLp P W S hS hcore q hq) w) • h = _
      rw [h2]
      dsimp only [SmoothCylinder.valueLp]
      rw [h3]
    have hz : B (c.valueLp P W S hS hcore q hq) wh-
        L.compLp (K (c.gradientLp P W S hS hcore q hq)) = c.ibpTestLp P W S hS hcore h 2 (by simp) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (B (c.valueLp P W S hS hcore q hq) wh)
          (L.compLp (K (c.gradientLp P W S hS hcore q hq))),
        (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (c.valueLp P W S hS hcore q hq) wh,
        L.coeFn_compLp (K (c.gradientLp P W S hS hcore q hq)),
        probabilityLpInclusion_coe P 2 q hq2 (c.gradientLp P W S hS hcore q hq),
        (c.value_memLp P W S hS hcore q hq).coeFn_toLp,
        (c.gradient_memLp P W S hS hcore q hq).coeFn_toLp,
        ((linearSmoothCylinder h).value_memLp P W S hS hcore q hq).coeFn_toLp,
        (c.ibpTest_memLp P W S hS hcore h 2 (by simp)).coeFn_toLp] with w h1 h2 h3 h4 h5 h6 h7 h8
      rw [h1,Pi.sub_apply]
      simp only [B,ContinuousLinearMap.holderL_apply_apply]
      rw [h2]
      dsimp only [SmoothCylinder.valueLp]
      rw [h3]
      change c.valueLp P W S hS hcore q hq w * wh w - inner ℝ h
        (K (c.gradientLp P W S hS hcore q hq) w) = _
      rw [h4]
      dsimp only [wh,SmoothCylinder.valueLp,SmoothCylinder.gradientLp,SmoothCylinder.ibpTestLp]
      rw [h5,h6,h7,h8]
      simp only [SmoothCylinder.ibpTest,linear_cylinder_value]
      rw [real_inner_comm h]
    change IsDivergence D (A.compLp (J (c.valueLp P W S hS hcore q hq)))
      (B (c.valueLp P W S hS hcore q hq) wh-L.compLp (K (c.gradientLp P W S hS hcore q hq)))
    rwa [hv,hz]
  have hs : closure (range (cylinderPair P W S hS hcore q hq)) ⊆
      Φ ⁻¹' (divergenceGraph D : Set _) := by
    apply closure_minimal
    · rintro _ ⟨c,rfl⟩
      exact hc c
    · exact (divergence_graph_isClosed D).preimage hΦ
  have hz : (F,U) ∈ closure (range (cylinderPair P W S hS hcore q hq)) := by rwa [←hgq]
  exact hs hz

end Asakura.Chapter12
