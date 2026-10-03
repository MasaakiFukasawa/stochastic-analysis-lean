import Chapter12CylinderDirectionDivergence
import Chapter12LinearCylinder
import Chapter12DivergenceClosedGraph

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The product correction in the basket gamma and vega weights, on the
same closed Malliavin operator as the payoff derivative. -/
theorem wiener_linear_direction_divergence {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (u v : H) :
    ∃ (hi : MemLp (fun w => W u w • v) 2 P)
      (hz : MemLp (fun w => W u w*W v w-inner ℝ u v) 2 P),
      IsDivergence D (hi.toLp _) (hz.toLp _) := by
  let G := linearSmoothCylinder u
  obtain ⟨hi,hd⟩ := cylinder_direction_divergence P W S hS hcore D hg G v
  have he : G.ibpTest P W v=(fun w => W u w*W v w-inner ℝ u v) := by
    funext w
    dsimp only [SmoothCylinder.ibpTest,G]
    rw [linear_cylinder_gradient]
    rfl
  have hz : MemLp (fun w => W u w*W v w-inner ℝ u v) 2 P :=
    he ▸ G.ibpTest_memLp P W S hS hcore v 2 (by simp)
  have hze : hz.toLp _=G.ibpTestLp P W S hS hcore v 2 (by simp) := by
    apply Lp.ext
    filter_upwards [hz.coeFn_toLp,(G.ibpTest_memLp P W S hS hcore v 2 (by simp)).coeFn_toLp] with w h1 h2
    dsimp only [SmoothCylinder.ibpTestLp]
    rw [h1,h2,he]
  refine ⟨hi,hz,?_⟩
  rw [hze]
  exact hd

/-- Linearity and closedness extend verified elementary-integrand formulas
to the closure of their linear span. -/
theorem divergence_from_dense_span {E H A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (D : E →ₗ.[ℝ] H) (J : A →L[ℝ] H) (I : A →L[ℝ] E)
    (S : Set A) (hd : Dense (Submodule.span ℝ S : Set A))
    (hs : ∀ v∈S,IsDivergence D (J v) (I v)) :
    ∀ v,IsDivergence D (J v) (I v) := by
  let V : Submodule ℝ A := (divergenceGraph D).comap (J.prod I).toLinearMap
  have hV : IsClosed (V : Set A) := (divergence_graph_isClosed D).preimage (J.prod I).continuous
  have hsub : Submodule.span ℝ S≤V := Submodule.span_le.mpr hs
  exact hd.induction (fun v hv => hsub hv) hV

end Asakura.Chapter12
