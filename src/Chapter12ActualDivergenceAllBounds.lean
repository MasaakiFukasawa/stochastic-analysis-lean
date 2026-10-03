import Chapter12VectorDivergenceAllBounds
import Chapter12ScalarJetOperatorsFromCore
import Chapter12CylinderExponentEquality

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

theorem vector_divergence_bounds_for_actual_output {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D₀ : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D₀.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (p : ℕ) (hp : 0<p) [Fact (1≤((2*p:ℕ):ℝ≥0∞))]
    (q : ℝ≥0∞) [Fact (1≤q)] [HolderConjugate ((2*p:ℕ):ℝ≥0∞) q] (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hd : DenseRange (fun f : D₀.domain => (f : Lp ℝ 2 P)))
    (c : VectorCylinderExpr H H) (g : SmoothCylinder H)
    (hg : IsDivergence D₀ (c.valueLp P W S hS hcore 2 (by simp))
      (g.valueLp P W S hS hcore 2 (by simp))) :
      ‖g.valueLp P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖≤
        (2*(2*p-1):ℕ)*∑ j : Fin (2*p+1),
          ‖(iteratedVectorCylinderExpr H c j).valueLp P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ ∧
      ∀ k : ℕ,
      ‖(iteratedCylinderExpr H g k).valueLp P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖≤
        (k+1:ℕ)*‖(iteratedVectorCylinderExpr H c k).valueLp
          P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖+
        (2*(2*p-1):ℕ)*∑ j : Fin (2*p+1),
          ‖(iteratedVectorCylinderExpr H c (j.val+(k+1))).valueLp
            P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ := by
  obtain ⟨g₁,hg₁,hvalue,higher⟩ := vector_divergence_all_bounds H P W S hS hcore D₀ hgraph p hp q hq hdense c
  have he2 := divergence_unique D₀ hd hg hg₁
  have hep := cylinder_value_equality_all_exponents P W S hS hcore g g₁ 2 (2*p:ℕ)
    (by simp) (ENNReal.natCast_ne_top _) he2
  have hejet := scalar_jet_core_unique H P W S hS hcore (2*p:ℕ) q
    (ENNReal.natCast_ne_top _) hq hdense g g₁ hep
  refine ⟨?_,fun k => ?_⟩
  · simpa only [hep] using hvalue
  · have hek := hejet (k+1)
    change (iteratedCylinderExpr H g k).valueLp P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)=
      (iteratedCylinderExpr H g₁ k).valueLp P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) at hek
    simpa only [hek] using higher k

end Asakura.Chapter12
