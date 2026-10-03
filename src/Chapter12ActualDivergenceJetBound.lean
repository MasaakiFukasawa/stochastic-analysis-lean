import Chapter12ActualDivergenceAllBounds
import Chapter12FiniteJetNormBound
import Chapter12ScalarSobolevSumJet

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000

theorem actual_divergence_finite_jet_bound {Ω : Type*} [MeasurableSpace Ω]
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
      (g.valueLp P W S hS hcore 2 (by simp))) (k : ℕ) :
    ‖scalarSobolevSumCoreJet H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) k g‖≤
      (k+1:ℕ)*((k:ℝ)+(2*(2*p-1):ℕ)*(2*p+1:ℕ))*
        ‖vectorSobolevCoreJet H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) (k+2*p) c‖ := by
  obtain ⟨hvalue,higher⟩ := vector_divergence_bounds_for_actual_output H P W S hS hcore
    D₀ hgraph p hp q hq hdense hd c g hg
  apply finite_jet_norm_bound (k:=k) (m:=2*p) _ _
    (vectorSobolevCoreJet H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) (k+2*p) c)
    (scalarSobolevSumCoreJet H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) k g)
    (2*(2*p-1):ℕ) (by positivity)
  · exact hvalue
  · intro r
    exact higher r.val

end Asakura.Chapter12
