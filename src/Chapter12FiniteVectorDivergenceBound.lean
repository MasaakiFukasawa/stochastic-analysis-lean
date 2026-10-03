import Chapter12FiniteVectorCoreRebasis
import Chapter12GaussianCoreMomentBound

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

/-- The printed dimension-free bound for every finite smooth H-valued
cylinder, with its original representation and the book's actual adjoint. -/
theorem finite_vector_divergence_bound {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D₀ : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D₀.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (p : ℕ) (hp : 1≤p) [Fact (1≤((2*p:ℕ):ℝ≥0∞))]
    (q : ℝ≥0∞) [Fact (1≤q)] [HolderConjugate ((2*p:ℕ):ℝ≥0∞) q] (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    {l : ℕ} (c : Fin l → SmoothCylinder H) (v : Fin l → H) :
    ∃ g : SmoothCylinder H,
      IsDivergence D₀ ((finiteVectorCylinderExpr c v).valueLp P W S hS hcore 2 (by simp))
        (g.valueLp P W S hS hcore 2 (by simp)) ∧
      ‖g.valueLp P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖≤
        (2*(2*p-1):ℕ)*∑ k : Fin (2*p+1),
          ‖(iteratedVectorCylinderExpr H (finiteVectorCylinderExpr c v) k).valueLp
            P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _)‖ := by
  obtain ⟨n,e,u,he,hrep⟩ := finite_vector_core_rebasis H P W S hS hcore c v
  obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore
    (2*p:ℕ) q (ENNReal.natCast_ne_top _) hq hdense
  refine ⟨(GaussianJet.divergence u).toCylinder e,?_,?_⟩
  · rw [hrep 2 (by simp)]
    exact gaussian_core_is_divergence H P W S hS hcore u e he D₀ hgraph
  · have hh := gaussian_core_high_moment_bound H P W S hS hcore u e he p hp
    have ho := vector_rebasis_all_derivatives H P W S hS hcore (finiteVectorCylinderExpr c v)
      (2*p:ℕ) (ENNReal.natCast_ne_top _) D hD u e (hrep _ (ENNReal.natCast_ne_top _))
    simpa only [ho] using hh

end Asakura.Chapter12
