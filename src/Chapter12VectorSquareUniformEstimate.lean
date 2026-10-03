import Chapter12VectorSquareExplicitEstimate
import Chapter12VectorSquareValueEstimate
import Chapter12VectorJetSize

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem vector_square_uniform_estimate {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q r s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)] [Fact (1≤s)]
    [HolderConjugate p q] [HolderConjugate r s]
    (hp : p≠⊤) (hq : q≠⊤) (hr : r≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x,‖iteratedFDeriv ℝ j (fun y:H => ‖y‖^2) x‖≤K*(1+‖x‖)^a)
    (j : ℕ) (hjk : j≤k) : ∃C:ℝ,0≤C ∧ ∀c d : VectorCylinderExpr H H,∀f g : SmoothCylinder H,
      f.value P W=ᵐ[P] (fun w => ‖c.rawValue P W w‖^2) →
      g.value P W=ᵐ[P] (fun w => ‖d.rawValue P W w‖^2) → ∀ᵐw ∂P,
      ‖(cylinderJetCoordinate H P W S hS hcore p hp f j-
        cylinderJetCoordinate H P W S hS hcore p hp g j) w‖≤
        C*(1+vectorJetSize H P W S hS hcore r hr c k w+
          vectorJetSize H P W S hS hcore r hr d k w)^(a+k+1)*
          vectorJetDistance H P W S hS hcore r hr c d k w := by
  obtain ⟨C,hC,l,hl,hest⟩ : ∃C:ℝ,0≤C ∧ ∃l:ℕ,l≤a+k+1 ∧
      ∀c d : VectorCylinderExpr H H,∀f g : SmoothCylinder H,
      f.value P W=ᵐ[P] (fun w => ‖c.rawValue P W w‖^2) →
      g.value P W=ᵐ[P] (fun w => ‖d.rawValue P W w‖^2) → ∀ᵐw ∂P,
      ‖(cylinderJetCoordinate H P W S hS hcore p hp f j-
        cylinderJetCoordinate H P W S hS hcore p hp g j) w‖≤
        C*(1+vectorJetSize H P W S hS hcore r hr c j w+
          vectorJetSize H P W S hS hcore r hr d j w)^l*
          vectorJetDistance H P W S hS hcore r hr c d j w := by
    by_cases hj : j=0
    · subst j
      exact ⟨K,hK,a,by omega,fun c d f g hf hg => vector_square_value_estimate
        H P W S hS hcore p q r s hp hq hr hs hdq hds K hK a
        (fun i hi => hKB i (by omega)) c d f g hf hg⟩
    · exact ⟨(Fintype.card (OrderedFinpartition j):ℝ)*K*(j+1),by positivity,a+j,by omega,
        fun c d f g hf hg => vector_square_explicit_estimate H P W S hS hcore p q r s hp hq hr hs
        hdq hds j (Nat.pos_of_ne_zero hj) K hK a (fun i hi => hKB i (by omega)) c d f g hf hg⟩
  refine ⟨C,hC,fun c d f g hf hg => ?_⟩
  filter_upwards [hest c d f g hf hg] with w hw
  apply hw.trans
  have hc := vectorJetSize_mono H P W S hS hcore r hr c hjk w
  have hd := vectorJetSize_mono H P W S hS hcore r hr d hjk w
  have hδ := vectorJetDistance_mono H P W S hS hcore r hr c d hjk w
  have hcn : 0≤vectorJetSize H P W S hS hcore r hr c j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hdn : 0≤vectorJetSize H P W S hS hcore r hr d j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδn : 0≤vectorJetDistance H P W S hS hcore r hr c d j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply mul_le_mul _ hδ hδn
  · exact mul_nonneg hC (pow_nonneg (by linarith) _)
  · apply mul_le_mul_of_nonneg_left _ hC
    exact (pow_le_pow_left₀ (by linarith) (by linarith) l).trans
      (pow_le_pow_right₀ (by linarith) hl)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_square_uniform_estimate
