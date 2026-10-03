import Chapter12ScalarVectorCoreEstimate
import Chapter12ScalarVectorCoreValueEstimate
import Chapter12VectorJetSize

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem scalar_vector_core_uniform_estimate {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q r s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)] [Fact (1≤s)]
    [HolderConjugate p q] [HolderConjugate r s]
    (hp : p≠⊤) (hq : q≠⊤) (hr : r≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x:ℝ×H,‖iteratedFDeriv ℝ j (fun y:ℝ×H => y.1 • y.2) x‖≤K*(1+‖x‖)^a)
    (j : ℕ) (hjk : j≤k) : ∃C:ℝ,0≤C ∧ ∀f g : SmoothCylinder H,∀c d : VectorCylinderExpr H H,∀ᵐw ∂P,
      ‖((iteratedVectorCylinderExpr H (c.scalarProduct f) j).valueLp P W S hS hcore p hp-
        (iteratedVectorCylinderExpr H (d.scalarProduct g) j).valueLp P W S hS hcore p hp) w‖≤
        C*(1+cylinderJetSize H P W S hS hcore r hr f k w+cylinderJetSize H P W S hS hcore r hr g k w+vectorJetSize H P W S hS hcore r hr c k w+
          vectorJetSize H P W S hS hcore r hr d k w)^(a+k+1)*
          (cylinderJetDistance H P W S hS hcore r hr f g k w+vectorJetDistance H P W S hS hcore r hr c d k w) := by
  obtain ⟨C,hC,l,hl,hest⟩ : ∃C:ℝ,0≤C ∧ ∃l:ℕ,l≤a+k+1 ∧
      ∀f g : SmoothCylinder H,∀c d : VectorCylinderExpr H H,∀ᵐw ∂P,
      ‖((iteratedVectorCylinderExpr H (c.scalarProduct f) j).valueLp P W S hS hcore p hp-
        (iteratedVectorCylinderExpr H (d.scalarProduct g) j).valueLp P W S hS hcore p hp) w‖≤
        C*(1+cylinderJetSize H P W S hS hcore r hr f j w+cylinderJetSize H P W S hS hcore r hr g j w+vectorJetSize H P W S hS hcore r hr c j w+
          vectorJetSize H P W S hS hcore r hr d j w)^l*
          (cylinderJetDistance H P W S hS hcore r hr f g j w+vectorJetDistance H P W S hS hcore r hr c d j w) := by
    by_cases hj : j=0
    · subst j
      exact ⟨K,hK,a,by omega,fun f g c d => scalar_vector_core_value_estimate
        H P W S hS hcore p q r s hp hq hr hs hdq hds K hK a
        (fun i hi => hKB i (by omega)) f g c d⟩
    · exact ⟨(Fintype.card (OrderedFinpartition j):ℝ)*K*(j+1),by positivity,a+j,by omega,
        fun f g c d => scalar_vector_core_estimate H P W S hS hcore p q r s hp hq hr hs
        hdq hds j (Nat.pos_of_ne_zero hj) K hK a (fun i hi => hKB i (by omega)) f g c d⟩
  refine ⟨C,hC,fun f g c d => ?_⟩
  filter_upwards [hest f g c d] with w hw
  apply hw.trans
  have hf := cylinderJetSize_mono H P W S hS hcore r hr f hjk w
  have hg := cylinderJetSize_mono H P W S hS hcore r hr g hjk w
  have hc := vectorJetSize_mono H P W S hS hcore r hr c hjk w
  have hd := vectorJetSize_mono H P W S hS hcore r hr d hjk w
  have hδ := add_le_add (cylinderJetDistance_mono H P W S hS hcore r hr f g hjk w)
    (vectorJetDistance_mono H P W S hS hcore r hr c d hjk w)
  have hfn : 0≤cylinderJetSize H P W S hS hcore r hr f j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hgn : 0≤cylinderJetSize H P W S hS hcore r hr g j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcn : 0≤vectorJetSize H P W S hS hcore r hr c j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hdn : 0≤vectorJetSize H P W S hS hcore r hr d j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδn : 0≤cylinderJetDistance H P W S hS hcore r hr f g j w+vectorJetDistance H P W S hS hcore r hr c d j w :=
    add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  apply mul_le_mul _ hδ hδn
  · exact mul_nonneg hC (pow_nonneg (by linarith) _)
  · apply mul_le_mul_of_nonneg_left _ hC
    exact (pow_le_pow_left₀ (by linarith) (by linarith) l).trans
      (pow_le_pow_right₀ (by linarith) hl)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_vector_core_uniform_estimate
