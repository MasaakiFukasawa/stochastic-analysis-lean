import Chapter12CylinderCompositionExplicitEstimate
import Chapter12CylinderValueCompositionEstimate
import Chapter12CylinderJetSizeMonotone

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem cylinder_composition_uniform_estimate {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q r s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤r)] [Fact (1≤s)]
    [HolderConjugate p q] [HolderConjugate r s]
    (hp : p≠⊤) (hq : q≠⊤) (hr : r≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hB : ∀j:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ j b x‖≤C*(1+‖x‖)^a)
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x,‖iteratedFDeriv ℝ j b x‖≤K*(1+‖x‖)^a)
    (j : ℕ) (hjk : j≤k) : ∃C:ℝ,0≤C ∧ ∀c d : SmoothCylinder H,∀ᵐw ∂P,
      ‖(cylinderJetCoordinate H P W S hS hcore p hp (composeSmoothCylinder c b hb hB) j-
        cylinderJetCoordinate H P W S hS hcore p hp (composeSmoothCylinder d b hb hB) j) w‖≤
        C*(1+cylinderJetSize H P W S hS hcore r hr c k w+
          cylinderJetSize H P W S hS hcore r hr d k w)^(a+k+1)*
          cylinderJetDistance H P W S hS hcore r hr c d k w := by
  obtain ⟨C,hC,l,hl,hest⟩ : ∃C:ℝ,0≤C ∧ ∃l:ℕ,l≤a+k+1 ∧
      ∀c d : SmoothCylinder H,∀ᵐw ∂P,
      ‖(cylinderJetCoordinate H P W S hS hcore p hp (composeSmoothCylinder c b hb hB) j-
        cylinderJetCoordinate H P W S hS hcore p hp (composeSmoothCylinder d b hb hB) j) w‖≤
        C*(1+cylinderJetSize H P W S hS hcore r hr c j w+
          cylinderJetSize H P W S hS hcore r hr d j w)^l*
          cylinderJetDistance H P W S hS hcore r hr c d j w := by
    by_cases hj : j=0
    · subst j
      exact ⟨K,hK,a,by omega,fun c d => cylinder_value_composition_explicit_estimate
        H P W S hS hcore p q r s hp hq hr hs hdq hds b hb hB K hK a
        (fun i hi => hKB i (by omega)) c d⟩
    · exact ⟨(Fintype.card (OrderedFinpartition j):ℝ)*K*(j+1),by positivity,a+j,by omega,
        fun c d => cylinder_composition_explicit_estimate H P W S hS hcore p q r s hp hq hr hs
        hdq hds b hb hB j (Nat.pos_of_ne_zero hj) K hK a (fun i hi => hKB i (by omega)) c d⟩
  refine ⟨C,hC,fun c d => ?_⟩
  filter_upwards [hest c d] with w hw
  apply hw.trans
  have hc := cylinderJetSize_mono H P W S hS hcore r hr c hjk w
  have hd := cylinderJetSize_mono H P W S hS hcore r hr d hjk w
  have hδ := cylinderJetDistance_mono H P W S hS hcore r hr c d hjk w
  have hcn : 0≤cylinderJetSize H P W S hS hcore r hr c j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hdn : 0≤cylinderJetSize H P W S hS hcore r hr d j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hδn : 0≤cylinderJetDistance H P W S hS hcore r hr c d j w := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply mul_le_mul _ hδ hδn
  · exact mul_nonneg hC (pow_nonneg (by linarith) _)
  · apply mul_le_mul_of_nonneg_left _ hC
    exact (pow_le_pow_left₀ (by linarith) (by linarith) l).trans
      (pow_le_pow_right₀ (by linarith) hl)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_composition_uniform_estimate
