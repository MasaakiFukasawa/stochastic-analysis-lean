import Chapter12CylinderCauchyCompletion
import Chapter12DerivativeCauchyCriterion

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem cylinder_derivative_limit {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (c : ℕ → SmoothCylinder H) (f : Lp ℝ p P)
    (hf : Tendsto (fun n => (c n).valueLp P W S hS hcore p hp) atTop (𝓝 f))
    {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (hv : CauchySeq v)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hb : ∀j:ℕ,1≤j → ∃C:ℝ,0≤C ∧ ∀n m,
      ‖cylinderJetCoordinate H P W S hS hcore p hp (c n) j-
        cylinderJetCoordinate H P W S hS hcore p hp (c m) j‖≤
        C*(‖v n-v m‖+r n+r m)) :
    ∀k:ℕ,∃x : malliavinSobolevJetSpace H P W S hS hcore p hp k,x.val 0=f := by
  intro k
  apply cylinder_cauchy_jet_limit H P W S hS hcore p hp k c _ f hf
  intro j
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact hf.cauchySeq
  | succ j =>
    obtain ⟨C,hC,hbC⟩ := hb (j+1) (by omega)
    exact derivative_cauchy_criterion _ v hv r hr C hC hbC
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_derivative_limit
