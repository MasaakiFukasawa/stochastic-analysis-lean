import Chapter12GaussianClosedDerivativeDifference
import Chapter12ScalarJetOperatorsFromCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_all_jet_difference_norm {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    {N : ℕ} (f g : GaussianJet N) (e : Fin N → H) (he : Orthonormal ℝ e) (k : ℕ) :
    (fun w => ‖(cylinderJetCoordinate H P W S hS hcore p hp (f.toCylinder e) k-
      cylinderJetCoordinate H P W S hS hcore p hp (g.toCylinder e) k) w‖)=ᵐ[P]
      (fun w => Real.sqrt (∑a : Fin k → Fin N,
        ‖iteratedFDeriv ℝ k f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)-
          iteratedFDeriv ℝ k g.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)) := by
  cases k with
  | zero =>
    filter_upwards [Lp.coeFn_sub ((f.toCylinder e).valueLp P W S hS hcore p hp)
        ((g.toCylinder e).valueLp P W S hS hcore p hp),
      ((f.toCylinder e).value_memLp P W S hS hcore p hp).coeFn_toLp,
      ((g.toCylinder e).value_memLp P W S hS hcore p hp).coeFn_toLp] with w hw hf hg
    change ‖((f.toCylinder e).valueLp P W S hS hcore p hp-(g.toCylinder e).valueLp P W S hS hcore p hp) w‖=_
    rw [hw,Pi.sub_apply]
    change (f.toCylinder e).valueLp P W S hS hcore p hp w=_ at hf
    change (g.toCylinder e).valueLp P W S hS hcore p hp w=_ at hg
    rw [hf,hg]
    simp only [iteratedFDeriv_zero_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_fin,pow_zero,one_smul,Real.sqrt_sq (norm_nonneg _)]
    rfl
  | succ k =>
    obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore p q hp hq hdense
    exact gaussian_closed_derivative_difference H P W S hS hcore p hp f g e he D hD k
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_all_jet_difference_norm
