import Chapter12VectorCylinderSquare

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianVectorScalarProjection {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N:ℕ} (u:Fin N → GaussianJet N) (e:Fin N → H) (h:H) : GaussianJet N :=
  GaussianJet.finsetSum Finset.univ (fun i => (u i).smul (inner ℝ h (e i)))

theorem gaussianVectorScalarProjection_value {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N:ℕ} (u:Fin N → GaussianJet N) (e:Fin N → H) (h:H) (x:Fin N → ℝ) :
    (gaussianVectorScalarProjection u e h).f x=inner ℝ h (gaussianVectorFunction u e x) := by
  simp only [gaussianVectorScalarProjection,GaussianJet.finsetSum,GaussianJet.smul,
    gaussianVectorFunction,inner_sum,inner_smul_right,mul_comm]

theorem scalar_from_vector_frame {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (c:SmoothCylinder H) (h:H) (hh:‖h‖=1)
    {N:ℕ} (u:Fin N → GaussianJet N) (e:Fin N → H)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
    (hc:(VectorCylinderExpr.term c h).valueLp P W S hS hcore p hp=
      gaussianTensorCore H P W S hS hcore p hp u e 0) :
    c.value P W=ᵐ[P] ((gaussianVectorScalarProjection u e h).toCylinder e).value P W := by
  have hr := vector_rebased_raw_value H P W S hS hcore (.term c h) u e p hp hc
  filter_upwards [hr] with w hw
  change c.value P W w • h=gaussianVectorFunction u e (fun i => W (e i) w) at hw
  change _=(gaussianVectorScalarProjection u e h).f (fun i => W (e i) w)
  rw [gaussianVectorScalarProjection_value,←hw,inner_smul_right,real_inner_self_eq_norm_sq,hh,one_pow,mul_one]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_from_vector_frame
