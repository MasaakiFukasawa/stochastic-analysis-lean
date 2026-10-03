import Chapter8GibbsActualInvariance
import Chapter8PotentialDriftRegularity

open MeasureTheory Set
open scoped NNReal BigOperators ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxRecDepth 3000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's Gibbs invariance theorem, from its C3 and weighted
second-moment assumptions, with the actual SDE and invariant law constructed.
No ellipticity or convexity is needed. -/
theorem gibbs_manuscript_invariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (U : (Fin d → ℝ) → ℝ) (hU : ContDiff ℝ 3 U)
    (A₂ A₃ : ℝ≥0)
    (h₂ : ∀ x,‖fderiv ℝ (fderiv ℝ U) x‖≤(A₂:ℝ))
    (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ))
    (β : ℝ) (hβ : 0<β)
    (hi : Integrable (fun x : Fin d → ℝ => (1+∑ i,x i^2)*Real.exp (-β*U x)))
    (M : Fin d → Fin d → ℝ) (hM : ∀ i j,M i j=M j i)
    (σ : Fin d → Fin n → ℝ) (hσ : ∀ i j,∑ k,σ i k*σ j k=2*β⁻¹*M i j) :
    let π := volume.withDensity (fun x : Fin d → ℝ =>
      ENNReal.ofReal ((∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U x)))
    IsProbabilityMeasure π ∧
    ∃ Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ,
      (∀ x,VectorSDESolution P B.F B.W
        (fun i y => -(∑ j,M i j*fderiv ℝ U y (Pi.single j 1)))
        (fun i j _ => σ i j) (fun _ => x) (Z x)) ∧
      ∀ T : ℝ,0≤T → ∃ Y : (Fin d → ℝ) × Ω → (Fin d → ℝ),Measurable Y ∧
        (∀ x,(fun w => Y (x,w))=ᵐ[P] Z x (realTimeClamp T)) ∧ (π.prod P).map Y=π := by
  obtain ⟨b,D,D₂,C,L,Cg,hb,hd,hd₂,hc,hlip,hL,hDb,hCg,hgrad⟩ :=
    potential_drift_regularity U hU A₂ A₃ h₂ h₃ M
  have hUc : Continuous U := hU.continuous
  have hnorm : Integrable (fun x : Fin d → ℝ => (1+‖x‖^2)*Real.exp (-β*U x)) := by
    apply hi.mono' (by fun_prop)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (pi_norm_sq_le_sum_sq x)) (Real.exp_pos _).le
  have hh := gibbs_actual_invariance P B U (fderiv ℝ U)
    (fun x => (hU.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    (hU.continuous_fderiv (by norm_num)) β hβ.ne' hnorm M hM σ hσ b hb
    D D₂ hd hd₂ hc C L hlip hL hDb Cg hCg hgrad
  have hb' : (fun i y => b y i)=(fun i y => -(∑ j,M i j*fderiv ℝ U y (Pi.single j 1))) := by
    funext i y; exact hb y i
  rw [hb'] at hh
  exact hh

end Asakura.Chapter8
