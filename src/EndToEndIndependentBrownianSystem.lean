import EndToEndGaussianBrownianSystem

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The system required by the Ito construction is derived from two
independent Brownian motions on their original probability space. -/
noncomputable def independentBrownianSystem {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hcX : ∀ ω, Continuous (fun t => X t ω)) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (hI : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P) : BrownianSystem P 2 := by
  let Z : Fin 2 × ℝ≥0 → Ω → ℝ := fun q => if q.1=0 then X q.2 else Y q.2
  have hG : IsGaussianProcess Z P := by
    have h := (independent_gaussian_pair P X Y hX.isGaussianProcess hY.isGaussianProcess hI).comp_right
      (fun q : Fin 2 × ℝ≥0 => if q.1=0 then Sum.inl q.2 else Sum.inr q.2)
    convert h using 1
    funext q
    dsimp only [Z,Function.comp_def]
    split_ifs <;> rfl
  have hm q : Measurable (Z q) := by
    dsimp only [Z]
    split_ifs <;> first | exact hmX _ | exact hmY _
  have hc i ω : Continuous (fun t => Z (i,t) ω) := by
    dsimp only [Z]
    split_ifs <;> first | exact hcX ω | exact hcY ω
  have hz i : Z (i,0) =ᵐ[P] 0 := by
    dsimp only [Z]
    split_ifs <;> first | exact hX.eval_zero_ae_eq_zero | exact hY.eval_zero_ae_eq_zero
  have hmean q : (∫ ω, Z q ω ∂P) = 0 := by
    dsimp only [Z]
    split_ifs <;> first | exact hX.integral_eval _ | exact hY.integral_eval _
  have hcov (i j : Fin 2) (u v : ℝ≥0) : cov[Z (i,u), Z (j,v); P] =
      if i=j then ((min u v : ℝ≥0):ℝ) else 0 := by
    fin_cases i <;> fin_cases j
    · simpa [Z] using hX.covariance_eval u v
    · simpa [Z,Function.comp_def] using (hI.comp (measurable_pi_apply u) (measurable_pi_apply v)).covariance_eq_zero
        (hX.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
        (hY.isGaussianProcess.hasGaussianLaw_eval v).memLp_two
    · simpa [Z,Function.comp_def] using (hI.symm.comp (measurable_pi_apply u) (measurable_pi_apply v)).covariance_eq_zero
        (hY.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
        (hX.isGaussianProcess.hasGaussianLaw_eval v).memLp_two
    · simpa [Z] using hY.covariance_eval u v
  exact gaussianBrownianSystem P Z hG hm hc hz hmean hcov

theorem independentBrownianSystem_first {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hcX : ∀ ω, Continuous (fun t => X t ω)) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (hI : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (t : HalfClosedTime) (ω : Ω) :
    (independentBrownianSystem P X Y hX hY hmX hmY hcX hcY hI).W 0 t ω = X (halfTimeReal t) ω := rfl

theorem independentBrownianSystem_second {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hcX : ∀ ω, Continuous (fun t => X t ω)) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (hI : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (t : HalfClosedTime) (ω : Ω) :
    (independentBrownianSystem P X Y hX hY hmX hmY hcX hcY hI).W 1 t ω = Y (halfTimeReal t) ω := rfl

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.independentBrownianSystem
#print axioms Asakura.EndToEnd.independentBrownianSystem_first
#print axioms Asakura.EndToEnd.independentBrownianSystem_second
