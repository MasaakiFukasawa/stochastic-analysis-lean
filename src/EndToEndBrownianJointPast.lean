import EndToEndIndependentGaussianPair
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.EndToEnd

/-- For the identity Brownian covariance, the entire vector increment is
independent of the entire joint past, not just of each past coordinate. -/
theorem gaussian_brownian_increment_independent_joint_past
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι × ℝ≥0 → Ω → ℝ) (hZ : IsGaussianProcess Z P)
    (hcov : ∀ i j u v, cov[Z (i,u), Z (j,v); P] =
      if i = j then ((min u v : ℝ≥0) : ℝ) else 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (fun ω i => Z (i,t) ω - Z (i,s) ω)
      (fun ω (q : ι × Iic s) => Z (q.1,q.2.val) ω) P := by
  classical
  have hG : IsGaussianProcess
      (Sum.elim (fun i ω => Z (i,t) ω - Z (i,s) ω)
        (fun (q : ι × Iic s) ω => Z (q.1,q.2.val) ω)) P := by
    apply hZ.of_isGaussianProcess
    intro q
    cases q with
    | inl i =>
      refine ⟨{(i,t),(i,s)},
        ContinuousLinearMap.proj ⟨(i,t), by simp⟩ -
          ContinuousLinearMap.proj ⟨(i,s), by simp⟩, ?_⟩
      intro ω
      rfl
    | inr q =>
      refine ⟨{(q.1,q.2.val)}, ContinuousLinearMap.proj ⟨(q.1,q.2.val), by simp⟩, ?_⟩
      intro ω
      rfl
  apply hG.indepFun_of_covariance_eq_zero
    (fun i => (hZ.aemeasurable (i,t)).sub (hZ.aemeasurable (i,s)))
    (fun q => hZ.aemeasurable (q.1,q.2.val))
  intro i q
  rw [covariance_fun_sub_left (hZ.hasGaussianLaw_eval (i,t)).memLp_two
    (hZ.hasGaussianLaw_eval (i,s)).memLp_two
    (hZ.hasGaussianLaw_eval (q.1,q.2.val)).memLp_two, hcov, hcov]
  have hrs : q.2.val ≤ s := q.2.property
  simp only [min_eq_right hrs, min_eq_right (hrs.trans hst), sub_self]

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.gaussian_brownian_increment_independent_joint_past
