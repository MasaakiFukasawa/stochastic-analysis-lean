import FullAuditFinitePastIndependence

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace Asakura.FullAudit
open Asakura.Chapter1Written

/-- Finite-dimensional conditional laws at the stopping time, obtained by
bounded continuous measure uniqueness after the written approximation proof. -/
theorem brownian_strong_markov_finite_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[Asakura.nullAugmentation P (pastSigma B t)] {ω | τ ω ≤ t})
    (J : Finset ℝ≥0) :
    let G := writtenStoppedSpace m (fun t => Asakura.nullAugmentation P (pastSigma B t)) τ hτ
    HasLaw (fun ω => finiteFuture B J (τ ω) ω) (BrownianReal.projectiveFamily J) P ∧
      Indep (MeasurableSpace.comap (fun ω => finiteFuture B J (τ ω) ω) inferInstance) G P := by
  dsimp only
  let F := fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)
  have hle : ∀ t, F t ≤ m := fun t E hE => hE.1
  have hX : Measurable[m] (fun ω => finiteFuture B J (τ ω) ω) := by
    apply Measurable.of_eval
    intro j
    exact stopping_future_test_measurable B hm hc F hle τ hτ J (fun x => x j) (continuous_apply j)
  apply independent_law_of_restricted_laws _ P _ (fun A (hA : MeasurableSet[writtenStoppedSpace m F τ hτ] A) => hA.1) _ hX
  intro A hA
  apply restricted_law_of_continuous_tests P _ _ hX A hA.1
  intro f
  exact brownian_strong_markov_test_written P B hB hm hc τ hτ J f f.continuous ‖f‖
    (fun x => f.norm_coe_le_norm x) A hA

/-- The complete strong Markov assertion: the shifted process is a continuous
standard Brownian motion and its entire coordinate sigma algebra is independent
of the stopped sigma algebra. The initial state cancels in the increments. -/
theorem brownian_strong_markov_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[Asakura.nullAugmentation P (pastSigma B t)] {ω | τ ω ≤ t}) :
    let X := fun t ω => B (τ ω+t) ω-B (τ ω) ω
    let G := writtenStoppedSpace m (fun t => Asakura.nullAugmentation P (pastSigma B t)) τ hτ
    IsPreBrownianReal X P ∧ (∀ ω, Continuous (fun t => X t ω)) ∧
      Indep (MeasurableSpace.comap (fun ω t => X t ω) inferInstance) G P := by
  dsimp only
  let X := fun t ω => B (τ ω+t) ω-B (τ ω) ω
  let F := fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)
  have hle : ∀ t, F t ≤ m := fun t E hE => hE.1
  have hfinite := brownian_strong_markov_finite_written P B hB hm hc τ hτ
  refine ⟨⟨fun J => (hfinite J).1⟩,?_,?_⟩
  · intro ω
    exact ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  · refine process_independent_of_finite_coordinates _ P X ?_ (fun A (hA : MeasurableSet[writtenStoppedSpace m F τ hτ] A) => hA.1) ?_
    · intro t
      let J : Finset ℝ≥0 := {t}
      have htest := stopping_future_test_measurable B hm hc F hle τ hτ J
        (fun x => x ⟨t,Finset.mem_singleton_self t⟩) (continuous_apply _)
      exact htest
    · intro J
      exact (hfinite J).2
end Asakura.FullAudit
