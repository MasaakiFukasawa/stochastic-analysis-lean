import FullAuditBrownianFutureTest

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written

/-- Every rounded future test is measurable by countable time fibers. -/
theorem rounded_future_test_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable[m] (B t))
    (F : ℝ≥0 → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (τ : Ω → ℝ≥0) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (J : Finset ℝ≥0) (h : (J → ℝ) → ℝ) (hh : Continuous h) (n : ℕ) :
    Measurable[m] (fun ω => h (finiteFuture B J (ceilTime n (ceilIndex n (τ ω))) ω)) := by
  have hκ : Measurable[m] (fun ω => ceilIndex n (τ ω)) :=
    measurable_of_Iic fun k => hle (ceilTime n k) _ (ceil_index_stopping F τ hτ n k)
  exact measurable_countable_evaluation _ hκ (Set.to_countable _) _
    (fun k _ => hh.measurable.comp (finite_future_measurable B hm J (ceilTime n k)))

theorem stopping_future_test_tendsto {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (J : Finset ℝ≥0) (h : (J → ℝ) → ℝ) (hh : Continuous h) (ω : Ω) :
    Tendsto (fun n => h (finiteFuture B J (ceilTime n (ceilIndex n (τ ω))) ω)) atTop
      (𝓝 (h (finiteFuture B J (τ ω) ω))) :=
  (hh.comp (finite_future_continuous B hc J ω)).continuousAt.tendsto.comp (ceil_time_tendsto (τ ω))

theorem stopping_future_test_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : ℝ≥0 → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (τ : Ω → ℝ≥0) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (J : Finset ℝ≥0) (h : (J → ℝ) → ℝ) (hh : Continuous h) :
    Measurable[m] (fun ω => h (finiteFuture B J (τ ω) ω)) := by
  apply measurable_of_tendsto_metrizable (rounded_future_test_measurable B hm F hle τ hτ J h hh)
  exact tendsto_pi_nhds.mpr (stopping_future_test_tendsto B hc τ J h hh)

/-- The manuscript's entire ceiling approximation, countable sum and dominated
convergence argument, for every bounded continuous finite-dimensional test. -/
theorem brownian_strong_markov_test_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[Asakura.nullAugmentation P (pastSigma B t)] {ω | τ ω ≤ t})
    (J : Finset ℝ≥0) (h : (J → ℝ) → ℝ) (hh : Continuous h)
    (C : ℝ) (hb : ∀ x, ‖h x‖ ≤ C)
    (A : Set Ω) (hA : MeasurableSet[writtenStoppedSpace m
      (fun t => Asakura.nullAugmentation P (pastSigma B t)) τ hτ] A) :
    (∫ ω in A, h (finiteFuture B J (τ ω) ω) ∂P) =
      ∫ _ in A, (∫ x, h x ∂BrownianReal.projectiveFamily J) ∂P := by
  let F : ℝ≥0 → MeasurableSpace Ω := fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)
  have hF : Monotone F := fun s t hst => null_augmentation_mono P (past_sigma_mono B hst)
  have hle : ∀ t, F t ≤ m := fun t E hE => hE.1
  let c := ∫ x, h x ∂BrownianReal.projectiveFamily J
  have hn (n : ℕ) :
      (∫ ω in A, h (finiteFuture B J (ceilTime n (ceilIndex n (τ ω))) ω) ∂P) = ∫ _ in A, c ∂P := by
    exact countable_future_test_integral P (fun k => F (ceilTime n k))
      (hF.comp (ceil_time_mono n)) (fun k => hle _) (fun ω => ceilIndex n (τ ω))
      (ceil_index_stopping F τ hτ n) (fun k ω => h (finiteFuture B J (ceilTime n k) ω))
      (fun k => hh.measurable.comp (finite_future_measurable B hm J _)) C c
      (fun k ω => hb _) (fun k => brownian_future_test_conditional P B hB hm J _ h hh C hb)
      A (ceil_stopped_event m F τ hτ A hA n)
  have ht : Tendsto (fun n => ∫ ω in A, h (finiteFuture B J (ceilTime n (ceilIndex n (τ ω))) ω) ∂P)
      atTop (𝓝 (∫ ω in A, h (finiteFuture B J (τ ω) ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (rounded_future_test_measurable B hm F hle τ hτ J h hh n).aestronglyMeasurable
    · exact integrable_const C
    · intro n
      exact ae_of_all _ fun ω => hb _
    · exact ae_of_all _ (stopping_future_test_tendsto B hc τ J h hh)
  have htconst : Tendsto (fun n => ∫ ω in A, h (finiteFuture B J (ceilTime n (ceilIndex n (τ ω))) ω) ∂P)
      atTop (𝓝 (∫ _ in A, c ∂P)) := by
    simpa only [hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ _ in A, c ∂P) atTop (𝓝 _))
  exact tendsto_nhds_unique ht htconst
end Asakura.FullAudit
