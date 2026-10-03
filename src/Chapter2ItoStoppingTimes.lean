import Chapter2ItoStoppedIntervalLocalDomain

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The original stopping-time-valued formulation; real coordinates are
constructed inside the proof, not required as additional hypotheses. -/
theorem ito_stochastic_interval_for_stopping_times
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (σ τ : Ω → ClosedTime T) (hσtop : ∀ ω, σ ω < ⊤) (hτtop : ∀ ω, τ ω < ⊤)
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    ∃ Y Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X H Y ∧
      ItoCovarianceFormula P F X
        (fun z => (Ioc (σ z.1) (τ z.1)).indicator (fun _ => H z) (realTimeClamp z.2)) Z ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        Z t ω = Y (min (τ ω) t) ω - Y (min (σ ω) t) ω) := by
  choose s hs0 hsT hse using (fun ω => finite_closed_time_real (σ ω) (hσtop ω))
  choose v hv0 hvT hve using (fun ω => finite_closed_time_real (τ ω) (hτtop ω))
  have hsv ω : s ω ≤ v ω := by
    have hh := hστ ω
    rw [← hse ω,← hve ω] at hh
    change (realTimeClamp (s ω):EReal) ≤ (realTimeClamp (v ω):EReal) at hh
    rw [real_time_clamp_eq _ (hs0 ω) (hsT ω).le,real_time_clamp_eq _ (hv0 ω) (hvT ω).le] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hss t : MeasurableSet[F t] {ω | realTimeClamp (s ω) ≤ t} := by
    simpa only [hse] using hσ t
  have hvs t : MeasurableSet[F t] {ω | realTimeClamp (v ω) ≤ t} := by
    simpa only [hve] using hτ t
  obtain ⟨Y,Z,hY,hZ,hy,hz,hstop⟩ := ito_stochastic_interval_without_external_measurability
    P hT F hF hle hnull X A hX hA c hc hcm hcT hct hcut hcc hAm hAc H hH hi
    s v hs0 hv0 hsT hvT hsv hss hvs
  refine ⟨Y,Z,hY,hZ,hy,?_,?_⟩
  · apply hz.congr_on_time_domain P F X Z
    intro ω r hr hrT
    have hmem : r ∈ Ioc (s ω) (v ω) ↔ realTimeClamp r ∈ Ioc (σ ω) (τ ω) := by
      rw [← hse ω,← hve ω]
      change (s ω < r ∧ r ≤ v ω) ↔
        ((realTimeClamp (s ω):EReal) < (realTimeClamp r:EReal) ∧
          (realTimeClamp r:EReal) ≤ (realTimeClamp (v ω):EReal))
      rw [real_time_clamp_eq _ (hs0 ω) (hsT ω).le,real_time_clamp_eq _ hr hrT.le,
        real_time_clamp_eq _ (hv0 ω) (hvT ω).le]
      simp only [EReal.coe_lt_coe_iff,EReal.coe_le_coe_iff]
    by_cases hh : r ∈ Ioc (s ω) (v ω)
    · simp only [indicator_of_mem hh,indicator_of_mem (hmem.mp hh)]
    · simp only [indicator_of_notMem hh,indicator_of_notMem (fun hm => hh (hmem.mpr hm))]
  · simpa only [hse,hve] using hstop

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_stochastic_interval_for_stopping_times
