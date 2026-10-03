import Chapter2ItoCharacterizedConstruction
import Chapter2ItoStoppedInterval
import Chapter2StochasticIntervalMembership

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construct both integrals from the original local martingale and local
square-energy hypotheses, then prove the stochastic-interval identity by
covariance separation. Existence of the stopped-interval integral is not
assumed. -/
theorem ito_stochastic_interval_constructed
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
    (hHm : ∀ ω, Measurable (fun r => H (ω,r)))
    (σ τ : Ω → ℝ) (hσ0 : ∀ ω, 0 ≤ σ ω) (hτ0 : ∀ ω, 0 ≤ τ ω)
    (hσT : ∀ ω, (σ ω:EReal) < T) (hτT : ∀ ω, (τ ω:EReal) < T)
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (σ ω) ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (τ ω) ≤ t}) :
    ∃ Y Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X H Y ∧
      ItoCovarianceFormula P F X
        (fun z => (Ioc (σ z.1) (τ z.1)).indicator (fun r => H (z.1,r)) z.2) Z ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        Z t ω = Y (min (realTimeClamp (τ ω)) t) ω - Y (min (realTimeClamp (σ ω)) t) ω) := by
  obtain ⟨Y,hY,hy⟩ := ito_integral_exists_with_covariance_characterization
    P hT F hF hle hnull X A hX hA c hc hcm hcT hct hcut hcc hAm hAc H hH hi
  let J := fun z : Ω × ℝ => (Ioc (σ z.1) (τ z.1)).indicator (fun r => H (z.1,r)) z.2
  have hJ n : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => J (z.1,z.2.val)) :=
    real_stochastic_interval_integrand_progressive F hF σ τ hσ0 hτ0 hσT hτT hσ hτ (c n) (hc n).le (hcT n) H (hH n)
  have hJi n : ∀ᵐ ω ∂P, Integrable (fun r => J (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure := by
    filter_upwards [hi n] with ω hiω
    exact square_integrable_interval_indicator _ _ hiω (σ ω) (τ ω)
  obtain ⟨Z,hZ,hz⟩ := ito_integral_exists_with_covariance_characterization
    P hT F hF hle hnull X A hX hA c hc hcm hcT hct hcut hcc hAm hAc J hJ hJi
  exact ⟨Y,Z,hY,hZ,hy,hz,ito_stochastic_interval_identity P hT F hF hle hnull X Y Z H
    hX hY hZ hHm σ τ hσ0 hτ0 hστ hσ hτ hy hz⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_stochastic_interval_constructed
