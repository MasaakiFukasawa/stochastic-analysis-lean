import Chapter2ItoStoppedIntervalConstruction
import Chapter2ProgressivePathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Stop-interval integration under the manuscript's local progressive
measurability, with no assumption about H outside the time domain. -/
theorem ito_stochastic_interval_without_external_measurability
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
  obtain ⟨G,hGm,hGe⟩ := progressive_paths_measurable_encoding F c (fun n => (hc n).le) H hH
  have he (ω : Ω) (r : ℝ) (hr : 0 ≤ r) (hrT : (r:EReal) < T) : G (ω,r) = H (ω,r) := by
    have hrt : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r:EReal) < T
      rw [real_time_clamp_eq r hr hrT.le]
      exact hrT
    obtain ⟨n,hn⟩ := hcc _ hrt
    have hrn : r ≤ c n := by
      change (realTimeClamp r:EReal) < (realTimeClamp (c n):EReal) at hn
      rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
      exact (EReal.coe_lt_coe_iff.mp hn).le
    exact hGe n ω r ⟨hr,hrn⟩
  have hGp n : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)) := by
    have heq : (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)) =
        (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)) :=
      funext (fun z => hGe n z.1 z.2.val z.2.property)
    rw [heq]; exact hH n
  have hGi n : ∀ᵐ ω ∂P, Integrable (fun r => G (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure := by
    filter_upwards [hi n] with ω hiω
    apply hiω.congr
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 (c n) (hc n).le
      (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)] with r hr
    rw [hGe n ω r ⟨hr.1.le,hr.2⟩]
  obtain ⟨Y,Z,hY,hZ,hy,hz,hstop⟩ := ito_stochastic_interval_constructed P hT F hF hle hnull
    X A hX hA c hc hcm hcT hct hcut hcc hAm hAc G hGp hGi hGm
    σ τ hσ0 hτ0 hσT hτT hστ hσ hτ
  refine ⟨Y,Z,hY,hZ,hy.congr_on_time_domain P F X Y G H he,?_,hstop⟩
  apply hz.congr_on_time_domain P F X Z
  intro ω r hr hrT
  by_cases hmem : r ∈ Ioc (σ ω) (τ ω)
  · simp only [indicator_of_mem hmem]
    exact he ω r hr hrT
  · simp only [indicator_of_notMem hmem]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_stochastic_interval_without_external_measurability
