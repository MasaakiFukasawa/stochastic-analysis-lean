import Chapter2ConstructedStochasticFubini
import Chapter2StochasticFubiniProcesses
import Chapter2ItoConstructionChoices

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
universe u
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- From the chapter's local martingale and filtration hypotheses alone,
construct the quadratic variation, the time exhaustion, the global energy
measure, and an Ito isometry satisfying stochastic Fubini for actual
processes. All construction choices are existential conclusions. -/
theorem stochastic_fubini_from_local_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    ∃ (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (A : ClosedTime T → Ω → ℝ)
      (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
      (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
      (ν : Measure (Ω × ℝ)),
      LocalCovarianceWitness P F X X A ∧ SigmaFinite ν ∧ StrictMono c ∧
      (∀ n, (c n:EReal) < T) ∧
      (∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) ∧
      (∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
          ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
            (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P) ∧
      ∃ L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F,
      ∀ (E : Type u) [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
        (H : E × (Ω × ℝ) → ℝ), Measurable H →
        (∀ n, @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) (c n)) => H (z.1,(z.2.1,z.2.2.val)))) →
        (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞ →
    (∀ᵐ z ∂ν, Integrable (fun x => H (x,z)) μ) ∧
    ∃ Z : E → continuousM2Terminal P F, Integrable Z μ ∧
      (∀ᵐ x ∂μ, ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
        ItoCovarianceFormula P F X (fun z => H (x,z)) Y ∧ Z x = m2TerminalOfProcess P F Y hY) ∧
      ∃ Ybar : ClosedTime T → Ω → ℝ, ∃ hYbar : ContinuousM2Witness P F Ybar,
        ItoCovarianceFormula P F X (fun z => ∫ x, H (x,z) ∂μ) Ybar ∧
        (∫ x, Z x ∂μ) = m2TerminalOfProcess P F Ybar hYbar := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨A,hA,hm,hcont,h0,hAmr⟩ := quadratic_variation_measurable_encoding P hT F hF hle hnull X hX
  have hAm n := (regular_covariance_on_real_intervals A hm hcont (c n) (hc n).le (hcT n)).1
  have hAc n := (regular_covariance_on_real_intervals A hm hcont (c n) (hc n).le (hcT n)).2
  obtain ⟨ν,hν,henergy⟩ := global_stieltjes_energy_identity P c (fun n => (hc n).le) hcm.monotone
    (fun ω r => A (realTimeClamp r) ω) hAm hAc hAmr
  letI : SigmaFinite ν := hν
  obtain ⟨L,hIto⟩ := actual_ito_l2_isometry_constructed P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc hAmr ν henergy
  refine ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,?_⟩
  intro E mE μ hμ H hH hp hN
  exact stochastic_fubini_actual_processes P F hF hle hnull X c μ ν L hIto H hH hp hN

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stochastic_fubini_from_local_martingale
