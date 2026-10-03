import Chapter2StochasticFubiniTimeDomain
import Chapter13FubiniEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Finite-parameter square-energy form of the stochastic Fubini theorem.
This connects the localized HJM energy estimate to actual M2-valued integrals. -/
theorem finite_parameter_stochastic_fubini
    {Ω : Type} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
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
      ∀ (E : Type) [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
        (H : E × (Ω × ℝ) → ℝ),
        (∀ n, @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) (c n)) => H (z.1,(z.2.1,z.2.2.val)))) →
        Measurable H → Integrable (fun z => H z^2) (μ.prod ν) →
    (∀ᵐ z ∂ν, Integrable (fun x => H (x,z)) μ) ∧
    ∃ Z : E → continuousM2Terminal P F, Integrable Z μ ∧
      (∀ᵐ x ∂μ, ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
        ItoCovarianceFormula P F X (fun z => H (x,z)) Y ∧ Z x = m2TerminalOfProcess P F Y hY) ∧
      ∃ Ybar : ClosedTime T → Ω → ℝ, ∃ hYbar : ContinuousM2Witness P F Ybar,
        ItoCovarianceFormula P F X (fun z => ∫ x, H (x,z) ∂μ) Ybar ∧
        (∫ x, Z x ∂μ) = m2TerminalOfProcess P F Ybar hYbar := by
  obtain ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,hmain⟩ :=
    stochastic_fubini_on_time_domain P hT F hF hle hnull X hX
  letI : SigmaFinite ν := hν
  refine ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,?_⟩
  intro E mE μ hμ H hp hm hi
  exact hmain E μ H hp (finite_parameter_fubini_energy μ ν H hm hi).1
end Asakura.Chapter13
#print axioms Asakura.Chapter13.finite_parameter_stochastic_fubini
