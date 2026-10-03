import Chapter3ItoVariationEnergy
import Chapter3IncreasingAdaptedVariation
import Chapter2ContinuousVariationAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- For a continuous adapted integrand, construct its H² variation integral
and identify it with the actual Ito quadratic variation. No energy formula
or integrability assumption is added to continuity. -/
theorem continuous_ito_energy_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A H Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) :
    ∃ I B : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F I ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => I s ω) t) ∧
      VariationIntegralFormula P c (fun n => (hc n).le) A
        (fun z => H (realTimeClamp z.2) z.1^2) I ∧
      LocalCovarianceWitness P F Y Y B ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → B t ω = I t ω) := by
  let G := fun z : Ω × ℝ => H (realTimeClamp z.2) z.1
  have hAv := continuous_increasing_adapted_variation hT F hF A (hA.adapted P F hX hX) hAm hAc
  have hGm (r : ℝ) (hr : 0 ≤ r) (hrT : (r:EReal) < T) :
      Measurable[F (realTimeClamp r)] (fun ω => G (ω,r)) := by
    apply hHm
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr hrT.le]
    exact hrT
  have hGc (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T) ω : ContinuousOn (fun r => G (ω,r)) (Icc 0 b) := by
    intro r hr
    have hrt : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r : EReal) < T
      rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hbT.le)]
      exact (EReal.coe_le_coe hr.2).trans_lt hbT
    exact ((hHc ω _ hrt).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  obtain ⟨I,hIv,hIc,hI⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc A hAv hAc (fun z => G z^2)
    (fun r hr hrT => (hGm r hr hrT).pow_const 2)
    (fun b hb hbT ω => (hGc b hb hbT ω).pow 2)
  have hreg n := regular_covariance_on_real_intervals A hAm hAc (c n) (hc n).le (hcT n)
  have hp n := continuous_adapted_real_progressive F hF G (c n) (hc n).le
    (fun r hr => hGm r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hGc (c n) (hc n).le (hcT n))
  have hi n : ∀ᵐ ω ∂P, Integrable (fun r => G (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) ((hreg n).1 ω)
        (fun r hr => ((hreg n).2 ω r hr).mono inter_subset_left)).measure := by
    apply Filter.Eventually.of_forall
    intro ω
    let μ := (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) ((hreg n).1 ω)
      (fun r hr => ((hreg n).2 ω r hr).mono inter_subset_left)).measure
    letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
    exact continuous_integrable_compact_support μ 0 (c n) _ ((hGc (c n) (hc n).le (hcT n) ω).pow 2)
      ((interval_stieltjes_ae_mem_Ioc _ _ _ _ _ _).mono (fun r hr => ⟨hr.1.le,hr.2⟩))
  obtain ⟨B,hB,he⟩ := ito_energy_identified_with_variation_integral P hT F hF hle hnull
    X A hX hA c hc hcm hcT hct hcut hcc (fun n => (hreg n).1) (fun n => (hreg n).2)
    G hp hi Y hY hYI I hIc hI
  exact ⟨I,B,hIv,hIc,hI,hB,he⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_ito_energy_constructed
