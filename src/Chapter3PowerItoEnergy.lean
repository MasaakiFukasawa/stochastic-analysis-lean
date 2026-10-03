import Chapter3ContinuousItoEnergy
import Chapter3PowerStieltjesEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The actual unregularized Ito integral in the p>2 BDG argument has the displayed energy.
This constructs the variation integral and proves its value from the C¹
chain rule, rather than assuming the quadratic-variation identity. -/
theorem power_ito_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 2 < p)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X
      (fun z => (A (realTimeClamp z.2) z.1)^((p-2)/4)) Y) :
    ∃ B : ClosedTime T → Ω → ℝ, LocalCovarianceWitness P F Y Y B ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        B t ω = (2/p)*A t ω^(p/2) := by
  have hAp ω t (ht : t < ⊤) : 0 ≤ A t ω := by
    rw [← hA0 ω]
    exact hAm ω hT ht bot_le
  let H := fun t ω => (A t ω)^((p-2)/4)
  have hr : 0 ≤ (p-2)/4 := by linarith
  have hHm t (ht : t < ⊤) : Measurable[F t] (H t) :=
    (Real.continuous_rpow_const hr).measurable.comp (hA.adapted P F hX hX t ht)
  have hHc ω t (ht : t < ⊤) : ContinuousAt (fun s => H s ω) t :=
    (hAc ω t ht).rpow_const (Or.inr hr)
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,B,hIv,hIc,hI,hB,he⟩ := continuous_ito_energy_constructed P hT F hF hle hnull
    X A H Y hX hA hAm hAc hHm hHc hY hYI c hc hcm hcT hct hcut hcc
  have hI' : VariationIntegralFormula P c (fun n => (hc n).le) A
      (fun z => (A (realTimeClamp z.2) z.1)^(p/2-1)) I := by
    apply variation_integral_integrand_congr_on_domain P A I _ _ c (fun n => (hc n).le) hcT hI
    apply Filter.Eventually.of_forall
    intro ω r hr hrT
    have hrt : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r : EReal) < T
      rw [real_time_clamp_eq r hr hrT.le]
      exact hrT
    have hbase : 0 ≤ A (realTimeClamp r) ω := hAp ω _ hrt
    change ((A (realTimeClamp r) ω)^((p-2)/4))^2 = _
    rw [← Real.rpow_two,← Real.rpow_mul hbase]
    congr 1
    ring
  have hAv := continuous_increasing_adapted_variation hT F hF A (hA.adapted P F hX hX) hAm hAc
  have heI := power_stieltjes_energy_identity P hT F hF hle A I hAv hAc
    (Filter.Eventually.of_forall hA0) p hp c (fun n => (hc n).le) hcT hcc hI'
  refine ⟨B,hB,?_⟩
  filter_upwards [he,heI] with ω hb hi
  intro t ht
  exact (hb t ht).trans (hi t ht)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.power_ito_energy
