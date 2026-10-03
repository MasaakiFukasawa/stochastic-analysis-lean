import Chapter3ContinuousItoEnergy
import Chapter3IncreasingIntegralBound
import Chapter3BDGTwo

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Bounded continuous integrands and bounded quadratic variation give the
zero-mean Ito term needed when taking expectations in Ito's formula. -/
theorem bounded_continuous_ito_mean_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A H Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (hHa : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (b : ClosedTime T) (hb : b < ⊤) (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hAb : ∀ᵐ ω ∂P, A b ω ≤ K)
    (hHb : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |H s ω| ≤ L) :
    ContinuousM2Witness P F (fun t ω => Y (min b t) ω) ∧ (∫ ω, Y b ω ∂P) = 0 := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,B,hIv,hIc,hI,hB,he⟩ := continuous_ito_energy_constructed P hT F hF hle hnull
    X A H Y hX hA hAm hAc hHa hHc hY hYI c hc hcm hcT hct hcut hcc
  have hAv := continuous_increasing_adapted_variation hT F hF A (hA.adapted P F hX hX) hAm hAc
  have hIb := increasing_variation_integral_bound P hT F hF hle A (fun t ω => H t ω^2) I hAv hAm
    (fun t ht => (hHa t ht).pow_const 2) (fun ω t ht => (hHc ω t ht).pow 2)
    c (fun n => (hc n).le) hcT hcc hI
  have hbound : ∀ᵐ ω ∂P, |B b ω| ≤ L^2*K := by
    filter_upwards [he,hIb,hAb,hHb] with ω heω hiω haω hhω
    rw [heω b hb]
    have hsq : ∀ s, s ≤ b → |H s ω^2| ≤ L^2 := by
      intro s hs
      rw [abs_of_nonneg (sq_nonneg _)]
      have h := (sq_le_sq₀ (abs_nonneg (H s ω)) hL).mpr (hhω s hs)
      simpa only [sq_abs] using h
    have hi := hiω b hb (L^2) (sq_nonneg L) hsq
    rw [hA0 ω,sub_zero] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left haω (sq_nonneg L))
  have hBi : Integrable (B b) P := by
    apply (integrable_const (L^2*K)).mono'
      ((hB.adapted P F hY hY b hb).mono (hle b) le_rfl).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hbound
  have hstop t : MeasurableSet[F t] {ω : Ω | b ≤ t} := by
    by_cases h : b ≤ t <;> simp [h]
  have hm := (stopped_local_M2_equivalences P F hF hle hnull Y B hY hB
    (fun _ => b) hstop (fun _ => hb)).2.mp
      ((stopped_local_M2_equivalences P F hF hle hnull Y B hY hB
        (fun _ => b) hstop (fun _ => hb)).1.mp hBi)
  refine ⟨hm,?_⟩
  have hmean := integral_congr_ae ((hm.martingale ⊥ ⊤ le_top).trans hm.initial)
  rw [integral_condExp (hle ⊥)] at hmean
  simpa only [min_top_right,Pi.zero_apply,integral_zero] using hmean

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_continuous_ito_mean_zero
