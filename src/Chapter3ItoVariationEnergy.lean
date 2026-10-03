import Chapter3ItoAllTimeEnergy
import Chapter3PositiveVariationIntegral
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Identify the actual quadratic variation of an Ito integral with the
already constructed signed Stieltjes integral of H². -/
theorem ito_energy_identified_with_variation_integral
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
    (Y : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X H Y)
    (I : ClosedTime T → Ω → ℝ)
    (hIc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => I s ω) t)
    (hI : VariationIntegralFormula P c (fun n => (hc n).le) A (fun z => H z^2) I) :
    ∃ B : ClosedTime T → Ω → ℝ, LocalCovarianceWitness P F Y Y B ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ → B t ω = I t ω := by
  obtain ⟨B,hB,henergy⟩ := ito_covariance_formula_all_time_energy P hT F hF hle hnull
    X A hX hA c hc hcm hcT hct hcut hcc hAm hAc H hH hi Y hY hYI
  have he t (ht : t < ⊤) : B t =ᵐ[P] I t := by
    obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
    obtain ⟨j,hj⟩ := hcc (realTimeClamp d) ht
    have hdj : d ≤ c j := by
      change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
      rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
      exact (EReal.coe_lt_coe_iff.mp hj).le
    obtain ⟨hmA,hcontA,hbe⟩ := henergy j d hd hdj
    have hie := positive_variation_integral_at_time P A I (fun z => H z^2) c (fun n => (hc n).le)
      hcT hAm hAc hI j d hd hdj hmA hcontA
    exact hbe.trans hie.symm
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have hcommon := continuous_process_common_time_equality P
    (fun t : Iio (⊤ : ClosedTime T) => B t.val)
    (fun t : Iio (⊤ : ClosedTime T) => I t.val)
    (hB.continuous_open_paths P F Y Y B hY hY)
    (fun ω => continuous_iff_continuousAt.mpr (fun t =>
      (hIc ω t.val t.property).comp continuous_subtype_val.continuousAt))
    (fun t => he t.val t.property)
  exact ⟨B,hB,hcommon.mono (fun ω hω t ht => hω ⟨t,ht⟩)⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_energy_identified_with_variation_integral
