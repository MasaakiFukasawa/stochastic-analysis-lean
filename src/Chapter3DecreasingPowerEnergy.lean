import Chapter3PositiveIntegralLower
import Chapter3BoundedItoMean
import Chapter3RegularizedWeightRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The decreasing-weight integral has finite stopped energy and the
quadratic-variation lower bound used by the reverse small-p BDG proof. -/
theorem decreasing_power_ito_energy_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A K Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (hKa : ∀ t, t < ⊤ → Measurable[F t] (K t))
    (hKc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => K s ω) t)
    (hKm : ∀ ω, MonotoneOn (fun t => K t ω) (Iio ⊤))
    (hKp : ∀ ω t, t < ⊤ → 0 ≤ K t ω)
    (α p : ℝ) (hα : 0 < α) (hp : 0 < p) (hp2 : p < 2)
    (hY : LocalMProcessWitness P F Y)
    (hy : ItoCovarianceFormula P F X (fun z => (α+K (realTimeClamp z.2) z.1)^(p/2-1)) Y)
    (b : ClosedTime T) (hb : b < ⊤) (M : ℝ) (hM : 0 ≤ M)
    (hAb : ∀ᵐ ω ∂P, A b ω ≤ M) :
    ∃ B : ClosedTime T → Ω → ℝ,
      LocalCovarianceWitness P F Y Y B ∧ ContinuousM2Witness P F (fun t ω => Y (min b t) ω) ∧
      Integrable (B b) P ∧ (∫ ω, B b ω ∂P) = (∫ ω, Y b ω^2 ∂P) ∧
      (∀ᵐ ω ∂P, (α+K b ω)^(p-2)*A b ω ≤ B b ω) := by
  let H := fun t ω => (α+K t ω)^(p/2-1)
  have hH := shifted_power_process_regularity F K hKa hKc hKp α (p/2-1) hα
  have hHb : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |H s ω| ≤ α^(p/2-1) := by
    apply Filter.Eventually.of_forall
    intro ω s hs
    have ht := hs.trans_lt hb
    rw [abs_of_nonneg (hH.2.2 ω s ht).le]
    exact Real.rpow_le_rpow_of_nonpos hα (by linarith [hKp ω s ht]) (by linarith)
  have hmean := bounded_continuous_ito_mean_zero P hT F hF hle hnull X A H Y hX hA hAm hAc hA0
    hH.1 hH.2.1 hY hy b hb M (α^(p/2-1)) hM (Real.rpow_nonneg hα.le _) hAb hHb
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,B,hIv,hIc,hI,hB,he⟩ := continuous_ito_energy_constructed P hT F hF hle hnull
    X A H Y hX hA hAm hAc hH.1 hH.2.1 hY hy c hc hcm hcT hct hcut hcc
  have hHr := open_process_real_regularity F (fun t ω => H t ω^2)
    (fun t ht => (hH.1 t ht).pow_const 2) (fun ω t ht => (hH.2.1 ω t ht).pow 2)
  have hlower := positive_variation_integral_lower_bound P A I (fun z => H (realTimeClamp z.2) z.1^2)
    (fun ω => (α+K b ω)^(p-2)) hAm hAc hHr.2 c (fun n => (hc n).le) hcT hcc hI b hb (by
      intro ω r hr hrT hrb
      have ht := hrb.trans_lt hb
      have hbase : 0 < α+K (realTimeClamp r) ω := by linarith [hKp ω _ ht]
      change (α+K b ω)^(p-2) ≤ ((α+K (realTimeClamp r) ω)^(p/2-1))^2
      rw [← Real.rpow_two,← Real.rpow_mul hbase.le]
      have he : (p/2-1)*2 = p-2 := by ring
      rw [he]
      exact Real.rpow_le_rpow_of_nonpos hbase (by linarith [hKm ω ht hb hrb]) (by linarith))
  have hstop t : MeasurableSet[F t] {ω : Ω | b ≤ t} := by
    by_cases h : b ≤ t <;> simp [h]
  have henergy := stopped_M2_energy P F hF hle hnull Y B hY hB (fun _ => b) hstop (fun _ => hb) hmean.1
  refine ⟨B,hB,hmean.1,henergy.1,henergy.2.symm,?_⟩
  filter_upwards [he,hlower] with ω heω hlω
  rw [heω b hb]
  simpa only [hA0 ω,sub_zero] using hlω

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.decreasing_power_ito_energy_bound
