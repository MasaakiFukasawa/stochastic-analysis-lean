import Chapter2FiniteHorizonEnergy
import Chapter2ItoConstructionChoices
import Chapter2M2CovarianceL1Bound

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Every finite horizon of the constructed Stieltjes energy is dominated
by its global energy, including horizons outside the chosen exhaustion. -/
theorem global_stieltjes_finite_horizon_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν : Measure (Ω × ℝ))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (A ω) (Icc 0 (c n)))
    (hν : ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
        ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω)
          (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P)
    (d : ℝ) (hd : 0 ≤ d) (n : ℕ) (hdn : d ≤ c n)
    (hAd : ∀ ω, MonotoneOn (A ω) (Icc 0 d))
    (hAcd : ∀ ω, ContinuousOn (A ω) (Icc 0 d)) :
    ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ ω, ∫⁻ r, f (ω,r) ∂(intervalStieltjes 0 d hd (A ω) (hAd ω)
        (fun r hr => (hAcd ω r hr).mono inter_subset_left)).measure ∂P) ≤ ∫⁻ z, f z ∂ν := by
  intro f hf
  rw [hν f hf]
  apply lintegral_mono
  intro ω
  have he := interval_stieltjes_restrict_Iic 0 (c n) d hd hdn (A ω) (hA n ω)
    (fun r hr => (hAc n ω r hr).mono inter_subset_left) (hAd ω)
    (fun r hr => (hAcd ω r hr).mono inter_subset_left)
  dsimp only
  rw [he]
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    (le_iSup (fun j => ∫⁻ r, f (ω,r) ∂(intervalStieltjes 0 (c j) (hc j) (A ω) (hA j ω)
      (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure) n)

/-- The finite Stieltjes mass of an M2 test process is integrable, as
required by the KW/Fubini estimate. -/
theorem m2_quadratic_stieltjes_mass_integrable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Y B : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (hY2 : ContinuousM2Witness P F Y) (hB : LocalCovarianceWitness P F Y Y B)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hBm : ∀ ω, MonotoneOn (fun r => B (realTimeClamp r) ω) (Icc 0 d))
    (hBc : ∀ ω, ContinuousOn (fun r => B (realTimeClamp r) ω) (Icc 0 d)) :
    Integrable (fun ω => (intervalStieltjes 0 d hd (fun r => B (realTimeClamp r) ω)
      (hBm ω) (fun r hr => (hBc ω r hr).mono inter_subset_left)).measure.real univ) P := by
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  have hstop : ∀ s, MeasurableSet[F s] {ω : Ω | realTimeClamp (T := T) d ≤ s} := by
    intro s
    by_cases hs : realTimeClamp (T := T) d ≤ s <;> simp [hs]
  obtain ⟨hi,_⟩ := stopped_M2_energy P F hF hle hnull Y B hY hB
    (fun _ => realTimeClamp d) hstop (fun _ => hdt)
    (continuous_m2_stopped P F hF hle Y hY2 (fun _ => realTimeClamp d) hstop)
  apply hi.congr
  filter_upwards [local_quadratic_variation_initial P F Y B hY hB] with ω h0
  rw [Measure.real,interval_stieltjes_total_mass 0 d hd (fun ω r => B (realTimeClamp r) ω)
    hBm (fun ω r hr => (hBc ω r hr).mono inter_subset_left)]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hBm ω (left_mem_Icc.mpr hd) (right_mem_Icc.mpr hd) hd))]
  have hz : realTimeClamp (T := T) 0 = ⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T := T) 0 : EReal) = 0
    simpa only [EReal.coe_zero] using (real_time_clamp_eq (T := T) 0 le_rfl
      (by simpa only [EReal.coe_zero] using (show (0:EReal) ≤ T from Fact.out)))
  simp only [hz,h0,Pi.zero_apply,sub_zero]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.global_stieltjes_finite_horizon_domination
#print axioms Asakura.Chapter2Complete.m2_quadratic_stieltjes_mass_integrable
