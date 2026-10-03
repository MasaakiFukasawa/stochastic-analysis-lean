import Chapter2StochasticFubiniPrinted
import Chapter2ParameterProgressiveEncoding
import Chapter2EnergyPrefixSupport
import Chapter2ItoIntegrandEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The stochastic Fubini theorem with only the manuscript's product
progressiveness; an ambient measurable extension is constructed internally. -/
theorem stochastic_fubini_on_time_domain
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
      ∀ (E : Type) [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
        (H : E × (Ω × ℝ) → ℝ),
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
  obtain ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,hmain⟩ :=
    stochastic_fubini_printed_proof P hT F hF hle hnull X hX
  letI : SigmaFinite ν := hν
  letI : CompleteSpace (continuousM2Terminal P F) := continuous_m2_hilbert_complete P F hF hle hnull
  refine ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,?_⟩
  intro E mE μ hμ H hp hN
  obtain ⟨G,hG,hGe⟩ := parameter_progressive_measurable_encoding F hle c (fun n => (hc n).le) H hp
  have he (x : E) (ω : Ω) (r : ℝ) (hr : 0 ≤ r) (hrT : (r:EReal) < T) :
      G (x,(ω,r)) = H (x,(ω,r)) := by
    have hrt : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r:EReal) < T
      rw [real_time_clamp_eq r hr hrT.le]
      exact hrT
    obtain ⟨n,hn⟩ := hcc _ hrt
    have hrn : r ≤ c n := by
      change (realTimeClamp r:EReal) < (realTimeClamp (c n):EReal) at hn
      rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
      exact (EReal.coe_lt_coe_iff.mp hn).le
    exact hGe n x ω r ⟨hr,hrn⟩
  have hs : ∀ᵐ z ∂ν, ∃ n, z.2 ∈ Icc 0 (c n) := by
    apply energy_measure_ae_prefix P ν
      (fun n ω => (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure) c _ henergy
    intro n ω
    exact (interval_stieltjes_ae_mem_Ioc 0 (c n) (hc n).le
      (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).mono (fun r hr => ⟨hr.1.le,hr.2⟩)
  have heν x : (fun z => G (x,z)) =ᵐ[ν] (fun z => H (x,z)) := by
    filter_upwards [hs] with z hz
    obtain ⟨n,hn⟩ := hz
    exact hGe n x z.1 z.2 hn
  have hGN : (∫⁻ x, eLpNorm (fun z => G (x,z)) 2 ν ∂μ) < ∞ := by
    simpa only [eLpNorm_congr_ae (heν _)] using hN
  have hGp n : @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) (c n)) => G (z.1,(z.2.1,z.2.2.val))) := by
    convert hp n using 1
    funext z
    exact hGe n z.1 z.2.1 z.2.2.val z.2.2.property
  obtain ⟨hGi,Z,hZI,hZ,Ybar,hYbar,hbar,hebar⟩ := hmain E μ G hG hGp hGN
  refine ⟨?_,Z,hZI,?_,Ybar,hYbar,?_,hebar⟩
  · filter_upwards [hs,hGi] with z hz hi
    obtain ⟨n,hn⟩ := hz
    have hf : (fun x => G (x,z)) = (fun x => H (x,z)) := funext (fun x => hGe n x z.1 z.2 hn)
    rwa [← hf]
  · filter_upwards [hZ] with x hx
    obtain ⟨Y,hY,hf,heY⟩ := hx
    exact ⟨Y,hY,hf.congr_on_time_domain P F X Y _ _ (he x),heY⟩
  · apply hbar.congr_on_time_domain P F X Ybar
    intro ω r hr hrT
    exact integral_congr_ae (.of_forall fun x => he x ω r hr hrT)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stochastic_fubini_on_time_domain
