import Chapter4C1ClockVariation
import Chapter4ClockVariationIntegral
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- A deterministic C1 multiplier of an actual Ito integral satisfies
integration by parts; the new integral is constructed and associated
with the original driving martingale. -/
theorem deterministic_ito_product
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hAa : ∀ t,t<⊤ → Measurable[F t] (A t))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (g v : ℝ → ℝ) (hg : Continuous g) (hv : ContDiff ℝ 1 v)
    (hNI : ItoCovarianceFormula P F W (fun z => g z.2) N) :
    ∃ V : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F V ∧
      ItoCovarianceFormula P F W (fun z => v z.2*g z.2) V ∧
      ∀ᵐ w ∂P,∀ d : ℝ,0≤d → (d:EReal)<T →
        v d*N (realTimeClamp d) w=V (realTimeClamp d) w+
          ∫ r in 0..d,deriv v r*N (realTimeClamp r) w := by
  obtain ⟨hAm,hAc⟩ := clock_regular_from_identity A hclock
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨J,L,hJ,hJI,_,_,hLI,hprod⟩ := C1_weighted_product_constructed P hT F hF hle hnull N A hN
    (continuous_increasing_adapted_variation hT F hF A hAa hAm hAc) hAc v hv
    (C1_clock_adapted_variation hT F hF A hAa hclock v hv)
    c (fun n => (hc n).le) hcm.monotone hcT hcc
  obtain ⟨V,hV,hVI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => v z.2*g z.2) (by
      intro r hr hrT
      change Measurable[F (realTimeClamp r)] (fun _ : Ω => v r*g r)
      exact measurable_const)
    (fun _ _ _ _ => (hv.continuous.mul hg).continuousOn)
  have hJI' := hJI.congr_on_time_domain P F N J _ (fun z => v z.2)
    (fun w r hr hrT => by rw [hclock w r hr hrT])
  have hJV := ito_integral_associativity P hT F hF hle hnull W N J V
    (fun z => g z.2) (fun z => v z.2) hW hN hJ hV (fun _ => hg.measurable)
    (fun _ => hv.continuous.measurable) hNI hJI' hVI
  have htime := clock_variation_integral_all_times P A L _ c (fun n => (hc n).le) hcT
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) hLI
  refine ⟨V,hV,hVI,?_⟩
  filter_upwards [hprod,hJV,htime] with w hp hj ht
  intro d hd hdT
  have hdt := real_time_below d hd hdT
  obtain ⟨n,hn⟩ := hcc _ hdt
  have hdn : d≤c n := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
    exact (EReal.coe_lt_coe_iff.mp hn).le
  have hh := hp _ hdt
  rw [hclock w d hd hdT,hj _ hdt,ht n d ⟨hd,hdn⟩] at hh
  rw [mul_comm]
  convert hh using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r∈Icc 0 d := by simpa only [uIcc_of_le hd] using hr
  dsimp only
  rw [hclock w r hr'.1 ((EReal.coe_le_coe hr'.2).trans_lt hdT)]
  ring

end Asakura.Chapter4
