import Chapter4ItoPairDensity
import Chapter4CovarianceEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma half_line_integral_continuous (H : HalfClosedTime → ℝ)
    (hc : ∀ t,t<⊤ → ContinuousAt H t) : Continuous (fun r => H (realTimeClamp (T:=⊤) r)) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have ht : realTimeClamp (T:=⊤) r<⊤ := by
    change min ⊤ (max 0 (r:EReal))<⊤
    simp only [min_eq_right le_top]
    exact max_lt (EReal.coe_lt_top 0) (EReal.coe_lt_top r)
  exact (hc _ ht).comp real_time_clamp_continuous.continuousAt

lemma half_line_exhaustion_common
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (T:=⊤) (c n))
    (B : Ω → ℝ → Prop)
    (hB : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),B w r) :
    ∀ᵐ w ∂P,∀ r : ℝ,0≤r → B w r := by
  filter_upwards [ae_all_iff.mpr hB] with w hw
  intro r hr
  obtain ⟨n,hn⟩ := hcc (realTimeClamp r) (real_time_below r hr (EReal.coe_lt_top r))
  change (realTimeClamp (T:=⊤) r).val<(realTimeClamp (T:=⊤) (c n)).val at hn
  rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq (c n) (hc n) le_top] at hn
  exact hw n r ⟨hr,EReal.coe_le_coe_iff.mp hn.le⟩

/-- On the half line the density identity holds at every nonnegative time
on a single event of probability one. -/
theorem half_line_ito_covariance_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W Y N C H : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hY : LocalMProcessWitness P F Y)
    (hN : LocalMProcessWitness P F N) (hC : LocalCovarianceWitness P F W N C)
    (hHa : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun a => H a w) t)
    (hYI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) Y)
    (Q : Ω → ℝ → ℝ) (hQc : ∀ w,Continuous (Q w))
    (hCQ : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → C (realTimeClamp r) w=∫ a in 0..r,Q w a) :
    ∃ D : HalfClosedTime → Ω → ℝ,LocalCovarianceWitness P F Y N D ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0≤r → D (realTimeClamp r) w=∫ a in 0..r,H (realTimeClamp a) w*Q w a := by
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion (EReal.coe_lt_top 0)
  obtain ⟨D,hD,_,he⟩ := continuous_ito_covariance_density P (EReal.coe_lt_top 0) F hF hle hnull
    W Y N C hW hY hN hC H hHa hHc hYI (fun z => Q z.1 z.2) (fun w => (hQc w).measurable)
    c (fun n => (hc n).le) hcm.monotone hcT hcc
    (fun n => ae_of_all _ fun w => (hQc w).intervalIntegrable 0 (c n))
    (fun n => hCQ.mono (fun w hw r hr => hw r hr.1))
  exact ⟨D,hD,half_line_exhaustion_common P c (fun n => (hc n).le) hcc _ he⟩

end Asakura.Chapter4
