import Chapter4ShiftedDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Both brackets needed to recognize an Ito integral are derived from
its covariance characterization and the Brownian clock. -/
theorem brownian_ito_cross_and_self_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W N C H : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → C (realTimeClamp r) w=r)
    (hHa : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun a => H a w) t)
    (hNI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) N) :
    ∃ D E : HalfClosedTime → Ω → ℝ,
      LocalCovarianceWitness P F N W D ∧ LocalCovarianceWitness P F N N E ∧
      (∀ᵐ w ∂P,∀ r : ℝ,0≤r → D (realTimeClamp r) w=∫ a in 0..r,H (realTimeClamp a) w) ∧
      (∀ᵐ w ∂P,∀ r : ℝ,0≤r → E (realTimeClamp r) w=∫ a in 0..r,(H (realTimeClamp a) w)^2) := by
  obtain ⟨D,hD,hd⟩ := half_line_ito_covariance_density P F hF hle hnull W N W C H hW hN hW hC
    hHa hHc hNI (fun _ _ => 1) (fun _ => continuous_const)
    (ae_of_all _ fun w r hr => by simp [hclock w r hr])
  simp only [mul_one] at hd
  obtain ⟨E,hE,he⟩ := half_line_ito_covariance_density P F hF hle hnull W N N D H hW hN hN
    (hD.symm P F) hHa hHc hNI (fun w r => H (realTimeClamp r) w)
    (fun w => half_line_integral_continuous _ (hHc w)) hd
  exact ⟨D,E,hD,hE,hd,by simpa only [pow_two] using he⟩

end Asakura.Chapter4
