import Chapter4ItoCovarianceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Cross covariance of two actual Ito integrals, with a time density.
This proves the sigma-sigma-transpose term of the vector generator. -/
theorem continuous_ito_pair_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W V Y Z C : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hV : LocalMProcessWitness P F V)
    (hY : LocalMProcessWitness P F Y) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F W V C)
    (H K : ClosedTime T → Ω → ℝ)
    (hHa : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun s => H s w) t)
    (hKa : ∀ t,t<⊤ → Measurable[F t] (K t))
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (hYI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) Y)
    (hZI : ItoCovarianceFormula P F V (fun z => K (realTimeClamp z.2) z.1) Z)
    (Q : Ω × ℝ → ℝ) (hQm : ∀ w,Measurable (fun r => Q (w,r)))
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (hQi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => Q (w,r)) volume 0 (c n))
    (hCQ : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C (realTimeClamp r) w=∫ s in 0..r,Q (w,s)) :
    ∃ D : ClosedTime T → Ω → ℝ,LocalCovarianceWitness P F Y Z D ∧
      ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),D (realTimeClamp r) w=
        ∫ s in 0..r,H (realTimeClamp s) w*K (realTimeClamp s) w*Q (w,s) := by
  obtain ⟨D,hD,_,hDQ⟩ := continuous_ito_covariance_density P hT F hF hle hnull
    W Y V C hW hY hV hC H hHa hHc hYI Q hQm c hc hcm hcT hcc hQi hCQ
  have hHQm w := (open_path_real_measurable _ (hHc w)).mul (hQm w)
  have hHQi n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (realTimeClamp r) w*Q (w,r)) volume 0 (c n) := by
    filter_upwards [hQi n] with w hw
    apply hw.continuousOn_mul
    rw [uIcc_of_le (hc n)]
    intro r hr
    exact ((hHc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  obtain ⟨E,hE,_,hEQ⟩ := continuous_ito_covariance_density P hT F hF hle hnull
    V Z Y D hV hZ hY (hD.symm P F) K hKa hKc hZI
    (fun z => H (realTimeClamp z.2) z.1*Q z) hHQm c hc hcm hcT hcc hHQi hDQ
  refine ⟨E,hE.symm P F,?_⟩
  intro n
  filter_upwards [hEQ n] with w hw
  intro r hr
  rw [hw r hr]
  apply intervalIntegral.integral_congr
  intro s _
  ring

end Asakura.Chapter4
