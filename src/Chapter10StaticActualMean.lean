import Chapter10DeterministicStateProduct
import Chapter10StaticInformationRegularity

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Multiply the actual static filter equation by its information J=1/S.
Ito integration by parts yields the displayed explicit mean, including the
actual Brownian integral appearing in the observation integral. -/
theorem static_actual_mean {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C N : HalfClosedTime → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hN : LocalMProcessWitness P F N) (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (c : ℝ → ℝ) (hc : Continuous c) (S0 σ m0 : ℝ) (hS0 : 0<S0)
    (V : Ω → ℝ) (a : ℝ → Ω → ℝ) (ha : ∀ w,Continuous (fun t => a t w))
    (hNI : ItoCovarianceFormula P F W (fun z => staticVariance c S0 σ z.2*c z.2/σ) N)
    (he : ∀ᵐ w ∂P,∀ t,0≤t → a t w=m0+
      (∫ s in 0..t,staticVariance c S0 σ s*((c s)^2/σ^2)*(V w-a s w))+N (realTimeClamp t) w) :
    ∃ Z,LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W (fun z => c z.2/σ) Z ∧
      ∀ᵐ w ∂P,∀ t,0≤t → a t w=staticVariance c S0 σ t*
        (m0/S0+(∫ s in 0..t,(c s)^2/σ^2)*V w+Z (realTimeClamp t) w) := by
  let S := staticVariance c S0 σ
  let J := staticInformation c S0 σ
  have hSc : Continuous S := static_variance_continuous c hc S0 σ hS0
  have hq : Continuous (fun s => (c s)^2/σ^2) := (hc.pow 2).div_const _
  have hd t : deriv J t=(c t)^2/σ^2 := (static_information_derivative c hc S0 σ t).deriv
  have hJS t ht : J t*S t=1 := static_information_variance c S0 σ hS0 t ht
  obtain ⟨Z,hZ,hZI,hprod⟩ := deterministic_state_product P F hF hle hnull W C N hW hN hCa hclock
    (fun t => S t*c t/σ) J ((hSc.mul hc).div_const _) (static_information_C1 c hc S0 σ) hNI
    a (fun t w => S t*((c t)^2/σ^2)*(V w-a t w)) (fun _ => m0)
    (fun w => (hSc.mul hq).mul (continuous_const.sub (ha w))) he
  have hZI' := hZI.congr_on_time_domain P F W Z _ (fun z => c z.2/σ) (by
    intro w t ht _
    change J t*(S t*c t/σ)=c t/σ
    calc
      _ = (J t*S t)*c t/σ := by ring
      _ = _ := by rw [hJS t ht,one_mul])
  refine ⟨Z,hZ,hZI',?_⟩
  filter_upwards [hprod] with w hw
  intro t ht
  have hh := hw t ht
  have hj0 : J 0=S0⁻¹ := by simp [J,staticInformation]
  have hi : (∫ s in 0..t,deriv J s*a s w+J s*(S s*((c s)^2/σ^2)*(V w-a s w)))=
      (∫ s in 0..t,(c s)^2/σ^2)*V w := by
    rw [←intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0≤s := (show s∈Icc 0 t by simpa only [uIcc_of_le ht] using hs).1
    dsimp only
    rw [hd]
    calc
      _ = ((c s)^2/σ^2)*(J s*S s)*V w+((c s)^2/σ^2)*(1-J s*S s)*a s w := by ring
      _ = _ := by rw [hJS s hs0]; ring
  rw [hi,hj0] at hh
  change a t w=S t*(m0/S0+(∫ s in 0..t,(c s)^2/σ^2)*V w+Z (realTimeClamp t) w)
  calc
    a t w = S t*(J t*a t w) := by rw [←mul_assoc,mul_comm (S t),hJS t ht,one_mul]
    _ = _ := by rw [hh]; simp only [div_eq_mul_inv,mul_comm m0]

end Asakura.Chapter10
