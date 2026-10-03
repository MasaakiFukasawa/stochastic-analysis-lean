import Chapter10KyleActualTransform

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The exercise's time-dependent lambda and moving asset value give two
transformed actual Ito integrals: L gamma against the value noise and
L lambda sigma against the order noise. -/
theorem kyle_moving_transform {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C N U D M : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hU : LocalMProcessWitness P F U) (hM : LocalMProcessWitness P F M)
    (hCa : ∀ t,t<⊤ → Measurable[F t] (C t)) (hDa : ∀ t,t<⊤ → Measurable[F t] (D t))
    (hC : ∀ w r,0≤r → C (realTimeClamp r) w=r) (hD : ∀ w r,0≤r → D (realTimeClamp r) w=r)
    (l β γ : ℝ → ℝ) (hl : Continuous l) (hβ : Continuous β) (hγ : Continuous γ)
    (σ p0 : ℝ) (V0 : Ω → ℝ) (v p : ℝ → Ω → ℝ)
    (hv : ∀ w,Continuous (fun t => v t w)) (hp : ∀ w,Continuous (fun t => p t w))
    (hNI : ItoCovarianceFormula P F W (fun z => l z.2*σ) N)
    (hMI : ItoCovarianceFormula P F U (fun z => γ z.2) M)
    (heV : ∀ᵐ w ∂P,∀ t,0≤t → v t w=V0 w+M (realTimeClamp t) w)
    (heP : ∀ᵐ w ∂P,∀ t,0≤t → p t w=p0+
      (∫ s in 0..t,l s*β s*(v s w-p s w))+N (realTimeClamp t) w) :
    let L := linearIntegratingFactor (fun t => l t*β t)
    ∃ NR NQ,LocalMProcessWitness P F NR ∧ LocalMProcessWitness P F NQ ∧
      ItoCovarianceFormula P F U (fun z => L z.2*γ z.2) NR ∧
      ItoCovarianceFormula P F W (fun z => L z.2*(l z.2*σ)) NQ ∧
      (∀ᵐ w ∂P,∀ t,0≤t → L t*v t w=V0 w+
        (∫ s in 0..t,l s*β s*(L s*v s w))+NR (realTimeClamp t) w) ∧
      ∀ᵐ w ∂P,∀ t,0≤t → L t*p t w=p0+
        (∫ s in 0..t,l s*β s*(L s*v s w))+NQ (realTimeClamp t) w := by
  let L := linearIntegratingFactor (fun t => l t*β t)
  have ha : Continuous (fun t => l t*β t) := hl.mul hβ
  have hd t : deriv L t=l t*β t*L t := (integrating_factor_derivative _ ha t).deriv
  have hL0 : L 0=1 := integrating_factor_initial _
  have heV' : ∀ᵐ w ∂P,∀ t,0≤t → v t w=V0 w+(∫ _ in 0..t,(0:ℝ))+M (realTimeClamp t) w := by
    simpa only [intervalIntegral.integral_zero,add_zero] using heV
  obtain ⟨NR,hNR,hNRI,hR⟩ := deterministic_state_product P F hF hle hnull U D M hU hM hDa hD
    γ L hγ (integrating_factor_C1 _ ha) hMI v (fun _ _ => 0) V0 (fun _ => continuous_const) heV'
  obtain ⟨NQ,hNQ,hNQI,hQ⟩ := deterministic_state_product P F hF hle hnull W C N hW hN hCa hC
    (fun t => l t*σ) L (hl.mul_const _) (integrating_factor_C1 _ ha) hNI
    p (fun t w => l t*β t*(v t w-p t w)) (fun _ => p0) (fun w => ha.mul ((hv w).sub (hp w))) heP
  refine ⟨NR,NQ,hNR,hNQ,hNRI,hNQI,?_,?_⟩
  · filter_upwards [hR] with w hw
    intro t ht
    have hh := hw t ht
    rw [hL0,one_mul] at hh
    convert hh using 1
    congr 2
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hd]
    change l s*β s*(L s*v s w)=_
    ring
  · filter_upwards [hQ] with w hw
    intro t ht
    have hh := hw t ht
    rw [hL0,one_mul] at hh
    convert hh using 1
    congr 2
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hd]
    change l s*β s*(L s*v s w)=_
    ring

end Asakura.Chapter10
