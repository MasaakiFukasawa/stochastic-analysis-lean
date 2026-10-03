import Chapter10DeterministicStateProduct
import Chapter10IntegratingFactorRegularity
import Chapter6IntegratingFactorPrimitive

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual candidate-price SDE becomes the linear Gaussian observation
model after multiplying by L. The drift involving the observed price cancels,
and the transformed Ito integral is constructed from the same Brownian noise. -/
theorem kyle_actual_transform {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C : HalfClosedTime → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (β : ℝ → ℝ) (hβ : Continuous β) (l σ p0 : ℝ) (V : Ω → ℝ)
    (p : ℝ → Ω → ℝ) (hp : ∀ w,Continuous (fun t => p t w))
    (he : ∀ᵐ w ∂P,∀ t,0≤t → p t w=p0+(∫ s in 0..t,l*β s*(V w-p s w))+(l*σ)*W (realTimeClamp t) w) :
    let L := linearIntegratingFactor (fun t => l*β t)
    ∃ N,LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => L z.2*(l*σ)) N ∧
      (∀ w t,L t*V w=V w+∫ s in 0..t,l*β s*(L s*V w)) ∧
      ∀ᵐ w ∂P,∀ t,0≤t → L t*p t w=p0+
        (∫ s in 0..t,l*β s*(L s*V w))+N (realTimeClamp t) w := by
  let L := linearIntegratingFactor (fun t => l*β t)
  have ha : Continuous (fun t => l*β t) := hβ.const_mul l
  have hd s : deriv L s=l*β s*L s := (integrating_factor_derivative _ ha s).deriv
  have hL0 : L 0=1 := integrating_factor_initial _
  obtain ⟨N,hN,hNI,hprod⟩ := deterministic_state_product P F hF hle hnull W C
    (fun t w => (l*σ)*W t w) hW (hW.smul P F (l*σ)) hCa hclock
    (fun _ => l*σ) L continuous_const (integrating_factor_C1 _ ha)
    (constant_ito_integral P (by simp : (0:EReal)<⊤) F hF hle hnull W hW (l*σ))
    p (fun s w => l*β s*(V w-p s w)) (fun _ => p0)
    (fun w => ha.mul (continuous_const.sub (hp w))) he
  refine ⟨N,hN,hNI,?_,?_⟩
  · intro w t
    change L t*V w=V w+∫ s in 0..t,l*β s*(L s*V w)
    have hh := integrating_factor_primitive (fun s => l*β s) ha t
    have hi : (∫ s in 0..t,l*β s*(L s*V w))=(∫ s in 0..t,l*β s*L s)*V w := by
      rw [←intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      ring
    rw [hi]
    change L t=1+∫ s in 0..t,l*β s*L s at hh
    rw [hh]
    ring
  · filter_upwards [hprod] with w hw
    intro t ht
    have hh := hw t ht
    rw [hL0,one_mul] at hh
    convert hh using 1
    congr 2
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hd]
    change l*β s*(L s*V w)=_
    ring

end Asakura.Chapter10
