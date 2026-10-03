import Chapter10DeterministicStateProduct

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Integration by parts needs the state equation and drift continuity only
on the compact interval in question. This permits coefficients singular at a
later maturity: extend the deterministic coefficients past this interval. -/
theorem finite_deterministic_state_product {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C N : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (g v : ℝ → ℝ) (hg : Continuous g) (hv : ContDiff ℝ 1 v)
    (hNI : ItoCovarianceFormula P F W (fun z => g z.2) N)
    (R : ℝ) (hR : 0≤R) (Y b : ℝ → Ω → ℝ) (ξ : Ω → ℝ)
    (hb : ∀ w,ContinuousOn (fun s => b s w) (Icc 0 R))
    (hY : ∀ᵐ w ∂P,∀ t∈Icc 0 R,Y t w=ξ w+(∫ s in 0..t,b s w)+N (realTimeClamp t) w) :
    ∃ J : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P F J ∧
      ItoCovarianceFormula P F W (fun z => v z.2*g z.2) J ∧
      ∀ᵐ w ∂P,∀ t∈Icc 0 R,
        v t*Y t w=v 0*ξ w+(∫ s in 0..t,deriv v s*Y s w+v s*b s w)+J (realTimeClamp t) w := by
  let b' := fun s w => b (projIcc 0 R hR s) w
  have hbc w : Continuous (fun s => b' s w) :=
    (hb w).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc 0 R hR s).property)
  let Y' := fun t w => ξ w+(∫ s in 0..t,b' s w)+N (realTimeClamp t) w
  have hbe s (hs : s∈Icc 0 R) w : b' s w=b s w := by
    dsimp only [b']; rw [projIcc_of_mem hR hs]
  have hie t (ht : t∈Icc 0 R) w : (∫ s in 0..t,b' s w)=∫ s in 0..t,b s w := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hbe s ⟨hs.1,hs.2.trans ht.2⟩ w
  obtain ⟨J,hJ,hJI,hprod⟩ := deterministic_state_product P F hF hle hnull W C N hW hN hCa hclock
    g v hg hv hNI Y' b' ξ hbc (Filter.Eventually.of_forall (fun _ _ _ => rfl))
  refine ⟨J,hJ,hJI,?_⟩
  filter_upwards [hY,hprod] with w hw hp
  have he t (ht : t∈Icc 0 R) : Y' t w=Y t w := by
    dsimp only [Y']; rw [hie t ht w,hw t ht]
  intro t ht
  have hh := hp t ht.1
  rw [he t ht] at hh
  rw [hh]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsR : s∈Icc 0 R := ⟨hs.1,hs.2.trans ht.2⟩
  dsimp only
  rw [he s hsR,hbe s hsR w]

end Asakura.Chapter10
