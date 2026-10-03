import Chapter10StaticObservationIntegral

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Multiply the actual static filter equation by its information J=1/S.
Ito integration by parts yields the displayed explicit mean, including the
actual Brownian integral appearing in the observation integral. -/
theorem static_mean_observation_formula {Ω : Type*} [m : MeasurableSpace Ω]
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
      (∫ s in 0..t,staticVariance c S0 σ s*((c s)^2/σ^2)*(V w-a s w))+N (realTimeClamp t) w)
    (hσ : σ≠0) (Y A : HalfClosedTime → Ω → ℝ)
    (hY : SemimartingaleDecomposition P F Y A (fun t w => σ*W t w))
    (hA : ∀ t,0≤t → ∀ w,A (realTimeClamp t) w=∫ s in 0..t,c s*V w)
    (τ : ℕ → ℝ) (hτ : ∀ n,0≤τ n) (hτm : Monotone τ)
    (hτco : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := ⊤) (τ n)) :
    ∃ U,SemimartingaleIntegralFormula P F τ hτ A (fun t w => σ*W t w)
      (fun z => c z.2/σ^2) U ∧ ∀ t,0≤t → ∀ᵐ w ∂P,
        a t w=staticVariance c S0 σ t*(m0/S0+U (realTimeClamp t) w) := by
  obtain ⟨Z,hZ,hZI,hm⟩ := static_actual_mean P F hF hle hnull W C N hW hN hCa hclock
    c hc S0 σ m0 hS0 V a ha hNI he
  obtain ⟨U,hUI,hU⟩ := static_observation_integral P F hF hle hnull W C Y A Z hW hZ hCa hclock
    c hc σ hσ V hY hA hZI τ hτ hτm hτco
  refine ⟨U,hUI,?_⟩
  intro t ht
  filter_upwards [hm,hU t ht] with w hm hU
  rw [hm t ht,hU]
  ring

end Asakura.Chapter10
