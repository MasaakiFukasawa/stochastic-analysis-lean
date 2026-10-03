import Chapter4DeterministicItoProduct
import Chapter10DensityProductIntegrals
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic integration by parts for an actual scalar Ito-driven
state. The new noise integral is constructed, not assumed. -/
theorem deterministic_state_product {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C N : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (g v : ℝ → ℝ) (hg : Continuous g) (hv : ContDiff ℝ 1 v)
    (hNI : ItoCovarianceFormula P F W (fun z => g z.2) N)
    (Y b : ℝ → Ω → ℝ) (ξ : Ω → ℝ) (hb : ∀ w,Continuous (fun s => b s w))
    (hY : ∀ᵐ w ∂P,∀ t,0≤t → Y t w=ξ w+(∫ s in 0..t,b s w)+N (realTimeClamp t) w) :
    ∃ J : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P F J ∧
      ItoCovarianceFormula P F W (fun z => v z.2*g z.2) J ∧
      ∀ᵐ w ∂P,∀ t,0≤t →
        v t*Y t w=v 0*ξ w+(∫ s in 0..t,deriv v s*Y s w+v s*b s w)+J (realTimeClamp t) w := by
  obtain ⟨J,hJ,hJI,hprod⟩ := deterministic_ito_product P (by simp : (0:EReal)<⊤)
    F hF hle hnull W C N hW hN hCa (fun w r hr _ => hclock w r hr) g v hg hv hNI
  refine ⟨J,hJ,hJI,?_⟩
  filter_upwards [hY,hprod] with w hy hp
  intro t ht
  let A := fun s => ξ w+∫ u in 0..s,b u w
  have hAd s : HasDerivAt A (b s w) s :=
    (intervalIntegral.integral_hasDerivAt_right ((hb w).intervalIntegrable 0 s)
      ((hb w).stronglyMeasurableAtFilter _ _) (hb w).continuousAt).const_add _
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun s => (hAd s).continuousAt)
  have hvc := hv.continuous
  have hvd := hv.continuous_deriv le_rfl
  have hNc : Continuous (fun s => N (realTimeClamp s) w) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hN.path P F w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hd s : HasDerivAt (fun u => v u*A u) (deriv v s*A s+v s*b s w) s := by
    convert ((hv.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul (hAd s) using 1 <;> ring
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s∈uIcc 0 t) => hd s)
    ((hvd.mul hAc |>.add (hvc.mul (hb w))).intervalIntegrable 0 t)
  have hsum := intervalIntegral.integral_add
    ((hvd.mul hAc |>.add (hvc.mul (hb w))).intervalIntegrable (μ := volume) 0 t)
    ((hvd.mul hNc).intervalIntegrable (μ := volume) 0 t)
  simp only [Pi.add_apply,Pi.mul_apply] at hsum
  have heq : (∫ s in 0..t,deriv v s*Y s w+v s*b s w)=
      (∫ s in 0..t,deriv v s*A s+v s*b s w)+(∫ s in 0..t,deriv v s*N (realTimeClamp s) w) := by
    rw [←hsum]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0≤s := (show s∈Icc 0 t by simpa only [uIcc_of_le ht] using hs).1
    dsimp only
    rw [hy s hs0]
    dsimp only [A,Pi.add_apply,Pi.mul_apply]
    ring
  have hp' := hp t ht (EReal.coe_lt_top t)
  rw [heq,hfund,hy t ht]
  have ha0 : A 0=ξ w := by simp [A]
  rw [ha0]
  dsimp only [A] at *
  nlinarith

end Asakura.Chapter10
