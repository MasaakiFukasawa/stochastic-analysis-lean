import Chapter10KyleFiniteMovingTransform
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Undo the integrating factor in the actual Kalman mean equation.
The resulting equation has drift k beta (v-m) and noise k sigma dW,
where k is the transformed Kalman gain times lambda. -/
theorem kyle_finite_filter_back_transform {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C N : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (l β K : ℝ → ℝ) (hl : Continuous l) (hβ : Continuous β) (hK : Continuous K)
    (R : ℝ) (hR : 0≤R) (σ a0 : ℝ) (a v : ℝ → Ω → ℝ)
    (ha : ∀ w,ContinuousOn (fun t => a t w) (Icc 0 R)) (hv : ∀ w,ContinuousOn (fun t => v t w) (Icc 0 R))
    (hNI : ItoCovarianceFormula P F W
      (fun z => K z.2*linearIntegratingFactor (fun t => l t*β t) z.2*(l z.2*σ)) N)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R, a t w=a0+
      (∫ s in 0..t,l s*β s*a s w+
        K s*l s*β s*(linearIntegratingFactor (fun t => l t*β t) s*v s w-a s w))+
      N (realTimeClamp t) w) :
    let L := linearIntegratingFactor (fun t => l t*β t)
    ∃ J,LocalMProcessWitness P F J ∧
      ItoCovarianceFormula P F W (fun z => K z.2*l z.2*σ) J ∧
      ∀ᵐ w ∂P,∀ t∈Icc 0 R, a t w/L t=a0+
        (∫ s in 0..t,K s*l s*β s*(v s w-a s w/L s))+J (realTimeClamp t) w := by
  let L := linearIntegratingFactor (fun t => l t*β t)
  have hc := hl.mul hβ
  have hLc := (integrating_factor_C1 _ hc).continuous
  have hLne s : L s≠0 := integrating_factor_nonzero _ _
  have hd s : deriv (fun t => (L t)⁻¹) s= -(l s*β s)/(L s) := by
    have hh := ((integrating_factor_derivative _ hc s).inv (hLne s)).deriv
    convert hh using 1
    dsimp only [L,Pi.mul_apply]
    field_simp
    rfl
  have hLi : ContDiff ℝ 1 (fun t => (L t)⁻¹) :=
    (integrating_factor_C1 _ hc).inv hLne
  have hL0 : L 0=1 := integrating_factor_initial _
  obtain ⟨J,hJ,hJI,hprod⟩ := finite_deterministic_state_product P F hF hle hnull W C N hW hN hCa hclock
    (fun t => K t*L t*(l t*σ)) (fun t => (L t)⁻¹)
    ((hK.mul hLc).mul (hl.mul_const _)) hLi hNI
    R hR a (fun s w => l s*β s*a s w+K s*l s*β s*(L s*v s w-a s w)) (fun _ => a0)
    (fun w => (hc.continuousOn.mul (ha w)).add (((hK.mul hl).mul hβ).continuousOn.mul ((hLc.continuousOn.mul (hv w)).sub (ha w)))) he
  have hJI' := hJI.congr_on_time_domain P F W J _ (fun z => K z.2*l z.2*σ)
    (fun w r _ _ => by dsimp only;field_simp [hLne r])
  refine ⟨J,hJ,hJI',?_⟩
  filter_upwards [hprod] with w hw
  intro t ht
  have hh := hw t ht
  rw [hL0,inv_one,one_mul] at hh
  have hi : (∫ s in 0..t,deriv (fun t => (L t)⁻¹) s*a s w+
      (L s)⁻¹*(l s*β s*a s w+K s*l s*β s*(L s*v s w-a s w)))=
      ∫ s in 0..t,K s*l s*β s*(v s w-a s w/L s) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hd]
    field_simp [hLne s]
    ring
  rw [hi] at hh
  simpa only [div_eq_mul_inv,mul_comm (a t w)] using hh

end Asakura.Chapter10
