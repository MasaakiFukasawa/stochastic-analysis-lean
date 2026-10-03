import Chapter6BoundedItoCrossDensity
import Chapter6GirsanovWritten
import Chapter2OneSidedStoppedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the changed-measure martingale part of an Ito process from
the actual bounded density integrand and the original square-integrable Z. -/
theorem girsanov_ito_drift {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (B : BrownianSystem P 1)
    (β Z : Ω × ℝ → ℝ) (hβm : Measurable β) (hZm : Measurable Z)
    (K : ℝ) (hβb : ∀ z,|β z|≤K)
    (N M C : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hM : LocalMProcessWitness P B.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) β N)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) Z M)
    (hC : LocalCovarianceWitness P B.F N N C)
    (hZsq : ∀ b : ℝ,0≤b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => Z (w,r)^2) volume 0 b)
    (R : ℝ) (hR : 0≤R)
    (hmean : (∫ w,Real.exp (N (realTimeClamp R) w-C (realTimeClamp R) w/2) ∂P)=1)
    (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (N (realTimeClamp R) w-C (realTimeClamp R) w/2)))) :
    ∃ A,AdaptedLocalVariationWitness B.F A ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t) ∧
      LocalMProcessWitness Q B.F (fun t w => M t w-A t w) ∧
      (∀ r : ℝ,0≤r → A (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..min R r,β (w,s)*Z (w,s)) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨D,hD,hDe⟩ := bounded_ito_cross_density P B β Z hβm hZm K hβb N M hN hM hNI hMI hZsq
  let τ := fun _w : Ω => (realTimeClamp R : HalfClosedTime)
  have hτ t : MeasurableSet[B.F t] {w | τ w≤t} := by
    by_cases h : realTimeClamp R≤t <;> simp [τ,h]
  have hτt w : τ w<⊤ := changed_time_finite R hR
  have hNs := hN.stopped P B.F B.mono B.le τ hτ
  obtain ⟨A,hA⟩ := local_covariance_witness_exists P B.F B.mono B.le B.null
    (fun t w => N (min (τ w) t) w) M hNs hM
  have hL := girsanov_maruyama_written P Q hT B.F B.mono B.le B.null N C hN hC τ hτ hτt hmean hQ M A hM hA
  refine ⟨A,covariance_adapted_variation P B.F B.mono B.le hNs hM hA,
    local_covariance_path_continuous P B.F _ M A hNs hM hA,hL,?_⟩
  intro r hr
  filter_upwards [local_covariance_one_sided_stopping P B.F B.mono B.le B.null N M D A hN hM hD τ hτ hA,
    hDe (min R r) (le_min hR hr)] with w hw hd
  rw [hw _ (changed_time_finite r hr)]
  have he : min (τ w) (realTimeClamp r)=realTimeClamp (min R r) :=
    (real_time_clamp_mono.map_min (a := R) (b := r)).symm
  rw [he,hd]

end Asakura.Chapter6
