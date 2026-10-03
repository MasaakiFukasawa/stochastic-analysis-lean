import Chapter6VectorCrossDensity
import Chapter6GirsanovWritten
import Chapter2OneSidedStoppedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the changed-measure martingale part of an Ito process from
the actual bounded density integrand and the original square-integrable Z. -/
theorem girsanov_vector_ito_drift {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {d : ℕ} (B : BrownianSystem P d)
    (β H : Fin d → Ω × ℝ → ℝ) (hβm : ∀ j,Measurable (β j)) (hHm : ∀ j,Measurable (H j))
    (K : ℝ) (hK : 0≤K) (hβb : ∀ j z,|β j z|≤K) (hHb : ∀ j z,|H j z|≤K)
    (N M : Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ j,LocalMProcessWitness P B.F (N j)) (hM : ∀ j,LocalMProcessWitness P B.F (M j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (β j) (N j))
    (hMI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (H j) (M j))
    (C : HalfClosedTime → Ω → ℝ)
    (hC : LocalCovarianceWitness P B.F (fun t w => ∑ j,N j t w) (fun t w => ∑ j,N j t w) C)
    (R : ℝ) (hR : 0≤R)
    (hmean : (∫ w,Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2) ∂P)=1)
    (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2)))) :
    ∃ A,AdaptedLocalVariationWitness B.F A ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t) ∧
      LocalMProcessWitness Q B.F (fun t w => (∑ j,M j t w)-A t w) ∧
      (∀ r : ℝ,0≤r → A (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..min R r,∑ j,β j (w,s)*H j (w,s)) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨D,hD,hDe⟩ := bounded_vector_cross_density P B β H hβm hHm K hK hβb hHb N M hN hM hNI hMI
  let Z := fun t w => ∑ j,N j t w
  let Y := fun t w => ∑ j,M j t w
  have hZ := local_martingale_finset_sum P hT B.F B.mono B.le Finset.univ N (fun j _ => hN j)
  have hY := local_martingale_finset_sum P hT B.F B.mono B.le Finset.univ M (fun j _ => hM j)
  let τ := fun _w : Ω => (realTimeClamp R : HalfClosedTime)
  have hτ t : MeasurableSet[B.F t] {w | τ w≤t} := by
    by_cases h : realTimeClamp R≤t <;> simp [τ,h]
  have hτt w : τ w<⊤ := changed_time_finite R hR
  have hNs := hZ.stopped P B.F B.mono B.le τ hτ
  obtain ⟨A,hA⟩ := local_covariance_witness_exists P B.F B.mono B.le B.null
    (fun t w => Z (min (τ w) t) w) Y hNs hY
  have hL := girsanov_maruyama_written P Q hT B.F B.mono B.le B.null Z C hZ hC τ hτ hτt hmean hQ Y A hY hA
  refine ⟨A,covariance_adapted_variation P B.F B.mono B.le hNs hY hA,
    local_covariance_path_continuous P B.F _ Y A hNs hY hA,hL,?_⟩
  intro r hr
  filter_upwards [local_covariance_one_sided_stopping P B.F B.mono B.le B.null Z Y D A hZ hY hD τ hτ hA,
    hDe (min R r) (le_min hR hr)] with w hw hd
  rw [hw _ (changed_time_finite r hr)]
  have he : min (τ w) (realTimeClamp r)=realTimeClamp (min R r) :=
    (real_time_clamp_mono.map_min (a := R) (b := r)).symm
  rw [he,hd]

end Asakura.Chapter6
