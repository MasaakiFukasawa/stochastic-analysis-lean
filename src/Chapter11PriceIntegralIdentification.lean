import Chapter11ReplicationRepresentation
import Chapter4BrownianSystem

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A local Ito formula and a conditional price formula identify the
actual local integral with the already represented L2 martingale. -/
theorem price_integral_identification {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (U : Ω → ℝ) (V : ℝ → Ω → ℝ) (N M : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P F N) (hM : ContinuousM2Witness P F M)
    (a c R : ℝ) (hR : 0≤R)
    (hce : ∀ t∈Icc 0 R,V t=ᵐ[P] P[U|F (realTimeClamp t)])
    (hrep : ∀ t∈Icc 0 R,(fun w => a+M (realTimeClamp t) w)=ᵐ[P] P[U|F (realTimeClamp t)])
    (hito : ∀ t∈Icc 0 R,V t=ᵐ[P] fun w => c+N (realTimeClamp t) w) :
    c=a ∧ ∀ t∈Icc 0 R,N (realTimeClamp t)=ᵐ[P] M (realTimeClamp t) := by
  have he t (ht : t∈Icc 0 R) : (fun w => c+N (realTimeClamp t) w)=ᵐ[P] fun w => a+M (realTimeClamp t) w :=
    (hito t ht).symm.trans ((hce t ht).trans (hrep t ht).symm)
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have ha : (fun _ : Ω => c)=ᵐ[P] fun _ => a := by
    filter_upwards [he 0 ⟨le_rfl,hR⟩,hN.initial P F,hM.initial] with w hw hn hm
    simpa only [hz,hn,hm,Pi.zero_apply,add_zero] using hw
  have hac : c=a := by simpa using integral_congr_ae ha
  refine ⟨hac,?_⟩
  intro t ht
  filter_upwards [he t ht] with w hw
  rw [hac] at hw
  exact add_left_cancel hw

end Asakura.Chapter11
