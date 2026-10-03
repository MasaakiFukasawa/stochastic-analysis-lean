import Chapter13ExponentialItoDensity
import Chapter13HJMAlgebra
import Chapter6ExponentialLocal
import Chapter6FiniteTimeDensity
import Chapter3OpenPathMeasurable
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

theorem hjm_term_rate_ito {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A M C:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A M)
    (hC:LocalCovarianceWitness P F M M C)
    {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h k:Ω × ℝ → E)
    (ham:∀w,Measurable (fun r => (‖k (w,r)‖^2-‖h (w,r)‖^2)/2))
    (hqm:∀w,Measurable (fun r => ‖k (w,r)-h (w,r)‖^2))
    (R:ℝ) (hR:0≤R) (hRT:(R:EReal)<T)
    (hai:∀ᵐw∂P,IntervalIntegrable (fun r => (‖k (w,r)‖^2-‖h (w,r)‖^2)/2) volume 0 R)
    (hqi:∀ᵐw∂P,IntervalIntegrable (fun r => ‖k (w,r)-h (w,r)‖^2) volume 0 R)
    (hAe:∀ᵐw∂P,∀r∈Icc 0 R,A (realTimeClamp r) w=A ⊥ w+∫s in 0..r,(‖k (w,s)‖^2-‖h (w,s)‖^2)/2)
    (hCe:∀ᵐw∂P,∀r∈Icc 0 R,C (realTimeClamp r) w=∫s in 0..r,‖k (w,s)-h (w,s)‖^2)
    (δ:ℝ) (hδ:δ≠0) :
    let rate:=fun t w => (Real.exp (X t w)-1)/δ
    ∃L,LocalMProcessWitness P F L ∧
      ItoCovarianceFormula P F M (fun z => Real.exp (X (realTimeClamp z.2) z.1)) L ∧
      ∀r∈Icc 0 R,(fun w => δ*(rate (realTimeClamp r) w-rate ⊥ w))=ᵐ[P]
        (fun w => L (realTimeClamp r) w+
          ∫s in 0..r,(1+δ*rate (realTimeClamp s) w)*inner ℝ (k (w,s)-h (w,s)) (k (w,s))) := by
  intro rate
  obtain ⟨L,hL,hLI,he⟩:=exponential_ito_time_density P hT F hF hle hnull X A M C hX hC
    (fun z => (‖k z‖^2-‖h z‖^2)/2) (fun z => ‖k z-h z‖^2) ham hqm R hR hRT hai hqi hAe hCe
  have hr t w:1+δ*rate t w=Real.exp (X t w) := by dsimp [rate];field_simp;ring
  refine ⟨L,hL,hLI,?_⟩
  intro r hri
  filter_upwards [he r hri] with w hw
  have hi:(∫s in 0..r,Real.exp (X (realTimeClamp s) w)*
      ((‖k (w,s)‖^2-‖h (w,s)‖^2)/2+‖k (w,s)-h (w,s)‖^2/2))=
      ∫s in 0..r,(1+δ*rate (realTimeClamp s) w)*inner ℝ (k (w,s)-h (w,s)) (k (w,s)) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [hr,bond_ratio_ito_drift]
  rw [hi] at hw
  have heq:δ*(rate (realTimeClamp r) w-rate ⊥ w)=Real.exp (X (realTimeClamp r) w)-Real.exp (X ⊥ w) := by
    dsimp [rate]
    field_simp
    ring
  rw [heq]
  linarith
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_term_rate_ito
