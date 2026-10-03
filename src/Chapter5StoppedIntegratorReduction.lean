import Chapter5StoppedIntegralFormula
import Chapter2ContinuousIntegrand
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The integral against a stopped coordinate is the stopped integral
against the original coordinate. Both integrals are constructed here. -/
theorem continuous_stopped_integrator_reduction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hHa : ∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => H (w,r)))
    (hHc : ∀ b : ℝ,0≤b → (b:EReal)<T → ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 b))
    (a : ℝ) (ha : 0≤a) :
    ∃ Y Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧ LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X H Y ∧
      ItoCovarianceFormula P F (fun t w => X (min (realTimeClamp a) t) w) H Z ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=Y (min (realTimeClamp a) t) w) := by
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) a≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) a≤t <;> simp [h]
  have hXs := hX.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  obtain ⟨Y,hY,hy⟩ := continuous_adapted_ito_exists P hT F hF hle hnull X hX H hHa hHc
  obtain ⟨Z,hZ,hz⟩ := continuous_adapted_ito_exists P hT F hF hle hnull _ hXs H hHa hHc
  have hYs := hY.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  have hys := stopped_ito_covariance_formula P hT F hF hle hnull X Y H hX hY hHm hy a ha
  have he : (fun z : Ω × ℝ => H z*(Ioc 0 a).indicator (fun _ => (1:ℝ)) z.2)=
      (fun z => (Ioc 0 a).indicator (fun r => H (z.1,r)) z.2) := by
    funext z
    by_cases h : z.2∈Ioc 0 a <;> simp [indicator_of_mem,indicator_of_notMem,h]
  refine ⟨Y,Z,hY,hZ,hy,hz,?_⟩
  apply ito_integral_associativity P hT F hF hle hnull X _ Z _
    (fun z => (Ioc 0 a).indicator (fun _ => (1:ℝ)) z.2) H hX hXs hZ hYs
    (fun _ => measurable_const.indicator measurableSet_Ioc) hHm
    (stopped_identity_ito_integral P hT F hF hle hnull X hX a ha) hz
  rw [he]
  exact hys

end Asakura.Chapter5
