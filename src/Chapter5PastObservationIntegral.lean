import Chapter5StoppedIntegratorReduction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- In Ito's formula, an already stopped past coordinate contributes no
increment on the current interval. This applies to the actual derivative
integral, by uniqueness of its covariance characterization. -/
theorem past_observation_integral_constant
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X N : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hN : LocalMProcessWitness P F N)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hHa : ∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => H (w,r)))
    (hHc : ∀ b : ℝ,0≤b → (b:EReal)<T → ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 b))
    (a : ℝ) (ha : 0≤a)
    (hI : ItoCovarianceFormula P F (fun t w => X (min (realTimeClamp a) t) w) H N) :
    ∀ᵐ w ∂P,∀ u v : ClosedTime T,u<⊤ → v<⊤ →
      realTimeClamp a≤u → realTimeClamp a≤v → N u w=N v w := by
  obtain ⟨Y,Z,hY,hZ,hy,hz,he⟩ := continuous_stopped_integrator_reduction
    P hT F hF hle hnull X hX H hHm hHa hHc a ha
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) a≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) a≤t <;> simp [h]
  have hXs := hX.stopped P F hF hle (fun _ => realTimeClamp a) hstop
  have hnz := hI.unique P hT F hF hle hnull _ N Z H hXs hN hZ hz
  filter_upwards [he,hnz] with w hw hnw
  intro u v hu hv hau hav
  rw [hnw u hu,hnw v hv,hw u hu,hw v hv,min_eq_left hau,min_eq_left hav]

end Asakura.Chapter5
