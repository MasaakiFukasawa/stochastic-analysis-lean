import Chapter2RegularQuadraticVariation
import Chapter2LocalCovarianceAE
import Chapter2RealElementaryEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The original local martingale itself has a regular quadratic-variation
representative. Thus subsequent Ito constructions need not alter X. -/
theorem local_quadratic_variation_regular_choice
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    ∃ A : ClosedTime T → Ω → ℝ,
      LocalCovarianceWitness P F X X A ∧
      (∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) ∧
      (∀ ω, A ⊥ ω = 0) := by
  obtain ⟨X',A,hX',hA,he,hm,hc,h0⟩ := regular_quadratic_variation_representatives P F hF hle hnull X hX
  have he' : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X' t ω = X t ω := he.mono (fun ω hω t _ => hω t)
  exact ⟨A,hA.congr_ae_processes P F hF hle hX' hX' hX hX he' he',hm,hc,fun ω => (h0 ω).2⟩

theorem regular_covariance_on_real_intervals
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (A : ClosedTime T → Ω → ℝ)
    (hm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T) :
    (∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 b)) ∧
      (∀ ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 b)) := by
  have hbelow r (hr : r ∈ Icc 0 b) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hbT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hbT
  constructor
  · intro ω r hr s hs hrs
    exact hm ω (hbelow r hr) (hbelow s hs) (real_time_clamp_mono hrs)
  · intro ω r hr
    exact ((hc ω _ (hbelow r hr)).comp real_time_clamp_continuous.continuousAt).continuousWithinAt

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_quadratic_variation_regular_choice
#print axioms Asakura.Chapter2Complete.regular_covariance_on_real_intervals
