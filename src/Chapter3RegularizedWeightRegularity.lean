import Chapter3RegularizedItoEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Regularity of the positive shifted powers used in BDG, also for negative exponents. -/
theorem shifted_power_process_regularity
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (A : ClosedTime T → Ω → ℝ)
    (hAa : ∀ t, t < ⊤ → Measurable[F t] (A t))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hAp : ∀ ω t, t < ⊤ → 0 ≤ A t ω)
    (ε r : ℝ) (hε : 0 < ε) :
    (∀ t, t < ⊤ → Measurable[F t] (fun ω => (ε+A t ω)^r)) ∧
    (∀ ω t, t < ⊤ → ContinuousAt (fun s => (ε+A s ω)^r) t) ∧
    (∀ ω t, t < ⊤ → 0 < (ε+A t ω)^r) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    have ha : 0 < ε/4 := by positivity
    have heq : (fun ω => (ε+A t ω)^r) =
        fun ω => positivePowerExtension (ε/4) r (ε+A t ω) := by
      funext ω
      exact (positivePowerExtension_value_deriv ha (by linarith [hAp ω t ht]) r).1.symm
    rw [heq]
    exact (positivePowerExtension_contDiff ha r 0).continuous.measurable.comp
      (measurable_const.add (hAa t ht))
  · intro ω t ht
    exact (continuousAt_const.add (hAc ω t ht)).rpow_const
      (Or.inl (by linarith [hAp ω t ht] : ε+A t ω ≠ 0))
  · intro ω t ht
    exact Real.rpow_pos_of_pos (by linarith [hAp ω t ht]) r

/-- A nonnegative shifted power of an increasing process is itself increasing. -/
theorem shifted_power_process_monotone
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (A : ClosedTime T → Ω → ℝ)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAp : ∀ ω t, t < ⊤ → 0 ≤ A t ω)
    (ε r : ℝ) (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    ∀ ω, MonotoneOn (fun t => (ε+A t ω)^r) (Iio ⊤) := by
  intro ω s hs t ht hst
  exact Real.rpow_le_rpow (add_nonneg hε (hAp ω s hs))
    (by linarith [hAm ω hs ht hst]) hr

/-- Transfer open-time process regularity to the real-time encodings of the integrands. -/
theorem open_process_real_regularity
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (H : ClosedTime T → Ω → ℝ)
    (hHa : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t) :
    (∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (H (realTimeClamp r))) ∧
    (∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω,
      ContinuousOn (fun r => H (realTimeClamp r) ω) (Icc 0 b)) := by
  have hrt (r : ℝ) (hr : 0 ≤ r) (hrT : (r:EReal) < T) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr hrT.le]
    exact hrT
  refine ⟨fun r hr hrT => hHa _ (hrt r hr hrT),?_⟩
  intro b hb hbT ω r hr
  exact ((hHc ω _ (hrt r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hbT))).comp
    real_time_clamp_continuous.continuousAt).continuousWithinAt

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.shifted_power_process_regularity
#print axioms Asakura.Chapter3Complete.shifted_power_process_monotone
#print axioms Asakura.Chapter3Complete.open_process_real_regularity
