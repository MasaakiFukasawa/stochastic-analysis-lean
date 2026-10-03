import Chapter2LocalCovarianceRules

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Stopping strictly before the open endpoint gives an adapted continuous
process on the closed time interval, without a terminal integrability assumption. -/
theorem LocalMProcessWitness.stopped_regular
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) :
    (∀ t, Measurable[F t] (fun ω => X (min (σ ω) t) ω)) ∧
    (∀ ω, Continuous (fun t => X (min (σ ω) t) ω)) := by
  obtain ⟨τ,ht,hm,htt,hc,hXτ⟩ := hX.localizers
  constructor
  · intro t
    let Z := fun n r ω => X (min (τ n ω) (min (σ ω) r)) ω
    have hZ (n) := continuous_m2_stopped P F hF hle _ (hXτ n).1 σ hσ
    apply @glued_value_measurable Ω (F t) (fun n ω => Z n t ω)
      (fun n => (hZ n).adapted t)
    intro ω
    obtain ⟨n,hn⟩ := hc ω (σ ω) (hσtop ω)
    refine eventually_atTop.2 ⟨n,fun k hk => ?_⟩
    dsimp [Z]
    rw [← min_assoc,min_eq_right (hn.le.trans (hm ω hk))]
  · intro ω
    apply continuous_iff_continuousAt.2
    intro t
    exact (hX.path P F ω _ ((min_le_left _ _).trans_lt (hσtop ω))).comp
      (continuous_const.min continuous_id).continuousAt

/-- The same regularity for the actual covariance process follows from
XY-C being local, not from an additional regularity hypothesis on C. -/
theorem LocalCovarianceWitness.stopped_regular
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X Y C : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) :
    (∀ t, Measurable[F t] (fun ω => C (min (σ ω) t) ω)) ∧
    (∀ ω, Continuous (fun t => C (min (σ ω) t) ω)) := by
  obtain ⟨hxm,hxc⟩ := hX.stopped_regular P F hF hle σ hσ hσtop
  obtain ⟨hym,hyc⟩ := hY.stopped_regular P F hF hle σ hσ hσtop
  obtain ⟨hdm,hdc⟩ := hC.defect.stopped_regular P F hF hle σ hσ hσtop
  constructor
  · intro t
    have h := ((hxm t).mul (hym t)).sub (hdm t)
    convert h using 1
    funext u
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  · intro ω
    have h := ((hxc ω).mul (hyc ω)).sub (hdc ω)
    convert h using 1
    funext u
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.stopped_regular
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.stopped_regular
