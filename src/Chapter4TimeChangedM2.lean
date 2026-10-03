import Chapter3InitialWeight

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic increasing continuous time change, with the starting
value removed, preserves an actual continuous square-integrable martingale. -/
theorem continuous_m2_time_change_increment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T S : EReal} [Fact (0≤T)] [Fact (0≤S)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (φ : ClosedTime S → ClosedTime T) (hφ : Monotone φ) (hcφ : Continuous φ)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) :
    ContinuousM2Witness P (fun t => F (φ t)) (fun t w => X (φ t) w-X (φ ⊥) w) := by
  have hx0 t : Measurable[F (φ t)] (X (φ ⊥)) := (hX.adapted _).mono (hF (hφ bot_le)) le_rfl
  refine ⟨fun t => (hX.adapted _).sub (hx0 t),fun t => (hX.moment _).sub (hX.moment _),
    fun w => ((hX.path w).comp hcφ).sub continuous_const,?_,?_⟩
  · intro s t hst
    have hsub := condExp_sub ((hX.moment (φ t)).integrable (by norm_num))
      ((hX.moment (φ ⊥)).integrable (by norm_num)) (F (φ s))
    have hz : P[X (φ ⊥) | F (φ s)]=X (φ ⊥) :=
      condExp_of_stronglyMeasurable (hle _) (hx0 s).stronglyMeasurable ((hX.moment _).integrable (by norm_num))
    rw [hz] at hsub
    exact hsub.trans ((hX.martingale _ _ (hφ hst)).sub Filter.EventuallyEq.rfl)
  · exact Filter.Eventually.of_forall (fun w => sub_self _)

lemma bounded_martingale_time_change_increment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T S : EReal} [Fact (0≤T)] [Fact (0≤S)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (φ : ClosedTime S → ClosedTime T) (hφ : Monotone φ) (hcφ : Continuous φ)
    (X : ClosedTime T → Ω → ℝ) (hX : X∈boundedMProcess P F) :
    (fun t w => X (φ t) w-X (φ ⊥) w)∈boundedMProcess P (fun t => F (φ t)) :=
  ⟨continuous_m2_time_change_increment P F hF hle φ hφ hcφ X hX.1,
    fun t => (hX.2 (φ t)).sub (hX.2 (φ ⊥))⟩

end Asakura.Chapter4
