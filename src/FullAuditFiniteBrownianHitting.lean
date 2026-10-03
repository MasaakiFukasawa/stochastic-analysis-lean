import FullAuditHittingExercise
import FullAuditBrownianMartingaleExercise

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology NNReal
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

noncomputable def finiteTimeToNNReal (T : ℝ≥0) (t : ClosedTime (T:ℝ)) : ℝ≥0 :=
  ⟨t.val.toReal,EReal.toReal_nonneg t.property.1⟩

theorem finite_time_to_nnreal_continuous (T : ℝ≥0) : Continuous (finiteTimeToNNReal T) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : t.val ≠ ⊤ := ne_of_lt (t.property.2.trans_lt (EReal.coe_lt_top _))
  have hb : t.val ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe 0).trans_le t.property.1)
  exact (EReal.tendsto_toReal ht hb).comp continuous_subtype_val.continuousAt

theorem finite_time_to_nnreal_mono (T : ℝ≥0) : Monotone (finiteTimeToNNReal T) := by
  intro s t hst
  exact EReal.toReal_le_toReal hst
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le s.property.1))
    (ne_of_lt (t.property.2.trans_lt (EReal.coe_lt_top _)))

theorem finite_time_to_nnreal_le (T : ℝ≥0) (t : ClosedTime (T:ℝ)) : finiteTimeToNNReal T t ≤ T := by
  have h := EReal.toReal_le_toReal t.property.2
    (ne_of_gt ((EReal.bot_lt_coe 0).trans_le t.property.1)) (EReal.coe_ne_top _)
  change t.val.toReal ≤ (T:ℝ)
  simpa only [EReal.toReal_coe] using h

/-- Full corrected Brownian hitting exercise: for every finite horizon, the
 event of not yet reaching 1 has strictly positive probability. Thus the
 hitting time on the half-line has no deterministic finite upper bound. -/
theorem brownian_hitting_time_unbounded {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (T : ℝ≥0) :
    0 < P {ω | ∀ t : ℝ≥0, t ≤ T → B t ω ≠ 1} := by
  letI : Fact (0 ≤ ((T:ℝ):EReal)) := ⟨by exact_mod_cast T.property⟩
  let ρ := finiteTimeToNNReal T
  let X := fun t ω => B (ρ t) ω
  let F := fun t => pastSigma B (ρ t)
  have hzρ : ρ ⊥ = 0 := by
    apply Subtype.ext
    change (0:EReal).toReal = (0:ℝ)
    rfl
  have hz : X ⊥ =ᵐ[P] 0 := by
    change (fun ω => B (ρ ⊥) ω) =ᵐ[P] (fun _ => 0)
    rw [hzρ]
    exact hB.eval_zero_ae_eq_zero
  have h := nonzero_level_not_hit_by_terminal P F ((past_sigma_mono B).comp (finite_time_to_nnreal_mono T))
    (fun t => past_sigma_le B hm (ρ t)) X (fun t => natural_process_adapted B (ρ t))
    (fun t => hB.integrable_eval (ρ t)) (fun ω => (hc ω).comp (finite_time_to_nnreal_continuous T))
    (fun s t hst => brownian_natural_martingale_written P B hB hm _ _ (finite_time_to_nnreal_mono T hst)) hz 1 (by norm_num)
  apply lt_of_lt_of_le h (measure_mono _)
  intro ω hω t ht
  let s : ClosedTime (T:ℝ) := ⟨(t:ℝ),by exact_mod_cast t.property,by exact_mod_cast ht⟩
  have hs : ρ s = t := by
    apply Subtype.ext
    change ((t:ℝ):EReal).toReal = (t:ℝ)
    exact EReal.toReal_coe _
  simpa only [X,hs] using hω s

end Asakura.FullAudit
