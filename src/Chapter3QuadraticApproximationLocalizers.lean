import Chapter3ContinuousAdaptedWeights
import Chapter3QuadraticVariationRegularity
import Chapter2ExplicitLocalizers

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The common localizers used in the weighted quadratic approximation
are constructed by stopping |H-H₀|+Q. Both bounds follow from this one stop;
Q's positivity and its zero initial value are derived from its witness. -/
theorem quadratic_approximation_bounded_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n) :
    ∃ σ : ℕ → Ω → ClosedTime T,
      (∀ n t, MeasurableSet[F t] {ω | σ n ω ≤ t}) ∧
      (∀ ω, Monotone (fun n => σ n ω)) ∧ (∀ n ω, σ n ω < ⊤) ∧
      (∀ ω t, t < ⊤ → ∃ n, t < σ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t,
        |H (min (σ n ω) t) ω-H ⊥ ω| ≤ (n:ℝ) ∧
        0 ≤ Q (min (σ n ω) t) ω ∧ Q (min (σ n ω) t) ω ≤ (n:ℝ)) := by
  have hbot : (⊥ : ClosedTime T) < ⊤ := bot_le.trans_lt (hct 0)
  let W := fun t ω => |H t ω-H ⊥ ω|+Q t ω
  have hQm (t) (ht : t < ⊤) : Measurable[F t] (Q t) := by
    have h := ((hX.adapted P F t ht).mul (hX.adapted P F t ht)).sub (hQ.defect.adapted P F t ht)
    convert h using 1
    funext ω
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  have hWm (t) (ht : t < ⊤) : Measurable[F t] (W t) := by
    letI : MeasurableSpace Ω := F t
    have hh := (hHm t ht).sub ((hHm ⊥ hbot).mono (hF bot_le) le_rfl)
    have hn := hh.norm.add (hQm t ht)
    simpa only [W,Pi.add_def,Pi.sub_apply,Real.norm_eq_abs] using hn
  have hWc (ω t) (ht : t < ⊤) : ContinuousAt (fun s => W s ω) t := by
    exact ((hHc ω t ht).sub continuousAt_const).abs.add
      (covariance_continuous_at P F X X Q hX hX hQ ω t ht)
  have hW0 : W ⊥ =ᵐ[P] 0 := by
    filter_upwards [local_quadratic_variation_initial P F X Q hX hQ] with ω hω
    simpa only [W,sub_self,abs_zero,zero_add] using hω
  have hcm' : ∀ ω : Ω, Monotone (fun n => (fun _ : Ω => c n) ω) := fun _ => hcm
  have hcs (n t) : MeasurableSet[F t] {ω : Ω | c n ≤ t} := by
    by_cases ht : c n ≤ t <;> simp [ht]
  have hcapm (n t) : Measurable[F t] (fun ω => W (min (c n) t) ω) :=
    (hWm _ ((min_le_left _ _).trans_lt (hct n))).mono (hF (min_le_right _ _)) le_rfl
  have hcapc (n ω) : Continuous (fun t => W (min (c n) t) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hWc ω _ ((min_le_left _ _).trans_lt (hct n))).comp
      (continuous_const.min continuous_id).continuousAt
  have hz (n) : (fun ω => W (min (c n) ⊥) ω) =ᵐ[P] 0 := by
    simpa only [min_bot_right] using hW0
  obtain ⟨hs,hm,ht,hco,hb⟩ := explicit_continuous_process_bounded_localizers P F hF W
    (fun n _ => c n) hcs hcm' (fun n _ => hct n) (fun _ => hcc) hcapm hcapc hz
  refine ⟨_,hs,hm,ht,hco,?_⟩
  intro n
  filter_upwards [hb n,local_quadratic_variation_monotone P F hF hle hnull X Q hX hQ,
    local_quadratic_variation_initial P F X Q hX hQ] with ω hbω hmono hzero
  intro t
  let s := min (min (sInf {t | (n:ℝ) ≤ |W (min (c n) t) ω|}) (c n)) t
  have hst : s < ⊤ :=
    (min_le_left _ _).trans_lt (ht n ω)
  have hnonneg := hmono hbot hst bot_le
  dsimp only at hnonneg
  rw [show Q ⊥ ω = 0 from hzero] at hnonneg
  have hbound := hbω t
  change abs (abs (H s ω-H ⊥ ω)+Q s ω) ≤ (n:ℝ) at hbound
  change 0 ≤ Q s ω at hnonneg
  change |H s ω-H ⊥ ω| ≤ (n:ℝ) ∧ 0 ≤ Q s ω ∧ Q s ω ≤ (n:ℝ)
  have hab := (le_abs_self _).trans hbound
  exact ⟨by linarith,hnonneg,by linarith [abs_nonneg (H s ω-H ⊥ ω)]⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.quadratic_approximation_bounded_localizers
