import FullAuditFiniteBrownianHitting
import FullAuditContinuousDoob
import Chapter2BrownianSquare

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The already established maximal inequality bounds the probability of
leaving [-1,1] on a short interval. Applying the weak inequality to B²
even gives T, and hence in particular the 4T bound used in the text. -/
theorem brownian_small_time_failure
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (T : ℝ≥0) :
    P.real {w | ∃ t : ℝ≥0,t ≤ T ∧ 1 < |B t w|} ≤ (T:ℝ) := by
  letI : Fact (0 ≤ ((T:ℝ):EReal)) := ⟨by exact_mod_cast T.property⟩
  let ρ := finiteTimeToNNReal T
  let F := fun t => Asakura.nullAugmentation P (pastSigma B (ρ t))
  let X := fun t w => B (ρ t) w^2
  have hF : Monotone F := fun s t hst => null_augmentation_mono P
    (past_sigma_mono B (finite_time_to_nnreal_mono T hst))
  have hl t : F t ≤ m := fun _ he => he.1
  have hmX t : Measurable[F t] (X t) := (natural_augmented_adapted P B hm (ρ t)).pow_const 2
  have hi u : Integrable (fun w => B u w^2) P := by
    have h2 := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
    exact (memLp_two_iff_integrable_sq h2.aestronglyMeasurable).mp h2
  have hρT : ρ ⟨(T:ℝ),Fact.out,le_rfl⟩ = T := by
    apply Subtype.ext
    exact EReal.toReal_coe _
  have hdom t : X t ≤ᵐ[P] P[X ⟨(T:ℝ),Fact.out,le_rfl⟩|F t] := by
    have hs := brownian_square_augmented_martingale P B hB hm (ρ t) T (finite_time_to_nnreal_le T t)
    have hsub := condExp_sub (hi T) (integrable_const (μ := P) (T:ℝ)) (F t)
    have hconst := condExp_of_stronglyMeasurable (hl t) stronglyMeasurable_const (integrable_const (μ := P) (T:ℝ))
    filter_upwards [hs,hsub] with w hs hsub
    change P[(fun w => B T w^2-(T:ℝ))|F t] w = B (ρ t) w^2-(ρ t:ℝ) at hs
    change P[(fun w => B T w^2-(T:ℝ))|F t] w = P[(fun w => B T w^2)|F t] w-P[(fun _ => (T:ℝ))|F t] w at hsub
    rw [hconst] at hsub
    change B (ρ t) w^2 ≤ P[(fun w => B (ρ ⟨(T:ℝ),Fact.out,le_rfl⟩) w^2)|F t] w
    rw [hρT]
    have hle := finite_time_to_nnreal_le T t
    exact_mod_cast (show B (ρ t) w^2 ≤ P[(fun w => B T w^2)|F t] w from by
      have hh : (ρ t:ℝ) ≤ (T:ℝ) := hle
      linarith)
  have hmax := continuous_doob_weak_written P (Fact.out : 0 ≤ ((T:ℝ):EReal)) F hF hl X hmX
    (fun w t => (((hc w).comp (finite_time_to_nnreal_continuous T)).pow 2).continuousAt.continuousWithinAt)
    (hi _) (fun t => ae_of_all _ fun w => sq_nonneg _) hdom 1 (by norm_num)
  let A := {w | ENNReal.ofReal (1:ℝ) ≤ ⨆ t,ENNReal.ofReal (X t w)}
  have hint : (∫ w in A,X ⟨(T:ℝ),Fact.out,le_rfl⟩ w ∂P) ≤ (T:ℝ) := by
    calc
      _ ≤ ∫ w,X ⟨(T:ℝ),Fact.out,le_rfl⟩ w ∂P := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun w => sq_nonneg _) (hi _)
      _ = (T:ℝ) := by change (∫ w,B (ρ _) w^2 ∂P) = _; rw [hρT]; exact brownian_square_mean P B hB T
  have hsub : {w | ∃ t : ℝ≥0,t ≤ T ∧ 1 < |B t w|} ⊆ A := by
    rintro w ⟨t,ht,hv⟩
    let s : ClosedTime (T:ℝ) := ⟨(t:ℝ),by exact_mod_cast t.property,by exact_mod_cast ht⟩
    have hs : ρ s = t := by apply Subtype.ext; exact EReal.toReal_coe _
    apply le_trans (b := ENNReal.ofReal (X s w)) _ (le_iSup (fun t : ClosedTime (T:ℝ) => ENNReal.ofReal (X t w)) s)
    apply ENNReal.ofReal_le_ofReal
    change 1 ≤ B (ρ s) w^2
    rw [hs]
    nlinarith [sq_abs (B t w)]
  have hreal := ENNReal.toReal_mono (measure_ne_top P A) (measure_mono hsub)
  change P.real {w | ∃ t : ℝ≥0,t ≤ T ∧ 1 < |B t w|} ≤ P.real A at hreal
  norm_num only [inv_one,one_mul] at hmax
  exact hreal.trans (hmax.trans hint)

end Asakura.Chapter7
