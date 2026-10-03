import Chapter2BrownianSquare
import FullAuditFiniteBrownianHitting
import Chapter2LocalCovarianceRules

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology NNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- On every positive finite time interval the Brownian process is an
actual continuous L2 martingale, and time itself satisfies the defining
local-covariation conditions. The square martingale calculation is proved
from independent increments in Chapter2BrownianSquare. -/
theorem brownian_finite_local_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (b : ℝ≥0) (hb : 0 < b) [Fact (0 ≤ ((b:ℝ):EReal))] :
    let ρ := finiteTimeToNNReal b
    let F := fun t => pastSigma B (ρ t)
    let X := fun t ω => B (ρ t) ω
    ContinuousM2Witness P F X ∧ LocalMProcessWitness P F X ∧
      LocalCovarianceWitness P F X X (fun t _ => (ρ t : ℝ)) := by
  intro ρ F X
  letI : MeasurableSpace Ω := m
  have hF : Monotone F := (past_sigma_mono B).comp (finite_time_to_nnreal_mono b)
  have hle t : F t ≤ m := past_sigma_le B hm (ρ t)
  have hzρ : ρ ⊥ = 0 := by
    apply Subtype.ext
    change (0:EReal).toReal = (0:ℝ)
    rfl
  have hρc := finite_time_to_nnreal_continuous b
  have hρm := finite_time_to_nnreal_mono b
  have hz : X ⊥ =ᵐ[P] 0 := by
    change (fun ω => B (ρ ⊥) ω) =ᵐ[P] (fun _ => 0)
    rw [hzρ]
    exact hB.eval_zero_ae_eq_zero
  have hX : ContinuousM2Witness P F X :=
    ⟨fun t => natural_process_adapted B (ρ t),
      fun t => (hB.isGaussianProcess.hasGaussianLaw_eval (ρ t)).memLp_two,
      fun ω => (hc ω).comp hρc,
      fun s t hst => brownian_natural_martingale_written P B hB hm _ _ (hρm hst),hz⟩
  have hT : (0:EReal) < (b:ℝ) := by exact_mod_cast hb
  obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion hT
  have hXloc := continuous_m2_is_local P F hF hle u hu hut huc X hX
  let Z := fun t ω => B (ρ t) ω ^ 2-(ρ t : ℝ)
  have hZ : ContinuousM2Witness P F Z := by
    refine ⟨fun t => ((natural_process_adapted B (ρ t)).pow_const 2).sub measurable_const,
      fun t => brownian_square_centered_memLp_two P B hB (ρ t),
      fun ω => ((hc ω).comp hρc).pow 2 |>.sub (continuous_subtype_val.comp hρc),
      fun s t hst => brownian_square_natural_martingale P B hB hm _ _ (hρm hst),?_⟩
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    change B (ρ ⊥) ω ^ 2-(ρ ⊥ : ℝ) = 0
    rw [hzρ,hω]
    norm_num
  refine ⟨hX,hXloc,?_,?_⟩
  · have h := continuous_m2_is_local P F hF hle u hu hut huc Z hZ
    simpa only [Z,X,pow_two] using h
  · refine ⟨fun n _ => u n,?_,fun _ => hu,fun n _ => hut n,fun _ => huc,?_⟩
    · intro n t
      by_cases ht : u n ≤ t <;> simp [ht]
    · intro n ω
      refine ⟨fun t => (ρ (min (u n) t) : ℝ),fun _ => 0,?_,monotone_const,?_⟩
      · exact (fun s t hst => hρm ((monotone_const.min monotone_id) hst))
      · intro t
        simp only [sub_zero]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.brownian_finite_local_covariance
