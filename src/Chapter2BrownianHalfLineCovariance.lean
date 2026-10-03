import Chapter2HalfLineLocalization
import Chapter2LocalCovarianceRules

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The Brownian exercise on [0,infinity), with the augmented natural
filtration and the actual local-covariation characterization. The artificial
value of halfTimeReal at infinity is never used by a local witness. -/
theorem brownian_half_line_local_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) :
    let F := halfClosedFiltration m (fun t => Asakura.nullAugmentation P (pastSigma B t))
    let X := fun t ω => B (halfTimeReal t) ω
    LocalMProcessWitness P F X ∧
      LocalCovarianceWitness P F X X (fun t _ => (halfTimeReal t : ℝ)) := by
  intro F X
  let F0 := fun t => Asakura.nullAugmentation P (pastSigma B t)
  have hF0 : Monotone F0 := fun s t hst => null_augmentation_mono P (past_sigma_mono B hst)
  have hle0 t : F0 t ≤ m := fun _ h => h.1
  obtain ⟨had,hi,_,hM⟩ := brownian_martingale_exercise P B hB hm hc 2 (by norm_num)
  have hX := half_line_martingale_local P F0 hF0 hle0 B had hi hc hM hB.eval_zero_ae_eq_zero
  let Z := fun t ω => B t ω^2-(t:ℝ)
  have hZa t : Measurable[F0 t] (Z t) := ((had t).pow_const 2).sub measurable_const
  have hZi t : MemLp (Z t) 2 P := brownian_square_centered_memLp_two P B hB t
  have hZc ω : Continuous (fun t => Z t ω) := ((hc ω).pow 2).sub continuous_subtype_val
  have hZm : ∀ s t, s ≤ t → P[Z t | F0 s] =ᵐ[P] Z s :=
    brownian_square_augmented_martingale P B hB hm
  have hZ0 : Z 0 =ᵐ[P] 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp only [Z,hω,NNReal.coe_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,Pi.zero_apply]
  have hZ := half_line_martingale_local P F0 hF0 hle0 Z hZa hZi hZc hZm hZ0
  refine ⟨hX,?_,?_⟩
  · simpa only [Z,X,pow_two] using hZ
  · obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion (show (0:EReal) < ⊤ by simp)
    refine ⟨fun n _ => u n,?_,fun _ => hu,fun n _ => hut n,fun _ => huc,?_⟩
    · intro n t
      by_cases ht : u n ≤ t <;> simp [ht]
    · intro n ω
      refine ⟨fun t => (halfTimeReal (min (u n) t):ℝ),fun _ => 0,?_,monotone_const,?_⟩
      · intro s t hst
        exact half_time_real_mono ((monotone_const.min monotone_id) hst) ((min_le_left _ _).trans_lt (hut n))
      · intro t
        simp only [sub_zero]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.brownian_half_line_local_covariance
