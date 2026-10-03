import Chapter7BrownianExists

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def naturalBrownianSystem
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w)) :
    BrownianSystem P 1 := by
  let F0 := fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)
  let F := halfClosedFiltration m F0
  have hF0 : Monotone F0 := fun s t hst => null_augmentation_mono P (past_sigma_mono B hst)
  have hl t : F0 t ≤ m := fun _ he => he.1
  have hMC := brownian_half_line_local_covariance P B hB hm hc
  refine {
    F := F
    mono := half_closed_filtration_mono m F0 hF0 hl
    le := half_closed_filtration_le m F0 hl
    null := ?_
    W := fun _ t w => B (halfTimeReal t) w
    C := fun _ _ t _ => (halfTimeReal t:ℝ)
    martingale := fun _ => hMC.1
    cov := fun _ _ => hMC.2
    clock := ?_ }
  · intro t N hmN hzN
    by_cases ht : t < ⊤
    · have hi : F0 (halfTimeReal t) ≤ F t := by simp only [F,halfClosedFiltration,if_pos ht,le_refl]
      exact hi N (null_augmentation_null P (pastSigma B (halfTimeReal t)) N hmN hzN)
    · have hi : m ≤ F t := by simp only [F,halfClosedFiltration,if_neg ht,le_refl]
      exact hi N hmN
  · intro j k w r hr
    have hjk : j = k := Subsingleton.elim _ _
    simp only [hjk,if_true]
    exact changed_time_real r hr


end Asakura.Chapter7
