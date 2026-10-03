import FullAuditPositivePartLimit
import FullAuditQVConvex

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Countably many dyadic inequalities give a single exceptional null set;
 continuity extends them to every pair of times, including infinity. -/
theorem monotone_paths_from_qv_grids {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) {T : EReal} [Fact (0 ≤ T)]
    (A : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => A t ω))
    (hD : ∀ n, ∀ s ∈ range (qvPartition (T := T) n), ∀ t ∈ range (qvPartition n),
      s ≤ t → A s ≤ᵐ[P] A t) : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) := by
  let D := ⋃ n : ℕ, range (qvPartition (T := T) n)
  have hcount : D.Countable := countable_iUnion fun n => countable_range _
  have hpair : ∀ s ∈ D, ∀ t ∈ D, s ≤ t → A s ≤ᵐ[P] A t := by
    intro s hs t ht hst
    obtain ⟨i,hi⟩ := mem_iUnion.mp hs
    obtain ⟨j,hj⟩ := mem_iUnion.mp ht
    exact hD (max i j) s (qv_partition_refinement (le_max_left _ _) hi)
      t (qv_partition_refinement (le_max_right _ _) hj) hst
  have hall : ∀ᵐ ω ∂P, ∀ s ∈ D, ∀ t ∈ D, s ≤ t → A s ω ≤ A t ω := by
    apply (ae_ball_iff hcount).mpr
    intro s hs
    apply (ae_ball_iff hcount).mpr
    intro t ht
    by_cases hst : s ≤ t
    · exact (hpair s hs t ht hst).mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h => False.elim (hst h)
  filter_upwards [hall] with ω hω
  intro s t hst
  rcases lt_or_eq_of_le hst with hst | rfl
  · have hlimS := (hc ω).tendsto s |>.comp (gridTime_tendsto s)
    have hlimT := (hc ω).tendsto t |>.comp (gridTime_tendsto t)
    apply le_of_tendsto_of_tendsto hlimS hlimT
    filter_upwards [(gridTime_tendsto s).eventually_lt (gridTime_tendsto t) hst] with n hn
    exact hω (gridTime n s) (mem_iUnion.mpr ⟨n,grid_time_in_qv_partition n s⟩)
      (gridTime n t) (mem_iUnion.mpr ⟨n,grid_time_in_qv_partition n t⟩) hn.le
  · exact le_rfl

/-- Doob's inequality transfers terminal L2 convergence to each observation
 time, using the actual continuous martingale representatives. -/
theorem m2_terminal_limit_at_time {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (U : ℕ → ClosedTime T → Ω → ℝ) (Y : ClosedTime T → Ω → ℝ)
    (hU : ∀ n, ContinuousM2Witness P F (U n)) (hY : ContinuousM2Witness P F Y)
    (ht : Tendsto (fun n => eLpNorm (U n ⊤-Y ⊤) 2 P) atTop (𝓝 0)) (t : ClosedTime T) :
    Tendsto (fun n => eLpNorm (U n t-Y t) 2 P) atTop (𝓝 0) := by
  have hb (n) : eLpNorm (U n t-Y t) 2 P ≤ 2*eLpNorm (U n ⊤-Y ⊤) 2 P := by
    have h := continuous_martingale_path_difference_bound P F hF hle (U n) Y
      (hU n).adapted hY.adapted (hU n).moment hY.moment (hU n).path hY.path
      (hU n).martingale hY.martingale
    apply le_trans _ h
    apply eLpNorm_mono_ae (((hU n).moment t).sub (hY.moment t)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => ContinuousMap.norm_coe_le_norm
      (continuousPath (U n) (hU n).path ω-continuousPath Y hY.path ω) t
  have hlim : Tendsto (fun n => 2*eLpNorm (U n ⊤-Y ⊤) 2 P) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr (by norm_num : (2:ℝ≥0∞) ≠ ∞))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

end Asakura.FullAudit
