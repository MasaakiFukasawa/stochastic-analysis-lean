import FullAuditQVSequence
import FullAuditQVLimit

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's Hilbert-space convex-tail proof constructs a continuous
 martingale Y with X squared minus Y increasing outside one common null set. -/
theorem qv_exists_ae_monotone {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hTop : ∀ t, MemLp (X t) ∞ P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0) :
    ∃ Y, ContinuousM2Witness P F Y ∧
      (∀ᵐ ω ∂P, Monotone (fun t => X t ω^2-Y t ω)) ∧
      eLpNorm (Y ⊤) 2 P ≤ ENNReal.ofReal (2*(eLpNorm (X ⊤) ∞ P).toReal*Real.sqrt (∫ ω, X ⊤ ω^2 ∂P)) := by
  letI : CompleteSpace (continuousM2Terminal P F) := continuous_m2_hilbert_complete P F hF hle hnull
  let R := 2*(eLpNorm (X ⊤) ∞ P).toReal*Real.sqrt (∫ ω, X ⊤ ω^2 ∂P)
  obtain ⟨f,hf,hfg⟩ := qv_bounded_terminal_sequence P F hF hle X hm hTop hc hmart hz
  obtain ⟨g,v,hg,hgv⟩ := convergent_convex_tails f R hf
  have hgrid := convex_tail_grid_representatives P F X f g hfg hg
  choose U hU hterm hUG using hgrid
  obtain ⟨Y,hY,hyterm⟩ := v.property
  have heU (n) : ((hU n).moment ⊤).toLp (U n ⊤) = (g n : Lp ℝ 2 P) := by
    apply Lp.ext
    exact ((hU n).moment ⊤).coeFn_toLp.trans (hterm n)
  have heY : (hY.moment ⊤).toLp (Y ⊤) = (v : Lp ℝ 2 P) := by
    apply Lp.ext
    exact (hY.moment ⊤).coeFn_toLp.trans hyterm
  have ht : Tendsto (fun n => eLpNorm (U n ⊤-Y ⊤) 2 P) atTop (𝓝 0) := by
    apply (current_lp_tendsto_Lp_iff_tendsto_eLpNorm_prime_prime (fun n => U n ⊤)
      (fun n => (hU n).moment ⊤) (Y ⊤) (hY.moment ⊤)).mp
    simp only [heU,heY]
    exact continuous_subtype_val.tendsto v |>.comp hgv
  have htime (t) := m2_terminal_limit_at_time P F hF hle U Y hU hY ht t
  have hA : ∀ᵐ ω ∂P, Monotone (fun t => X t ω^2-Y t ω) := by
    apply monotone_paths_from_qv_grids P _ (fun ω => ((hc ω).pow 2).sub (hY.path ω))
    intro n s hs t hts hst
    have horder : ∀ᶠ k in atTop, (fun ω => X s ω^2-U k s ω) ≤ᵐ[P] (fun ω => X t ω^2-U k t ω) := by
      filter_upwards [eventually_ge_atTop n] with k hk
      exact hUG k s (qv_partition_refinement hk hs) t (qv_partition_refinement hk hts) hst
    have hmeas (k s) : AEStronglyMeasurable (fun ω => X s ω^2-U k s ω) P :=
      (((hm s).mono (hle s) le_rfl).pow_const 2).aestronglyMeasurable.sub ((hU k).moment s).aestronglyMeasurable
    have hmeasY (s) : AEStronglyMeasurable (fun ω => X s ω^2-Y s ω) P :=
      (((hm s).mono (hle s) le_rfl).pow_const 2).aestronglyMeasurable.sub (hY.moment s).aestronglyMeasurable
    apply ae_order_of_l2_limits P _ _ _ _ (fun k => hmeas k s) (fun k => hmeas k t)
      (hmeasY s) (hmeasY t) horder
    · have he (k) : (fun ω => X s ω^2-U k s ω)-(fun ω => X s ω^2-Y s ω) = Y s-U k s := by funext ω; simp
      simpa only [he,eLpNorm_sub_comm (Y s)] using htime s
    · have he (k) : (fun ω => X t ω^2-U k t ω)-(fun ω => X t ω^2-Y t ω) = Y t-U k t := by funext ω; simp
      simpa only [he,eLpNorm_sub_comm (Y t)] using htime t
  refine ⟨Y,hY,hA,?_⟩
  have hgn (n) : ‖g n‖ ≤ R := by
    apply mem_closedBall_zero_iff.mp
    apply convexHull_min _ (convex_closedBall (0 : continuousM2Terminal P F) R) (hg n)
    rintro z ⟨k,hk,rfl⟩
    exact mem_closedBall_zero_iff.mpr (hf k)
  have hv : ‖v‖ ≤ R := le_of_tendsto_of_tendsto (hgv.norm) tendsto_const_nhds (Eventually.of_forall hgn)
  have he : eLpNorm (Y ⊤) 2 P = ENNReal.ofReal ‖v‖ := by
    rw [← eLpNorm_congr_ae (hY.moment ⊤).coeFn_toLp,heY]
    change eLpNorm (v : Lp ℝ 2 P) 2 P = ENNReal.ofReal ‖(v : Lp ℝ 2 P)‖
    rw [Lp.norm_def,ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  rw [he]
  exact ENNReal.ofReal_le_ofReal hv

end Asakura.FullAudit
