import FullAuditMartingalePathNorm
import FullAuditLpComplete
import Chapter6ExponentialLocal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The local-to-global Doob step in the Novikov argument. The path norm
bound is derived from terminal stopped moments and Fatou; it is not an input. -/
theorem positive_local_path_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M : ClosedTime T → Ω → ℝ) (ha : ∀ t,Measurable[F t] (M t))
    (hc : ∀ w,Continuous (fun t => M t w)) (hp : ∀ t w,0 ≤ M t w)
    (hL : LocalMProcessWitness P F (fun t w => M t w-1))
    (τ : Ω → ClosedTime T) (hτt : ∀ w,τ w < ⊤)
    (hconst : ∀ w t,M (min (τ w) t) w = M t w)
    (p : ℝ) (hpp : 1 < p) (K : ℝ≥0∞)
    (hmoment : ∀ σ : Ω → ClosedTime T,
      (∀ t,MeasurableSet[F t] {w | σ w ≤ t}) → (∀ w,σ w < ⊤) →
      (∫⁻ w,ENNReal.ofReal (M (σ w) w)^p ∂P) ≤ K) :
    eLpNorm (continuousPath M hc) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p/(p-1))*K^(1/p) := by
  have hp0 : 0 < p := by linarith
  have hep : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  obtain ⟨σ,hs,hm,ht,hco,hb⟩ := hL.localizers
  let N := fun n t w => M (min (σ n w) t) w
  have hna n t : Measurable[F t] (N n t) := by
    have hh := ((hb n).1.adapted t).add (measurable_const (a := (1:ℝ)))
    convert hh using 1
    funext w
    simp only [N,Pi.add_apply,sub_add_cancel]
  have hnc n w : Continuous (fun t => N n t w) := (hc w).comp (continuous_const.min continuous_id)
  have hni n t : Integrable (N n t) P := by
    have hh := (((hb n).1.moment t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).add (integrable_const (1:ℝ))
    convert hh using 1
    funext w
    simp only [N,Pi.add_apply,sub_add_cancel]
  have hnm n s t (hst : s ≤ t) : P[N n t|F s] =ᵐ[P] N n s := by
    have hi := ((hb n).1.moment t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
    have hh := condExp_add hi (integrable_const (1:ℝ)) (m := F s)
    filter_upwards [hh,(hb n).1.martingale s t hst] with w hw hm
    change P[(fun w => (M (min (σ n w) t) w-1)+1)|F s] w =
      P[(fun w => M (min (σ n w) t) w-1)|F s] w+P[(fun _ => (1:ℝ))|F s] w at hw
    simp only [sub_add_cancel,condExp_const (μ := P) (hle s) (1:ℝ),hm] at hw
    exact hw
  have hnmPath n := continuous_path_measurable (N n) (hnc n) (fun t => (hna n t).mono (hle t) le_rfl)
  have hbound n : eLpNorm (continuousPath (N n) (hnc n)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p/(p-1))*K^(1/p) := by
    have hh := continuous_doob_strong_written P (Fact.out : 0 ≤ T) F hF hle (N n) (hna n)
      (fun w t => (hnc n w).continuousAt.continuousWithinAt) (hni n ⊤)
      (fun t => .of_forall (fun w => hp _ w))
      (fun t => (hnm n t ⊤ le_top).symm.le) p hpp
    have hen w : ‖continuousPath (N n) (hnc n) w‖ₑ = ⨆ t,ENNReal.ofReal (N n t w) := by
      rw [ContinuousMap.enorm_eq_iSup_enorm]
      simp only [continuousPath,ContinuousMap.coe_mk,← ofReal_norm,N,Real.norm_of_nonneg (hp _ _)]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hep ENNReal.ofReal_ne_top (hnmPath n).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp0.le,hen]
    have htop : (⟨T,(Fact.out : 0 ≤ T),le_rfl⟩ : ClosedTime T) = ⊤ := rfl
    simp only [htop,N,min_top_right] at hh
    exact hh.trans (mul_le_mul_right (ENNReal.rpow_le_rpow (hmoment (σ n) (hs n) (ht n)) (by positivity)) _)
  apply current_lp_eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (.of_forall hbound)
    (fun n => (hnmPath n).aestronglyMeasurable)
    (continuous_path_measurable M hc (fun t => (ha t).mono (hle t) le_rfl)).aestronglyMeasurable
  apply ae_of_all
  intro w
  obtain ⟨n,hn⟩ := hco w (τ w) (hτt w)
  apply tendsto_const_nhds.congr'
  apply eventually_atTop.mpr
  refine ⟨n,fun k hk => ?_⟩
  apply ContinuousMap.ext
  intro t
  change M t w = M (min (σ k w) t) w
  rw [← hconst w t,← hconst w (min (σ k w) t),← min_assoc,
    min_eq_left (hn.le.trans (hm w hk))]

end Asakura.Chapter6
