import Chapter11IntervalExit

open Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma eventually_inside_barrier_compacts (y : ℝ) (hy : y<0) :
    ∀ᶠ n : ℕ in atTop,-(n:ℝ)<y ∧ y< -(1/((n:ℝ)+1)) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (-y)
  have hl : Tendsto (fun n : ℕ => -(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).neg
  filter_upwards [eventually_ge_atTop k,hl.eventually (eventually_gt_nhds hy)] with n hn hny
  have hkn : (k:ℝ)≤n := by exact_mod_cast hn
  exact ⟨by linarith,hny⟩

/-- Boundary continuity removes the compact spatial stops for any
 candidate, rather than only for the explicitly constructed heat solution. -/
theorem barrier_candidate_spatial_limit
    (X : HalfClosedTime → ℝ) (hc : ∀ t,t<⊤ → ContinuousAt X t) (h0 : X ⊥<0)
    (R : ℝ) (hR : 0≤R) (v : ℝ × ℝ → ℝ)
    (hv : ContinuousOn v (Icc 0 R ×ˢ Iic 0)) :
    Tendsto (fun n : ℕ =>
      let ρ := min (intervalExit X (-(n:ℝ)) (-(1/((n:ℝ)+1)))) (realTimeClamp R)
      v ((halfTimeReal ρ : ℝ),X ρ)) atTop
      (𝓝 (v ((halfTimeReal (min (upperBarrierHit X) (realTimeClamp R)) : ℝ),
        X (min (upperBarrierHit X) (realTimeClamp R))))) := by
  let σ := fun n : ℕ => min (intervalExit X (-(n:ℝ)) (-(1/((n:ℝ)+1)))) (realTimeClamp R)
  let τ := min (upperBarrierHit X) (realTimeClamp R)
  have hRt := real_time_below R hR (EReal.coe_lt_top R)
  have hσt n : σ n<⊤ := (min_le_right _ _).trans_lt hRt
  have hτt : τ<⊤ := (min_le_right _ _).trans_lt hRt
  have hcoord (t : HalfClosedTime) (ht : t<⊤) : realTimeClamp (halfTimeReal t : ℝ)=t := by
    obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
    rw [changed_time_real r hr]
  have htime (t : HalfClosedTime) (ht : t≤realTimeClamp R) : (halfTimeReal t : ℝ)∈Icc 0 R := by
    refine ⟨(halfTimeReal t).property,?_⟩
    have hh := half_time_real_mono ht hRt
    change (halfTimeReal t : ℝ)≤(halfTimeReal (realTimeClamp R) : ℝ) at hh
    simpa only [changed_time_real R hR] using hh
  have hlim : Tendsto σ atTop (𝓝 τ) := barrier_compact_exit_limit X hc _ hRt
  have hp : Tendsto (fun n => ((halfTimeReal (σ n) : ℝ),X (σ n))) atTop
      (𝓝[Icc 0 R ×ˢ Iic 0] ((halfTimeReal τ : ℝ),X τ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact ((changed_time_coordinate_continuousAt τ hτt).tendsto.comp hlim).prodMk_nhds
        ((hc τ hτt).tendsto.comp hlim)
    · filter_upwards [eventually_inside_barrier_compacts (X ⊥) h0] with n hn
      have hb := before_interval_exit_bounds X hc _ _ hn (halfTimeReal (σ n) : ℝ)
        (halfTimeReal (σ n)).property (by rw [hcoord _ (hσt n)];exact min_le_left _ _)
      rw [hcoord _ (hσt n)] at hb
      exact ⟨htime _ (min_le_right _ _),hb.2.trans (neg_nonpos.mpr (by positivity))⟩
  have hτmem : ((halfTimeReal τ : ℝ),X τ)∈Icc 0 R ×ˢ Iic 0 := by
    refine ⟨htime _ (min_le_right _ _),?_⟩
    have hh := before_upper_hit_nonpos X hc h0 (halfTimeReal τ : ℝ) (halfTimeReal τ).property
      (by rw [hcoord τ hτt];exact min_le_left _ _)
    simpa only [hcoord τ hτt, mem_Iic] using hh
  exact (hv _ hτmem).tendsto.comp hp

end Asakura.Chapter11
