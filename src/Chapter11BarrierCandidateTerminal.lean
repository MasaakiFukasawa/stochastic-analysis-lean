import Chapter11BarrierStoppedLimit

open Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Terminal passage for any candidate with the printed boundary
 continuity. No continuity at the excluded corner is assumed. -/
theorem barrier_candidate_terminal_limit
    (X : HalfClosedTime → ℝ) (hc : ∀ t,t<⊤ → ContinuousAt X t) (h0 : X ⊥<0)
    (T : ℝ) (hT : 0<T) (hne : X (realTimeClamp T)≠0)
    (v : ℝ → ℝ → ℝ) (payoff : ℝ → ℝ)
    (hboundary : ∀ t∈Ico 0 T,v t 0=0)
    (hterminal : ∀ y,y<0 → v T y=payoff y)
    (hcont : ∀ y,y<0 → ContinuousWithinAt (fun z : ℝ × ℝ => v z.1 z.2)
      (Icc 0 T ×ˢ Iic 0) (T,y)) :
    Tendsto (fun t : ℝ =>
      let ρ := min (upperBarrierHit X) (realTimeClamp t)
      v (halfTimeReal ρ : ℝ) (X ρ)) (𝓝[<] T)
      (𝓝 (if realTimeClamp T<upperBarrierHit X then payoff (X (realTimeClamp T)) else 0)) := by
  let τ := upperBarrierHit X
  have htT := real_time_below T hT.le (EReal.coe_lt_top T)
  by_cases hτ : τ<realTimeClamp T
  · obtain ⟨q,hq,hqt,hqe⟩ := finite_closed_time_real τ (hτ.trans htT)
    have hqT : q<T := by
      rw [←hqe] at hτ
      change (realTimeClamp q:EReal)<(realTimeClamp T:EReal) at hτ
      rw [real_time_clamp_eq q hq le_top,real_time_clamp_eq T hT.le le_top] at hτ
      exact EReal.coe_lt_coe_iff.mp hτ
    have hhit := at_upper_hit_zero X hc h0 (hτ.trans htT)
    rw [if_neg (not_lt_of_ge hτ.le)]
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_gt_nhds hqT).filter_mono nhdsWithin_le_nhds] with t ht
    have hτt : τ≤realTimeClamp t := by rw [←hqe];exact real_time_clamp_mono ht.le
    change (0:ℝ)=v (halfTimeReal (min τ (realTimeClamp t)) : ℝ) (X (min τ (realTimeClamp t)))
    rw [min_eq_left hτt,hhit,←hqe,changed_time_real q hq,hboundary q ⟨hq,hqT⟩]
  · have hTτ : realTimeClamp T≤τ := le_of_not_gt hτ
    have hx := before_upper_hit_nonpos X hc h0 T hT.le hTτ
    have hxneg : X (realTimeClamp T)<0 := lt_of_le_of_ne hx hne
    have hsurvive : realTimeClamp T<τ := lt_of_le_of_ne hTτ (by
      intro he
      have hτtop : τ<⊤ := by rw [←he];exact htT
      have hh := at_upper_hit_zero X hc h0 hτtop
      change X τ=0 at hh
      rw [←he] at hh
      exact hne hh)
    rw [if_pos hsurvive]
    have hpair : Tendsto (fun t : ℝ => (t,X (realTimeClamp t))) (𝓝[<] T)
        (𝓝[Icc 0 T ×ˢ Iic 0] (T,X (realTimeClamp T))) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · exact (continuousAt_id.prodMk ((hc _ htT).comp real_time_clamp_continuous.continuousAt)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin,(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht ht0
        exact ⟨⟨ht0.le,ht.le⟩,before_upper_hit_nonpos X hc h0 t ht0.le
          ((real_time_clamp_mono ht.le).trans hTτ)⟩
    have hl := (hcont _ hxneg).tendsto.comp hpair
    rw [hterminal _ hxneg] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin,(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht ht0
    have hle : realTimeClamp t≤τ := (real_time_clamp_mono ht.le).trans hTτ
    change v t (X (realTimeClamp t))=v (halfTimeReal (min τ (realTimeClamp t)) : ℝ) (X (min τ (realTimeClamp t)))
    rw [min_eq_right hle,changed_time_real t ht0.le]

end Asakura.Chapter11
