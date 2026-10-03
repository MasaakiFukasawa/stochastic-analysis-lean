import Chapter3VariationPartitionBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem local_variation_bounded_on_prefix
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (A : ClosedTime T → Ω → ℝ) (hA : LocalVariationWitness F A)
    (b : ClosedTime T) (hb : b < ⊤) (ω : Ω) : BoundedVariationOn (fun t => A t ω) (Iic b) := by
  obtain ⟨σ,_,_,_,hc,hv⟩ := hA.localizers
  obtain ⟨k,hk⟩ := hc ω b hb
  obtain ⟨U,V,hU,hV,he⟩ := hv k ω
  have hUV := (increasing_difference_boundedVariation U V hU hV).mono (subset_univ (Iic b))
  have heq : EqOn (fun t => A t ω) (fun t => U t-V t) (Iic b) := by
    intro t ht
    simpa only [min_eq_right (ht.trans hk.le)] using he t
  change eVariationOn (fun t => A t ω) (Iic b) ≠ ∞
  rw [eVariationOn.congr heq]
  exact hUV

/-- Mixed terms with a finite-variation factor vanish uniformly. The
stronger estimate uses the common partition's control of the other factor;
it also covers the pure finite-variation square term. -/
theorem variation_cross_sum_uniform_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (A B H : ClosedTime T → Ω → ℝ) (hA : LocalVariationWitness F A)
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (hbB : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖B (min (τ n (j+1) ω) t) ω-B (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (b : ClosedTime T) (hb : b < ⊤) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω*
        (A (min (τ n (j+1) ω) (min b t)) ω-A (min (τ n j ω) (min b t)) ω)*
        (B (min (τ n (j+1) ω) (min b t)) ω-B (min (τ n j ω) (min b t)) ω))
      (fun _ => 0) atTop := by
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hbB n))] with ω hω
  have hAc := local_variation_bounded_on_prefix F A hA b hb ω
  have hHs : Continuous (fun t => H (min b t) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hHc ω _ ((min_le_left _ _).trans_lt hb)).comp
      (continuous_const.min continuous_id).continuousAt
  let Hs : C(ClosedTime T,ℝ) := ⟨_,hHs⟩
  have hHbound s (hs : s ≤ b) : |H s ω| ≤ ‖Hs‖ := by
    have h := Hs.norm_coe_le_norm s
    simpa only [Hs,ContinuousMap.coe_mk,min_eq_right hs,Real.norm_eq_abs] using h
  have hestimate n t := variation_cross_sum_bound (fun t => A t ω) (fun t => B t ω)
    (fun t => H t ω) b hb hAc (fun j => τ n j ω) (hτm n ω) (hτc n ω)
    ‖Hs‖ ((1/2:ℝ)^n) (norm_nonneg _) (pow_nonneg (by norm_num) n) hHbound (hω n) t
  have hl : Tendsto (fun n => ‖Hs‖*(1/2:ℝ)^n*(eVariationOn (fun t => A t ω) (Iic b)).toReal)
      atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul ‖Hs‖).mul_const
      (eVariationOn (fun t => A t ω) (Iic b)).toReal
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn
  intro t
  simpa only [Real.dist_eq,zero_sub,abs_neg] using (hestimate n t).trans_lt hn

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.local_variation_bounded_on_prefix
#print axioms Asakura.Chapter3Complete.variation_cross_sum_uniform_zero
