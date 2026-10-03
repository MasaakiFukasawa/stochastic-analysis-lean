import Chapter10MeanODEZero

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the price and filter integral equations when their gains agree.
The resulting homogeneous scalar equation has zero solution by the same
Gronwall uniqueness argument used earlier in the manuscript. -/
theorem kyle_variable_gain_sufficiency (a p z l β : ℝ → ℝ) (p0 T : ℝ) (hT : 0≤T)
    (ha : Continuous a) (hp : Continuous p) (hl : Continuous l) (hβ : Continuous β)
    (hprice : ∀ t∈Icc 0 T,p t=p0+z t)
    (hfilter : ∀ t∈Icc 0 T,a t=p0+z t+∫ s in 0..t,l s*β s*(p s-a s)) :
    ∀ t∈Icc 0 T,a t=p t := by
  let e := fun t => a t-p t
  have hec : Continuous e := ha.sub hp
  have hbc : Continuous (fun s => -l s*β s*e s) := (hl.neg.mul hβ).mul hec
  have heq t (ht : t∈Icc 0 T) : e t=∫ s in 0..t,-l s*β s*e s := by
    rw [show e t=a t-p t from rfl,hfilter t ht,hprice t ht]
    simp only [add_sub_cancel_left]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [e]
    ring
  have hed : ∀ t∈Ico 0 T,HasDerivWithinAt e (-l t*β t*e t) (Ici t) t := by
    intro t ht
    have hi := intervalIntegral.integral_hasDerivAt_right (hbc.intervalIntegrable 0 t)
      (hbc.stronglyMeasurableAtFilter _ _) hbc.continuousAt
    apply hi.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · have hlt : ∀ᶠ s in 𝓝[Ici t] t,s<T := (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin,hlt] with s hs hsT
      exact heq s ⟨ht.1.trans hs,hsT.le⟩
    · exact le_refl t
  have h0 : e 0=0 := by simpa only [intervalIntegral.integral_same] using heq 0 ⟨le_rfl,hT⟩
  obtain ⟨K,hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
    (hl.neg.mul hβ).continuousOn
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := e) (f' := fun t => -l t*β t*e t) (K := K) hec.continuousOn hed h0 (by
      intro t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK t ⟨ht.1,ht.2.le⟩) (norm_nonneg _))
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end Asakura.Chapter10
