import Chapter10KyleVariableGainSufficiency

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000

/-- Gain equality implies rational pricing locally before the singular
terminal time. No extension of the singular feedback through T is assumed. -/
theorem kyle_finite_gain_sufficiency (a p z l β : ℝ → ℝ) (p0 R : ℝ) (hR : 0≤R)
    (ha : ContinuousOn a (Icc 0 R)) (hp : ContinuousOn p (Icc 0 R))
    (hl : ContinuousOn l (Icc 0 R)) (hβ : ContinuousOn β (Icc 0 R))
    (hprice : ∀ t∈Icc 0 R,p t=p0+z t)
    (hfilter : ∀ t∈Icc 0 R,a t=p0+z t+∫ s in 0..t,l s*β s*(p s-a s)) :
    ∀ t∈Icc 0 R,a t=p t := by
  let c := fun t => (projIcc 0 R hR t).val
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcm : ∀ t,c t∈Icc 0 R := fun t => (projIcc 0 R hR t).property
  have hid : ∀ t∈Icc 0 R,c t=t := by
    intro t ht
    exact congrArg Subtype.val (projIcc_of_mem hR ht)
  have he := kyle_variable_gain_sufficiency (a ∘ c) (p ∘ c) (z ∘ c) (l ∘ c) (β ∘ c)
    p0 R hR (ha.comp_continuous hc hcm) (hp.comp_continuous hc hcm)
    (hl.comp_continuous hc hcm) (hβ.comp_continuous hc hcm) (by
      intro t ht
      simpa only [Function.comp_def,hid t ht] using hprice t ht) (by
      intro t ht
      simp only [Function.comp_def,hid t ht]
      rw [hfilter t ht]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s∈Icc 0 R := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1,hs.2.trans ht.2⟩
      dsimp only
      rw [hid s hs'])
  intro t ht
  simpa only [Function.comp_def,hid t ht] using he t ht

end Asakura.Chapter10
