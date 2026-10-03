import Chapter5ProgressivePrefixRestriction
import Chapter2CumulativeAdapted

open MeasureTheory Set
namespace Asakura.Chapter5
open Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- A progressive integrand on a closed finite interval extends by zero
past its endpoint while remaining progressive on every finite prefix. -/
theorem progressive_finite_zero_extension
    {Ω : Type*} (F : ℝ → MeasurableSpace Ω) (hF : Monotone F)
    (R : ℝ) (hR : 0≤R) (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val))) (S : ℝ) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) S => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) S => (Iic R).indicator (fun r => H (z.1,r)) z.2.val) := by
  classical
  apply (measurable_progressive_iff _ _).mpr
  intro t
  let u : Icc (0:ℝ) R := projIcc 0 R hR t.val
  let q : Iic t → Iic u := fun s => ⟨projIcc 0 R hR s.val.val,monotone_projIcc hR s.property⟩
  have hu : u.val≤t.val := by
    by_cases ht : t.val≤R
    · rw [show u=⟨t.val,t.property.1,ht⟩ from projIcc_of_mem hR ⟨t.property.1,ht⟩]
    · rw [show u=⟨R,hR,le_rfl⟩ from projIcc_of_right_le hR (le_of_not_ge ht)]
      exact le_of_not_ge ht
  letI : MeasurableSpace Ω := F t.val
  have hq : Measurable q := ((continuous_projIcc.measurable.comp
    (measurable_subtype_coe.comp measurable_subtype_coe)).subtype_mk)
  have hid : @Measurable Ω Ω (F t.val) (F u.val) id := (@measurable_id Ω (F u.val)).mono (hF hu) le_rfl
  have hm := ((measurable_progressive_iff _ _).mp hH u).comp
    ((hid.comp measurable_fst).prodMk (hq.comp measurable_snd))
  have ht : Measurable (fun z : Ω × Iic t => z.2.val.val) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd)
  have he : (fun z : Ω × Iic t => (Iic R).indicator (fun r => H (z.1,r)) z.2.val.val)=
      ((fun z : Ω × Iic t => z.2.val.val) ⁻¹' Iic R).indicator
        (fun z => H (z.1,(q z.2).val.val)) := by
    funext z
    by_cases hz : z.2.val.val≤R
    · have hp := projIcc_of_mem hR (show z.2.val.val∈Icc (0:ℝ) R from ⟨z.2.val.property.1,hz⟩)
      simp only [Set.indicator,mem_Iic,mem_preimage,hz,ite_true,q,hp]
    · simp only [Set.indicator,mem_Iic,mem_preimage,hz,ite_false]
  rw [he]
  exact hm.indicator (measurableSet_Iic.preimage ht)

end Asakura.Chapter5
