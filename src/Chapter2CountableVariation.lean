import FullAuditVariationProcess
import FullAuditStoppedContinuous

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true

/-- Variation is lower semicontinuous for pointwise convergence: every
finite partition sum depends continuously on finitely many evaluations. -/
theorem variation_pi_lowerSemicontinuous {ι : Type*} [LinearOrder ι] (S : Set ι) :
    LowerSemicontinuous (fun f : ι → ℝ => eVariationOn f S) := by
  unfold eVariationOn
  apply lowerSemicontinuous_iSup
  rintro ⟨n,u,hu,hs⟩
  apply Continuous.lowerSemicontinuous
  apply continuous_finset_sum
  intro j hj
  exact (continuous_apply (u (j+1))).edist (continuous_apply (u j))

theorem variation_pi_measurable {ι : Type*} [LinearOrder ι] [Countable ι] :
    Measurable (fun f : ι → ℝ => eVariationOn f univ) :=
  (variation_pi_lowerSemicontinuous (univ : Set ι)).measurable

/-- A countable set of observation times makes variation measurable. -/
theorem countable_variation_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [Countable ι] (X : ι → Ω → ℝ)
    (hm : ∀ t, Measurable (X t)) : Measurable (fun ω => eVariationOn (fun t => X t ω) univ) := by
  exact Measurable.comp (g := fun f : ι → ℝ => eVariationOn f univ)
    (f := fun ω : Ω => fun t : ι => X t ω)
    (variation_pi_measurable (ι := ι)) (measurable_pi_iff.mpr hm)

theorem countable_subset_variation_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] (S : Set ι) (hS : S.Countable) (X : ι → Ω → ℝ)
    (hm : ∀ t ∈ S, Measurable (X t)) : Measurable (fun ω => eVariationOn (fun t => X t ω) S) := by
  letI : Countable S := hS.to_subtype
  have h := countable_variation_measurable (fun t : S => X t.val) (fun t => hm t.val t.property)
  have he ω : eVariationOn (fun t : S => X t.val ω) univ = eVariationOn (fun t => X t ω) S := by
    simpa only [Function.comp_def,image_univ,Subtype.range_coe_subtype,Set.setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn (fun t => X t ω) (Subtype.val : S → ι)
        (t := univ) (fun _ _ _ _ h => h)
  simpa only [he] using h

/-- The supremum over a sequence of countable right grids equals the
full variation when their evaluation values converge pointwise. -/
theorem variation_eq_iSup_grid {ι : Type*} [LinearOrder ι]
    (S : Set ι) (q : ℕ → ι → ι) (hq : ∀ n, MonotoneOn (q n) S)
    (hqs : ∀ n, MapsTo (q n) S S) (f : ι → ℝ)
    (hl : ∀ t ∈ S, Tendsto (fun n => f (q n t)) atTop (𝓝 (f t))) :
    eVariationOn f S = ⨆ n, eVariationOn f (q n '' S) := by
  apply le_antisymm
  · rw [eVariationOn]
    apply iSup_le
    rintro ⟨k,u,hu,hus⟩
    have hlim : Tendsto (fun n => ∑ i ∈ Finset.range k,
        edist (f (q n (u (i+1)))) (f (q n (u i)))) atTop
        (𝓝 (∑ i ∈ Finset.range k, edist (f (u (i+1))) (f (u i)))) := by
      apply tendsto_finset_sum
      intro i hi
      exact (hl _ (hus (i+1))).edist (hl _ (hus i))
    apply le_of_tendsto hlim
    exact .of_forall fun n =>
      (eVariationOn.sum_le_of_monotoneOn_Iic
        (fun i hi j hj hij => hq n (hus i) (hus j) (hu hij))
        (fun i hi => mem_image_of_mem (q n) (hus i))).trans (le_iSup (fun k => eVariationOn f (q k '' S)) n)
  · apply iSup_le
    intro n
    exact eVariationOn.mono f (hqs n).image_subset

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.countable_subset_variation_measurable
#print axioms Asakura.Chapter2Complete.variation_eq_iSup_grid
