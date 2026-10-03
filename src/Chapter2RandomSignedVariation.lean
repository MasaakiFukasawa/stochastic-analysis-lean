import Chapter2CountableVariation
import FullAuditBVMeasure
import Chapter2FiniteKernelIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem continuous_interval_variation_measurable
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → ℝ → ℝ)
    (hC : ∀ ω, Continuous (C ω)) (hm : ∀ r, Measurable (fun ω => C ω r)) (a b : ℝ) :
    Measurable (fun ω => (eVariationOn (C ω) (Icc a b)).toReal) := by
  let Y : Ω → C(Icc a b,ℝ) := fun ω => ⟨fun r => C ω r.val,(hC ω).comp continuous_subtype_val⟩
  have hY : Measurable Y := ContinuousMap.measurable_iff_eval.mpr (fun r => hm r.val)
  have hv : Measurable (fun f : C(Icc a b,ℝ) => eVariationOn f univ) :=
    (continuous_map_variation_lowerSemicontinuous (univ : Set (Icc a b))).measurable
  have he ω : eVariationOn (Y ω) univ = eVariationOn (C ω) (Icc a b) := by
    simpa only [Y,ContinuousMap.coe_mk,Function.comp_def,image_univ,Subtype.range_coe_subtype,Set.setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn (C ω) (Subtype.val : Icc a b → ℝ)
        (t := univ) (fun _ _ _ _ h => h)
  have hvY : Measurable (fun ω => eVariationOn (Y ω) univ) :=
    Measurable.comp (g := fun f : C(Icc a b,ℝ) => eVariationOn f univ) (f := Y) hv hY
  exact ENNReal.measurable_toReal.comp (by simpa only [he] using hvY)

theorem continuous_variation_from_to_measurable
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → ℝ → ℝ)
    (hC : ∀ ω, Continuous (C ω)) (hm : ∀ r, Measurable (fun ω => C ω r)) (a b : ℝ) :
    Measurable (fun ω => variationOnFromTo (C ω) univ a b) := by
  by_cases hab : a ≤ b
  · simp only [variationOnFromTo.eq_of_le _ _ hab,univ_inter]
    exact continuous_interval_variation_measurable C hC hm a b
  · simp only [variationOnFromTo.eq_of_ge _ _ (le_of_not_ge hab),univ_inter]
    exact (continuous_interval_variation_measurable C hC hm b a).neg

/-- Total variations of the actual signed Stieltjes measures form a
measurable family. This supplies the random measure needed in the printed
absolute-integrability/Fubini argument. -/
theorem continuous_signed_stieltjes_totalVariation_measurable
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → ℝ → ℝ)
    (hC : ∀ ω, Continuous (C ω)) (hm : ∀ r, Measurable (fun ω => C ω r))
    (hb : ∀ ω, BoundedVariationOn (C ω) univ) (a : ℝ) :
    Measurable (fun ω => (bvSigned (C ω) (hb ω)
      (fun r => (hC ω).continuousAt.continuousWithinAt) a).totalVariation) := by
  let ν := fun ω => (bvSigned (C ω) (hb ω) (fun r => (hC ω).continuousAt.continuousWithinAt) a).totalVariation
  have hi (s t : ℝ) : Measurable (fun ω => ν ω (Ioc s t)) := by
    have he ω : ν ω (Ioc s t) = ENNReal.ofReal
        (variationOnFromTo (C ω) univ a t-variationOnFromTo (C ω) univ a s) := by
      dsimp only [ν]
      rw [bvSigned_totalVariation,StieltjesFunction.measure_Ioc]
      rfl
    simp only [he]
    exact ((continuous_variation_from_to_measurable C hC hm a t).sub
      (continuous_variation_from_to_measurable C hC hm a s)).ennreal_ofReal
  let S := fun n : ℕ => Ioc (-(n:ℝ)) (n:ℝ)
  have hSm : Monotone S := by
    intro n k hnk
    exact Ioc_subset_Ioc (by exact_mod_cast (neg_le_neg (show (n:ℝ) ≤ k by exact_mod_cast hnk)))
      (by exact_mod_cast hnk)
  have hSu : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro r
    obtain ⟨n,hn⟩ := exists_nat_gt |r|
    apply mem_iUnion.mpr
    refine ⟨n,?_,?_⟩
    · change -(n:ℝ) < r
      linarith [neg_abs_le r]
    · change r ≤ (n:ℝ)
      exact (le_abs_self r).trans hn.le
  have hu : Measurable (fun ω => ν ω univ) := by
    have he ω : ν ω univ = ⨆ n, ν ω (S n) := by
      rw [← hSu]
      exact hSm.measure_iUnion
    simp only [he]
    exact Measurable.iSup (fun n => hi (-(n:ℝ)) (n:ℝ))
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Ioc ℝ) (isPiSystem_Ioc id id) _ hu
  rintro _ ⟨s,t,hst,rfl⟩
  exact hi s t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_signed_stieltjes_totalVariation_measurable
