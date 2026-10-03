import Chapter2RandomSignedVariation
import Chapter2SignedIntegralEstimate

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Interval evaluations suffice for measurability of a family of finite
measures on the real line; no uniform bound on the masses is needed. -/
theorem measure_family_measurable_of_Ioc
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℝ)
    [∀ ω, IsFiniteMeasure (μ ω)]
    (hi : ∀ s t, Measurable (fun ω => μ ω (Ioc s t))) : Measurable μ := by
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
  have hu : Measurable (fun ω => μ ω univ) := by
    have he ω : μ ω univ = ⨆ n, μ ω (S n) := by
      rw [← hSu]
      exact hSm.measure_iUnion
    simp only [he]
    exact Measurable.iSup (fun n => hi (-(n:ℝ)) (n:ℝ))
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Ioc ℝ) (isPiSystem_Ioc id id) _ hu
  rintro _ ⟨s,t,hst,rfl⟩
  exact hi s t

/-- Measurability of both Jordan measures is derived, rather than added as
an assumption on the random signed measure. -/
theorem random_signed_jordan_measurable
    {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → SignedMeasure ℝ)
    (hv : Measurable (fun ω => (ν ω).totalVariation))
    (hi : ∀ s t, Measurable (fun ω => ν ω (Ioc s t))) :
    Measurable (fun ω => (ν ω).toJordanDecomposition.posPart) ∧
      Measurable (fun ω => (ν ω).toJordanDecomposition.negPart) := by
  have he ω (B : Set ℝ) (hB : MeasurableSet B) :
      (ν ω).toJordanDecomposition.posPart B =
        ENNReal.ofReal (((ν ω).totalVariation.real B+ν ω B)/2) ∧
      (ν ω).toJordanDecomposition.negPart B =
        ENNReal.ofReal (((ν ω).totalVariation.real B-ν ω B)/2) := by
    have hs := (ν ω).apply_eq_posPart_real_sub_negPart_real hB
    have ht : (ν ω).totalVariation.real B =
        (ν ω).toJordanDecomposition.posPart.real B+(ν ω).toJordanDecomposition.negPart.real B := by
      simp only [SignedMeasure.totalVariation,Measure.real,Measure.add_apply,
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    constructor
    · have hr : ((ν ω).totalVariation.real B+ν ω B)/2 =
          (ν ω).toJordanDecomposition.posPart.real B := by linarith
      rw [hr,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · have hr : ((ν ω).totalVariation.real B-ν ω B)/2 =
          (ν ω).toJordanDecomposition.negPart.real B := by linarith
      rw [hr,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hm s t : Measurable (fun ω => (ν ω).totalVariation.real (Ioc s t)) :=
    ENNReal.measurable_toReal.comp ((Measure.measurable_coe measurableSet_Ioc).comp hv)
  constructor
  · apply measure_family_measurable_of_Ioc
    intro s t
    simp only [(he _ _ measurableSet_Ioc).1]
    exact ((hm s t).add (hi s t)).div_const 2 |>.ennreal_ofReal
  · apply measure_family_measurable_of_Ioc
    intro s t
    simp only [(he _ _ measurableSet_Ioc).2]
    exact ((hm s t).sub (hi s t)).div_const 2 |>.ennreal_ofReal

theorem random_signed_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → SignedMeasure ℝ)
    (hv : Measurable (fun ω => (ν ω).totalVariation))
    (hi : ∀ s t, Measurable (fun ω => ν ω (Ioc s t)))
    (H : Ω × ℝ → ℝ) (hH : Measurable H) :
    Measurable (fun ω => signedIntegralRaw (ν ω) (fun r => H (ω,r))) := by
  obtain ⟨hp,hn⟩ := random_signed_jordan_measurable ν hv hi
  exact (finite_kernel_integral_measurable ⟨_,hp⟩ (fun ω => show IsFiniteMeasure (ν ω).toJordanDecomposition.posPart from inferInstance) H hH).sub
    (finite_kernel_integral_measurable ⟨_,hn⟩ (fun ω => show IsFiniteMeasure (ν ω).toJordanDecomposition.negPart from inferInstance) H hH)

theorem continuous_signed_stieltjes_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → ℝ → ℝ)
    (hC : ∀ ω, Continuous (C ω)) (hm : ∀ r, Measurable (fun ω => C ω r))
    (hb : ∀ ω, BoundedVariationOn (C ω) univ) (a : ℝ)
    (H : Ω × ℝ → ℝ) (hH : Measurable H) :
    Measurable (fun ω => signedIntegralRaw (bvSigned (C ω) (hb ω)
      (fun r => (hC ω).continuousAt.continuousWithinAt) a) (fun r => H (ω,r))) := by
  apply random_signed_integral_measurable _
    (continuous_signed_stieltjes_totalVariation_measurable C hC hm hb a) _ H hH
  intro s t
  by_cases hst : s ≤ t
  · simp only [bvSigned_Ioc _ _ _ _ s t hst]
    exact (hm t).sub (hm s)
  · simp only [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hst)),VectorMeasure.empty]
    exact measurable_const

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_signed_stieltjes_integral_measurable
