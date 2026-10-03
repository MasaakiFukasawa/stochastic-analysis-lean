import Chapter5WeightedSpace
import Chapter5FiniteTimeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- On the finite horizon the weighted and unweighted L² spaces contain
the same measurable processes. This justifies both directions of the
space change used in constructing the BSDE contraction. -/
theorem finite_weighted_memLp_two_iff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (β : ℝ) (hβ : 0 ≤ β)
    (H : Ω × ℝ → ℝ) (hH : Measurable H) :
    MemLp H 2 (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β) ↔
      MemLp H 2 (P.prod (volume.restrict (Ioc 0 R))) := by
  let ν := P.prod (volume.restrict (Ioc 0 R))
  have he : Integrable (fun z => H z^2) (exponentialEnergyMeasure ν β) ↔
      Integrable (fun z => Real.exp (β*z.2)*H z^2) ν := by
    unfold exponentialEnergyMeasure
    have hwm : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (β*z.2))) :=
      (measurable_const.mul measurable_snd).exp.ennreal_ofReal
    rw [integrable_withDensity_iff_integrable_smul' hwm
      (ae_of_all ν fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
  constructor
  · intro hi
    have hw := he.mp ((memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mp hi)
    apply (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mpr
    apply hw.mono' (hH.pow_const 2).aestronglyMeasurable
    have hs : ∀ᵐ z ∂ν,z.2 ∈ Ioc 0 R := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
      exact ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioc
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs,abs_sq]
    have hexp : 1 ≤ Real.exp (β*z.2) := Real.one_le_exp_iff.mpr (mul_nonneg hβ hz.1.le)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (sq_nonneg (H z))
  · intro hi
    apply (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mpr
    exact he.mpr (finite_time_weighted_energy P R hR β hβ H hH hi).1

end Asakura.Chapter5
