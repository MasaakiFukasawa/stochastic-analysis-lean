import Chapter2SignedIntegralContinuity
import FullAuditVariationApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The interval CS bound transfers absence of atoms to total variation. -/
theorem signed_cs_null_singletons
    (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] [NullSingletonClass α]
    (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t))) :
    NullSingletonClass ν.totalVariation := by
  constructor
  intro r
  have h := signed_cs_totalVariation α β ν (signed_cs_real_intervals α β ν hc) (measurableSet_singleton r)
  have hz : α.real {r} = 0 := by simp [Measure.real]
  simpa only [hz,Real.sqrt_zero,zero_mul,ENNReal.ofReal_zero,le_zero_iff] using h

/-- The integral of an actual finite step function is the coefficient
sum of signed interval masses; the Ico/Ioc endpoint convention is justified
by absence of atoms of total variation. -/
theorem signed_integral_finite_steps
    {ι : Type*} (ν : SignedMeasure ℝ) [NullSingletonClass ν.totalVariation]
    (s : Finset ι) (a b G : ι → ℝ) :
    signedIntegralRaw ν (fun r => ∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i) r) =
      ∑ i ∈ s, G i*ν (Ioc (a i) (b i)) := by
  classical
  have he : (fun r => ∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i) r) =ᵐ[ν.totalVariation]
      (fun r => ∑ i ∈ s, (Ioc (a i) (b i)).indicator (fun _ => G i) r) := by
    have hi i : (Ico (a i) (b i)).indicator (fun _ => G i) =ᵐ[ν.totalVariation]
        (Ioc (a i) (b i)).indicator (fun _ => G i) := by
      filter_upwards [Ico_ae_eq_Ioc (μ := ν.totalVariation) (a := a i) (b := b i)] with r hr
      simp only [Set.indicator,hr]
    have hi' (i : s) := hi i.val
    filter_upwards [ae_all_iff.2 hi'] with r hr
    exact Finset.sum_congr rfl (fun i his => hr ⟨i,his⟩)
  rw [signedIntegralRaw_congr_ae ν.totalVariation ν 1 (by norm_num) (by simp) he]
  unfold signedIntegralRaw
  rw [integral_finset_sum,integral_finset_sum,← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator measurableSet_Ioc,integral_indicator measurableSet_Ioc,
      setIntegral_const,setIntegral_const,ν.apply_eq_posPart_real_sub_negPart_real measurableSet_Ioc]
    simp only [smul_eq_mul]
    ring
  all_goals intro i hi; exact (integrable_const _).indicator measurableSet_Ioc

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_cs_null_singletons
#print axioms Asakura.Chapter2Complete.signed_integral_finite_steps
