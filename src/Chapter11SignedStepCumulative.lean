import Chapter2SignedElementaryIntegral
import Chapter2SignedRestriction
import Chapter2SignedCumulativeContinuity
import Chapter2CovarianceAbsoluteContinuity

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- Finite elementary Stieltjes gains up to a cutoff, including the
 endpoint convention justified by the absence of atoms. -/
theorem signed_step_cumulative {ι : Type*} (ξ : SignedMeasure ℝ)
    [NullSingletonClass ξ.totalVariation] (s : Finset ι) (a b G : ι → ℝ)
    (hab : ∀ i∈s,a i≤b i) (d : ℝ) :
    signedCumulative ξ (fun r => ∑ i∈s,(Ico (a i) (b i)).indicator (fun _ => G i) r) d=
      ∑ i∈s,G i*ξ (Ioc (min (a i) d) (min (b i) d)) := by
  classical
  let ν : SignedMeasure ℝ := ξ.restrict (Iic d)
  have hv : ν.totalVariation=ξ.totalVariation.restrict (Iic d) := signed_totalVariation_restrict ξ measurableSet_Iic
  letI : NullSingletonClass ν.totalVariation := by rw [hv];infer_instance
  have hi : Integrable (fun r => ∑ i∈s,(Ico (a i) (b i)).indicator (fun _ => G i) r) ξ.totalVariation := by
    apply integrable_finset_sum
    intro i _
    exact (integrable_const _).indicator measurableSet_Ico
  have hm : Measurable (fun r => ∑ i∈s,(Ico (a i) (b i)).indicator (fun _ => G i) r) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator measurableSet_Ico
  have he := signed_integral_restrict ξ (B := Iic d) measurableSet_Iic _ hm hi.restrict
  rw [signedCumulative,←he,signed_integral_finite_steps]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [VectorMeasure.restrict_apply _ measurableSet_Iic measurableSet_Ioc]
  congr 1
  ext r
  simp only [mem_inter_iff,mem_Ioc,mem_Iic,lt_min_iff,le_min_iff]
  constructor
  · rintro ⟨⟨ha,hb⟩,hr⟩
    exact ⟨lt_of_le_of_lt (min_le_left _ _) ha,hb,hr⟩
  · rintro ⟨ha,hb,hr⟩
    have had : a i<d := by by_contra hh;rw [min_eq_right (le_of_not_gt hh)] at ha;linarith
    rw [min_eq_left had.le] at ha
    exact ⟨⟨ha,hb⟩,hr⟩

/-- Ioc is the convention used by elementary Ito integrands. -/
theorem signed_step_cumulative_Ioc {ι : Type*} (ξ : SignedMeasure ℝ)
    [NullSingletonClass ξ.totalVariation] (s : Finset ι) (a b G : ι → ℝ)
    (hab : ∀ i∈s,a i≤b i) (d : ℝ) :
    signedCumulative ξ (fun r => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i) r) d=
      ∑ i∈s,G i*ξ (Ioc (min (a i) d) (min (b i) d)) := by
  classical
  rw [←signed_step_cumulative ξ s a b G hab d]
  apply signed_integral_congr_of_absolute_continuity ξ.totalVariation ξ (by rfl)
  have he (i : {i // i∈s}) := Ico_ae_eq_Ioc (μ:=ξ.totalVariation) (a:=a i.val) (b:=b i.val)
  filter_upwards [ae_all_iff.mpr he] with r hr
  by_cases hd : r∈Iic d
  · simp only [indicator_of_mem hd]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Set.indicator,hr ⟨i,hi⟩]
  · simp only [indicator_of_notMem hd]

end Asakura.Chapter11
