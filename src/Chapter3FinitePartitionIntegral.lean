import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1000000

/-- A finite measurable partition gives the exact step value on each piece.
The pieces may be empty and the partition need cover only almost everywhere. -/
theorem finite_partition_step_error
    {S ι : Type*} [MeasurableSpace S] [DecidableEq ι]
    (μ : Measure S) (s : Finset ι) (B : ι → Set S) (a : ι → ℝ) (f : S → ℝ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, ∃ i ∈ s, x ∈ B i)
    (δ : ℝ) (herr : ∀ i ∈ s, ∀ x ∈ B i, |a i-f x| ≤ δ) :
    ∀ᵐ x ∂μ, |(∑ i ∈ s, (B i).indicator (fun _ => a i) x)-f x| ≤ δ := by
  filter_upwards [hcover] with x hx
  obtain ⟨i,hi,hxi⟩ := hx
  have he : (∑ j ∈ s, (B j).indicator (fun _ => a j) x) = a i := by
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hxi _
    · intro j hj hji
      apply indicator_of_notMem
      intro hxj
      exact (Set.disjoint_left.mp (hdisj i hi j hj hji.symm)) hxi hxj
    · exact fun h => (h hi).elim
  rw [he]
  exact herr i hi x hxi

/-- Uniform step approximation controls every cumulative integral by the
same total-mass bound. Integrability of f is obtained from the approximation,
not introduced as a hidden premise. -/
theorem finite_partition_cumulative_error
    {S ι : Type*} [MeasurableSpace S] [DecidableEq ι]
    (μ : Measure S) [IsFiniteMeasure μ] (s : Finset ι) (B : ι → Set S)
    (hB : ∀ i ∈ s, MeasurableSet (B i)) (a : ι → ℝ) (f : S → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, ∃ i ∈ s, x ∈ B i)
    (δ : ℝ) (hδ : 0 ≤ δ) (herr : ∀ i ∈ s, ∀ x ∈ B i, |a i-f x| ≤ δ) :
    Integrable f μ ∧ ∀ D, MeasurableSet D →
      |(∫ x in D, (∑ i ∈ s, (B i).indicator (fun _ => a i) x) ∂μ)-∫ x in D, f x ∂μ| ≤
        δ*μ.real Set.univ := by
  let g := fun x => ∑ i ∈ s, (B i).indicator (fun _ => a i) x
  have hg : Integrable g μ := integrable_finsetSum s
    (fun i hi => (integrable_const (a i)).indicator (hB i hi))
  have hb := finite_partition_step_error μ s B a f hdisj hcover δ herr
  have hi : Integrable (fun x => g x-f x) μ :=
    (integrable_const δ).mono' (hg.aestronglyMeasurable.sub hf)
      (by simpa only [Real.norm_eq_abs] using hb)
  have hfi : Integrable f μ := by
    convert hg.sub hi using 1
    funext x
    simp only [Pi.sub_apply,sub_sub_cancel]
  refine ⟨hfi,?_⟩
  intro D hD
  rw [← integral_sub hg.integrableOn hfi.integrableOn]
  calc
    _ ≤ ∫ x in D, |g x-f x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => g x-f x) (μ := μ.restrict D)
    _ ≤ ∫ x in D, δ ∂μ := integral_mono_ae hi.abs.integrableOn (integrable_const δ)
      (ae_restrict_of_ae hb)
    _ ≤ δ*μ.real Set.univ := by
      rw [setIntegral_const,smul_eq_mul]
      have hm : μ.real D ≤ μ.real Set.univ := ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (subset_univ D))
      nlinarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.finite_partition_step_error
#print axioms Asakura.Chapter3Complete.finite_partition_cumulative_error
