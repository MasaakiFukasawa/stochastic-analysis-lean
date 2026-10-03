import Chapter7ProbabilityErrorAssembly
import Chapter7ScaledFiniteCLT

open MeasureTheory Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7

lemma probability_finite_sum_zero {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (s : Finset ι) (X : ι → ℕ → Ω → ℝ)
    (hX : ∀ i∈s,TendstoInMeasure P (X i) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n w => ∑ i∈s,X i n w) atTop (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all P (fun _ => tendsto_const_nhds))
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact probability_add_zero P _ _ (hX i (mem_insert_self _ _))
      (ih (fun j hj => hX j (mem_insert_of_mem hj)))

lemma probability_unscale_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*X n w) atTop (fun _ => 0)) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  have hn n : 0<Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hi n : Integrable (fun _ : Ω => |(Real.sqrt ((n+1:ℕ):ℝ))⁻¹|) P := integrable_const _
  have hb n : (∫ _ : Ω,|(Real.sqrt ((n+1:ℕ):ℝ))⁻¹| ∂P)≤1 := by
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,
      abs_of_nonneg (inv_nonneg.mpr (hn n).le)]
    apply inv_le_one_of_one_le₀
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
  have hp := probability_product_bounded_moment P _ (fun n _ => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹)
    hX hi 1 (by norm_num) hb
  apply hp.congr_left
  intro n
  exact ae_of_all P (fun w => by field_simp)

end Asakura.Chapter7
