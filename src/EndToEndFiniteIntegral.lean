import AppendixWrittenBorelCantelli

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.EndToEnd

/-- The printed argument k * measure{f=infinity} <= integral f, followed by
 k tending to infinity. No sigma-finiteness assumption is needed. -/
theorem finite_integral_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f)
    (hi : (∫⁻ x,f x ∂μ) < ∞) : ∀ᵐ x ∂μ, f x < ∞ := by
  classical
  let N := {x | f x = ∞}
  have hm : MeasurableSet N := hf (measurableSet_singleton ∞)
  have hb (k : ℕ) : (k:ℝ≥0∞) * μ N ≤ ∫⁻ x,f x ∂μ := by
    calc
      (k:ℝ≥0∞) * μ N = ∫⁻ x,N.indicator (fun _ => (k:ℝ≥0∞)) x ∂μ := by
        rw [lintegral_indicator hm,lintegral_const,Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x,f x ∂μ := lintegral_mono (fun x => by
        by_cases hx : x ∈ N
        · rw [Set.indicator_of_mem hx]
          exact (show f x = ∞ from hx) ▸ le_top
        · rw [Set.indicator_of_notMem hx]
          exact zero_le)
  have hz : μ N = 0 := by
    by_contra hn
    have hh := iSup_le hb
    rw [← ENNReal.iSup_mul,ENNReal.iSup_natCast,ENNReal.top_mul hn] at hh
    exact (not_le_of_gt hi) hh
  simpa only [ae_iff,ENNReal.not_lt_top,N] using hz

/-- General-measure Borel--Cantelli using the counting integral and the
 preceding finite-integral lemma. -/
theorem counting_borel_cantelli {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω) (hm : ∀ n,MeasurableSet (A n))
    (hi : ∑' n,μ (A n) < ∞) : ∀ᵐ x ∂μ, {n | x ∈ A n}.Finite := by
  have hf := finite_integral_ae_finite μ
    (fun x => ∑' n,(A n).indicator (fun _ => (1:ℝ≥0∞)) x)
    (Measurable.ennreal_tsum (fun n => measurable_const.indicator (hm n)))
    (by rwa [Asakura.written_counting_integral μ A hm])
  filter_upwards [hf] with x hx
  have hfin := ENNReal.finite_const_le_of_tsum_ne_top hx.ne (by norm_num : (1:ℝ≥0∞) ≠ 0)
  apply hfin.subset
  intro n hn
  change 1 ≤ (A n).indicator (fun _ => (1:ℝ≥0∞)) x
  change x ∈ A n at hn
  rw [Set.indicator_of_mem hn]

#print axioms finite_integral_ae_finite
#print axioms counting_borel_cantelli
end Asakura.EndToEnd
