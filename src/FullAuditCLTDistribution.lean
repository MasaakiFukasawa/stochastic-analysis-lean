import FullAuditCLTSmooth
import FullAuditCLTCutoffs

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

/-- Expectations of the explicit cutoffs sandwich the two endpoint conventions. -/
theorem cutoff_probability_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (a b : ℝ) (hab : a < b) :
    P.real {ω | Y ω ≤ a} ≤ (∫ ω, cltCutoff a b (Y ω) ∂P) ∧
      (∫ ω, cltCutoff a b (Y ω) ∂P) ≤ P.real {ω | Y ω < b} := by
  have hA : MeasurableSet {ω | Y ω ≤ a} := measurableSet_le hY measurable_const
  have hB : MeasurableSet {ω | Y ω < b} := measurableSet_lt hY measurable_const
  have hiA := (integrable_const (1:ℝ) (μ := P)).indicator hA
  have hiB := (integrable_const (1:ℝ) (μ := P)).indicator hB
  have hi : Integrable (fun ω => cltCutoff a b (Y ω)) P :=
    Integrable.of_bound ((cltCutoff_smooth a b hab).continuous.measurable.comp hY).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg ((cltCutoff_values a b hab).1 (Y ω)).1]
        exact ((cltCutoff_values a b hab).1 (Y ω)).2)
  have heA : (∫ ω, {ω | Y ω ≤ a}.indicator (fun _ => (1:ℝ)) ω ∂P) = P.real {ω | Y ω ≤ a} := by
    rw [integral_indicator hA,setIntegral_const]; simp
  have heB : (∫ ω, {ω | Y ω < b}.indicator (fun _ => (1:ℝ)) ω ∂P) = P.real {ω | Y ω < b} := by
    rw [integral_indicator hB,setIntegral_const]; simp
  rw [← heA,← heB]
  constructor
  · apply integral_mono hiA hi
    intro ω
    simpa only [Set.indicator,mem_setOf_eq,mem_Iic] using (cltCutoff_indicator_bounds a b (Y ω) hab).1
  · apply integral_mono hi hiB
    intro ω
    simpa only [Set.indicator,mem_setOf_eq,mem_Iio] using (cltCutoff_indicator_bounds a b (Y ω) hab).2

/-- The final double approximation in the written CLT proof, for either strict
or non-strict half-lines and a general non-atomic limiting measure. -/
theorem distribution_limit_from_cutoffs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℝ) (hnull : μ {z} = 0)
    (hlim : ∀ a b, a < b → Tendsto (fun n => ∫ ω, cltCutoff a b (Y n ω) ∂P) atTop
      (𝓝 (∫ y, cltCutoff a b y ∂μ))) :
    Tendsto (fun n => P.real {ω | Y n ω < z}) atTop (𝓝 (μ.real (Iic z))) ∧
      Tendsto (fun n => P.real {ω | Y n ω ≤ z}) atTop (𝓝 (μ.real (Iic z))) := by
  let δ : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hδ : ∀ k, 0 < δ k := by intro k; dsimp [δ]; positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlo := cltCutoff_integral_tendsto μ (fun k => z-δ k) (fun _ => z) z hnull
    (fun k => by linarith [hδ k]) (by simpa using tendsto_const_nhds.sub hδ0) tendsto_const_nhds
  have hup := cltCutoff_integral_tendsto μ (fun _ => z) (fun k => z+δ k) z hnull
    (fun k => by linarith [hδ k]) tendsto_const_nhds (by simpa using tendsto_const_nhds.add hδ0)
  have hbetween : ∀ n, P.real {ω | Y n ω < z} ≤ P.real {ω | Y n ω ≤ z} := by
    intro n
    exact measureReal_mono (fun ω (hω : Y n ω < z) => show Y n ω ≤ z from hω.le)
  have lower : ∀ c < μ.real (Iic z), ∀ᶠ n in atTop, c < P.real {ω | Y n ω < z} := by
    intro c hc
    obtain ⟨k,hk⟩ := ((tendsto_order.mp hlo).1 c hc).exists
    have h := (tendsto_order.mp (hlim (z-δ k) z (by linarith [hδ k]))).1 c hk
    filter_upwards [h] with n hn
    exact hn.trans_le (cutoff_probability_bounds P (Y n) (hY n) _ _ (by linarith [hδ k])).2
  have upper : ∀ c > μ.real (Iic z), ∀ᶠ n in atTop, P.real {ω | Y n ω ≤ z} < c := by
    intro c hc
    obtain ⟨k,hk⟩ := ((tendsto_order.mp hup).2 c hc).exists
    have h := (tendsto_order.mp (hlim z (z+δ k) (by linarith [hδ k]))).2 c hk
    filter_upwards [h] with n hn
    exact (cutoff_probability_bounds P (Y n) (hY n) _ _ (by linarith [hδ k])).1.trans_lt hn
  constructor
  · apply tendsto_order.mpr
    refine ⟨lower,fun c hc => ?_⟩
    exact (upper c hc).mono fun n hn => (hbetween n).trans_lt hn
  · apply tendsto_order.mpr
    refine ⟨fun c hc => ?_,upper⟩
    exact (lower c hc).mono fun n hn => hn.trans_le (hbetween n)

/-- The manuscript's full triangular-array central limit theorem, verified via
its heat-kernel/Taylor proof and its specified smooth cutoff construction. -/
theorem clt_written {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (n : ℕ) → Fin n → Ω → ℝ)
    (hmX : ∀ n i, Measurable (X n i))
    (hX : ∀ n i, Integrable (fun ω => X n i ω ^ 2) P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hind : ∀ n, iIndepFun (X n) P)
    (hvsum : Tendsto (fun n => ∑ i : Fin n, ∫ ω, X n i ω ^ 2 ∂P) atTop (𝓝 1))
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i : Fin n, ∫ ω in {ω | ε ≤ |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n => P.real {ω | (∑ i : Fin n, X n i ω) < z}) atTop
      (𝓝 ((gaussianReal 0 1).real (Iic z))) ∧
    Tendsto (fun n => P.real {ω | (∑ i : Fin n, X n i ω) ≤ z}) atTop
      (𝓝 ((gaussianReal 0 1).real (Iic z))) := by
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  apply distribution_limit_from_cutoffs P (fun n ω => ∑ i, X n i ω)
    (fun n => Finset.measurable_sum _ fun i _ => hmX n i) (gaussianReal 0 1) z (measure_singleton z)
  intro a b hab
  have h := clt_smooth_written P X hmX hX hmean hind hvsum hL (cutoffHeatTest a b hab)
  simpa only [cutoffHeatTest_zero] using h

/-- Identify the limiting probability with the displayed density integral. -/
theorem standard_gaussian_cdf_integral (z : ℝ) :
    (gaussianReal 0 1).real (Iic z) =
      ∫ x in Iic z, (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) := by
  have hleft : (∫ x, (Iic z).indicator (fun _ => (1:ℝ)) x ∂gaussianReal 0 1) =
      (gaussianReal 0 1).real (Iic z) := by
    rw [integral_indicator measurableSet_Iic,setIntegral_const]; simp
  rw [← hleft,integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  have he : (fun x => gaussianPDFReal 0 1 x • (Iic z).indicator (fun _ => (1:ℝ)) x) =
      (Iic z).indicator (gaussianPDFReal 0 1) := by
    funext x
    by_cases hx : x ∈ Iic z <;> simp [Set.indicator,hx]
  rw [he,integral_indicator measurableSet_Iic]
  congr 1
  funext x
  simp [gaussianPDFReal]

end Asakura.FullAudit
