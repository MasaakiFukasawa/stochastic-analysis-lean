import FullAuditStieltjesVariation
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Squaring a nonnegative extended square root, including zero and infinity. -/
theorem enn_half_square (x : ℝ≥0∞) : (x ^ (1/2:ℝ))^2 = x := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- A common finite partition and finite Cauchy-Schwarz, as in the manuscript. -/
theorem cs_simple_integral {Ω : Type*} [MeasurableSpace Ω]
    (α β η : Measure Ω)
    (hbound : ∀ E, MeasurableSet E → η E ≤ (α E)^(1/2:ℝ)*(β E)^(1/2:ℝ))
    (f g : SimpleFunc Ω ℝ≥0∞) :
    (∫⁻ x, f x*g x ∂η) ≤ (∫⁻ x, (f x)^2 ∂α)^(1/2:ℝ)*
      (∫⁻ x, (g x)^2 ∂β)^(1/2:ℝ) := by
  classical
  let h := f.pair g
  have hmap (μ : Measure Ω) (k : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) :
      (∫⁻ x, k (h x) ∂μ) = ∑ y ∈ h.range, k y * μ (h ⁻¹' {y}) := by
    calc
      _ = (h.map k).lintegral μ := SimpleFunc.lintegral_eq_lintegral _ _
      _ = _ := SimpleFunc.map_lintegral k h
  change (∫⁻ x, (h x).1*(h x).2 ∂η) ≤
    (∫⁻ x, (h x).1^2 ∂α)^(1/2:ℝ)*(∫⁻ x, (h x).2^2 ∂β)^(1/2:ℝ)
  rw [hmap η (fun y => y.1*y.2), hmap α (fun y => y.1^2), hmap β (fun y => y.2^2)]
  calc
    _ ≤ ∑ y ∈ h.range, (y.1*(α (h ⁻¹' {y}))^(1/2:ℝ))*
        (y.2*(β (h ⁻¹' {y}))^(1/2:ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      have hb := mul_le_mul' (le_rfl : y.1*y.2 ≤ y.1*y.2) (hbound (h ⁻¹' {y}) (h.measurableSet_fiber y))
      convert hb using 1 <;> ac_rfl
    _ ≤ _ := by
      have hc := ENNReal.inner_le_Lp_mul_Lq h.range
        (fun y => y.1*(α (h ⁻¹' {y}))^(1/2:ℝ))
        (fun y => y.2*(β (h ⁻¹' {y}))^(1/2:ℝ))
        (show Real.HolderConjugate 2 2 from by norm_num [Real.holderConjugate_iff])
      simpa only [ENNReal.rpow_two, mul_pow, enn_half_square] using hc

/-- Simultaneous increasing simple approximations finish the integral inequality.
The functions are finite-valued, as the manuscript's real-valued f,g are; their
integrals may be infinite. No continuity of multiplication at (0,infinity) is used. -/
theorem cs_measurable_integral {Ω : Type*} [MeasurableSpace Ω]
    (α β η : Measure Ω)
    (hbound : ∀ E, MeasurableSet E → η E ≤ (α E)^(1/2:ℝ)*(β E)^(1/2:ℝ))
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hft : ∀ x, f x ≠ ⊤) (hgt : ∀ x, g x ≠ ⊤) :
    (∫⁻ x, f x*g x ∂η) ≤ (∫⁻ x, (f x)^2 ∂α)^(1/2:ℝ)*
      (∫⁻ x, (g x)^2 ∂β)^(1/2:ℝ) := by
  let a := SimpleFunc.eapprox f
  let b := SimpleFunc.eapprox g
  have hab (x : Ω) : Monotone (fun n => a n x*b n x) := by
    intro n m hnm
    exact mul_le_mul' (SimpleFunc.monotone_eapprox f hnm x) (SimpleFunc.monotone_eapprox g hnm x)
  have halim (x : Ω) : Tendsto (fun n => a n x*b n x) atTop (𝓝 (f x*g x)) :=
    ENNReal.Tendsto.mul (SimpleFunc.tendsto_eapprox hf x) (Or.inr (hgt x))
      (SimpleFunc.tendsto_eapprox hg x) (Or.inr (hft x))
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (μ := η) (fun n => ((a n).measurable.mul (b n).measurable).aemeasurable)
    (Eventually.of_forall hab) (Eventually.of_forall halim)
  apply le_of_tendsto' hlim
  intro n
  apply (cs_simple_integral α β η hbound (a n) (b n)).trans
  apply mul_le_mul'
  · apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply lintegral_mono
    intro x
    apply pow_le_pow_left₀ (by positivity)
    exact (le_iSup (fun n => a n x) n).trans_eq (SimpleFunc.iSup_eapprox_apply hf x)
  · apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply lintegral_mono
    intro x
    apply pow_le_pow_left₀ (by positivity)
    exact (le_iSup (fun n => b n x) n).trans_eq (SimpleFunc.iSup_eapprox_apply hg x)

/-- Conversion from the manuscript's real square roots to extended integrals. -/
theorem finite_sqrt_mass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) : ENNReal.ofReal (Real.sqrt (μ.real E)) = (μ E)^(1/2:ℝ) := by
  rw [Measure.real_def, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
  simp [Measure.real_def, measure_ne_top]

/-- The full function inequality after extension from a generating algebra.
The original interval-to-algebra step is supplied by the separate semiring theorem. -/
theorem stieltjes_integral_from_algebra {Ω : Type*} [m : MeasurableSpace Ω]
    (α β : Measure Ω) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure Ω)
    (A : Set (Set Ω)) (hgen : m = MeasurableSpace.generateFrom A)
    (huniv : (univ : Set Ω) ∈ A) (hcompl : ∀ E ∈ A, Eᶜ ∈ A)
    (hinter : ∀ E ∈ A, ∀ F ∈ A, E ∩ F ∈ A)
    (hbound : ∀ E ∈ A, |ν E| ≤ Real.sqrt (α.real E)*Real.sqrt (β.real E))
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
      (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂α)^(1/2:ℝ)*
      (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂β)^(1/2:ℝ) := by
  have hb := signed_cs_from_algebra α β ν A hgen huniv hcompl hinter hbound
  have hv (E : Set Ω) (hE : MeasurableSet E) :
      ν.totalVariation E ≤ (α E)^(1/2:ℝ)*(β E)^(1/2:ℝ) := by
    have h := signed_cs_totalVariation α β ν hb hE
    rwa [ENNReal.ofReal_mul (Real.sqrt_nonneg _), finite_sqrt_mass α E, finite_sqrt_mass β E] at h
  have h := cs_measurable_integral α β ν.totalVariation hv
    (fun x => ENNReal.ofReal |f x|) (fun x => ENNReal.ofReal |g x|)
    (by simpa only [Real.norm_eq_abs] using hf.norm.ennreal_ofReal)
    (by simpa only [Real.norm_eq_abs] using hg.norm.ennreal_ofReal)
    (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
  simpa only [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using h

end Asakura.FullAudit
