import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Chapter12RapidDecayIntegrable

open MeasureTheory Set Filter
open scoped Topology CompactlySupported
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The density identification step after Gaussian smoothing: a common
bound and pointwise convergence suffice on compactly supported test functions.
No unproved Fourier inversion assertion is used in this limit passage. -/
theorem density_of_bounded_approximations {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν μ : Measure E) [ν.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (p : E → ℝ) (pn : ℕ → E → ℝ) (hp : Continuous p)
    (hpn : ∀ n,Measurable (pn n)) (hnonneg : ∀ n x,0≤pn n x)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ n x,pn n x≤C)
    (hlim : ∀ x,Tendsto (fun n => pn n x) atTop (𝓝 (p x)))
    (hweak : ∀ f : C_c(E, ℝ),Tendsto
      (fun n => ∫ x,f x ∂ν.withDensity (fun x => ENNReal.ofReal (pn n x))) atTop
      (𝓝 (∫ x,f x ∂μ))) :
    (∀ x,0≤p x) ∧ μ=ν.withDensity (fun x => ENNReal.ofReal (p x)) := by
  have hpos (x) : 0≤p x := ge_of_tendsto (hlim x) (Eventually.of_forall (fun n => hnonneg n x))
  refine ⟨hpos,?_⟩
  letI := IsLocallyFiniteMeasure.withDensity_ofReal (μ := ν) hp
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hi : Integrable (fun x => C*|f x|) ν := f.integrable.abs.const_mul C
  have ht := tendsto_integral_of_dominated_convergence (fun x => C*|f x|)
    (fun n => ((hpn n).mul f.continuous.measurable).aestronglyMeasurable) hi
    (fun n => ae_of_all _ (fun x => by
      change ‖pn n x*f x‖≤C*|f x|
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hnonneg n x)]
      exact mul_le_mul_of_nonneg_right (hbound n x) (abs_nonneg _)))
    (ae_of_all _ (fun x => (hlim x).mul_const (f x)))
  change Tendsto (fun n => ∫ x,pn n x*f x ∂ν) atTop (𝓝 (∫ x,p x*f x ∂ν)) at ht
  have he n : (∫ x,f x ∂ν.withDensity (fun x => ENNReal.ofReal (pn n x)))=
      ∫ x,pn n x*f x ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul (hpn n).ennreal_ofReal
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hnonneg n _),smul_eq_mul]
  have hep : (∫ x,f x ∂ν.withDensity (fun x => ENNReal.ofReal (p x)))=
      ∫ x,p x*f x ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul hp.measurable.ennreal_ofReal
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hpos _),smul_eq_mul]
  rw [hep]
  exact tendsto_nhds_unique (by simpa only [he] using hweak f) ht

end Asakura.Chapter12
