import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.FullAudit

/-- Differentiation of the actual normal density, with nonzero variance. -/
theorem gaussian_density_derivative (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (-((x-m)/(v:ℝ)) * gaussianPDFReal m v x) x := by
  have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  have hd := ((((hasDerivAt_id x).sub_const m).pow 2).neg.div_const (2*(v:ℝ))).exp.const_mul
    ((Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹)
  convert hd using 1
  · rfl
  · simp only [gaussianPDFReal,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one]
    field_simp
    <;> ring

/-- Transfer integrability to Lebesgue measure without an implicit density assumption. -/
theorem gaussian_integrable_density {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal m v) ↔ Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero m hv]
  simpa only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (μ := volume)
      (measurable_gaussianPDF m v) (ae_of_all _ fun _ => gaussianPDF_lt_top) (g := f))

/-- Ordinary integration by parts, the one-dimensional step of the manuscript's
Gaussian proof. Integrability is explicit, so it applies beyond bounded functions. -/
theorem gaussian_integration_by_parts {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f df : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (df x) x)
    (hf : Integrable f (gaussianReal m v))
    (hdf : Integrable df (gaussianReal m v))
    (hxf : Integrable (fun x => ((x-m)/(v:ℝ))*f x) (gaussianReal m v)) :
    (∫ x, df x ∂gaussianReal m v) =
      ∫ x, ((x-m)/(v:ℝ))*f x ∂gaussianReal m v := by
  have h1 := (gaussian_integrable_density hv).mp hf
  have h2 := (gaussian_integrable_density hv).mp hdf
  have h3 := (gaussian_integrable_density hv).mp hxf
  have h3n : Integrable (fun x => f x * (-((x-m)/(v:ℝ))*gaussianPDFReal m v x)) := by
    convert h3.neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have h2r : Integrable (fun x => df x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using h2
  have h1r : Integrable (fun x => f x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using h1
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => gaussian_density_derivative m v hv x) h3n h2r h1r
  have he : (∫ x, f x * (-((x-m)/(v:ℝ))*gaussianPDFReal m v x)) =
      -(∫ x, gaussianPDFReal m v x * (((x-m)/(v:ℝ))*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  rw [he] at hibp
  simp only [integral_gaussianReal_eq_integral_smul hv,smul_eq_mul]
  have hh := neg_injective hibp
  simpa only [mul_comm] using hh.symm

/-- Bounded first derivatives suffice in the heat-kernel calculation. -/
theorem gaussian_ibp_bounded {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f df : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (df x) x)
    (hmd : Measurable df) (C D : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) (hdf : ∀ x, ‖df x‖ ≤ D) :
    (∫ x, df x ∂gaussianReal m v) =
      ∫ x, ((x-m)/(v:ℝ))*f x ∂gaussianReal m v := by
  have hm : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hi : Integrable f (gaussianReal m v) := Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hf)
  have hid : Integrable df (gaussianReal m v) := Integrable.of_bound hmd.aestronglyMeasurable D (ae_of_all _ hdf)
  have hix : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num)
  have hixf : Integrable (fun x => ((x-m)/(v:ℝ))*f x) (gaussianReal m v) := by
    exact ((hix.sub (integrable_const m)).div_const (v:ℝ)).mul_bdd hm.aestronglyMeasurable (ae_of_all _ hf)
  exact gaussian_integration_by_parts hv hd hi hid hixf

end Asakura.FullAudit
