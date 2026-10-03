import FullAuditGaussianIBP
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- The single-coordinate integration by parts, before integrating the other coordinates. -/
theorem gaussian_product_rule_ibp {f g df dg : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hfg : Integrable (fun x => f x*g x) (gaussianReal 0 1))
    (hgd : Integrable (fun x => g x*df x) (gaussianReal 0 1))
    (hfd : Integrable (fun x => f x*dg x) (gaussianReal 0 1))
    (hxfg : Integrable (fun x => x*f x*g x) (gaussianReal 0 1)) :
    (∫ x, g x*df x ∂gaussianReal 0 1) =
      ∫ x, f x*(x*g x-dg x) ∂gaussianReal 0 1 := by
  have hd (x : ℝ) := (hf x).mul (hg x)
  have hgd2 : Integrable (fun x => df x*g x) (gaussianReal 0 1) := by
    simpa only [mul_comm] using hgd
  have hsum : Integrable (fun x => df x*g x+f x*dg x) (gaussianReal 0 1) := by
    exact hgd2.add hfd
  have hx : Integrable (fun x => ((x-0)/(1:ℝ≥0))* (f x*g x)) (gaussianReal 0 1) := by
    simpa only [NNReal.coe_one,sub_zero,div_one,mul_assoc] using hxfg
  have h := gaussian_integration_by_parts (by norm_num : (1:ℝ≥0) ≠ 0) hd hfg hsum hx
  simp only [NNReal.coe_one,sub_zero,div_one] at h
  rw [integral_add hgd2 hfd] at h
  calc
    _ = (∫ x, x*(f x*g x) ∂gaussianReal 0 1) - ∫ x, f x*dg x ∂gaussianReal 0 1 := by
      simpa only [mul_comm,Pi.mul_apply] using (eq_sub_iff_add_eq.mpr h)
    _ = _ := by
      rw [← integral_sub (by simpa only [mul_assoc] using hxfg) hfd]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

/-- Fubini in an arbitrary coordinate of the finite Gaussian product. All
 integrability obligations are explicit; no multidimensional IBP theorem is used. -/
theorem gaussian_finite_coordinate_ibp {n : ℕ} (i : Fin (n+1))
    {f g df dg : (Fin (n+1) → ℝ) → ℝ}
    (hf : ∀ z y, HasDerivAt (fun x => f (i.insertNth x z)) (df (i.insertNth y z)) y)
    (hg : ∀ z y, HasDerivAt (fun x => g (i.insertNth x z)) (dg (i.insertNth y z)) y)
    (hfg : Integrable (fun z => f z*g z) (Measure.pi fun _ => gaussianReal 0 1))
    (hgd : Integrable (fun z => g z*df z) (Measure.pi fun _ => gaussianReal 0 1))
    (hfd : Integrable (fun z => f z*dg z) (Measure.pi fun _ => gaussianReal 0 1))
    (hxfg : Integrable (fun z => z i*f z*g z) (Measure.pi fun _ => gaussianReal 0 1)) :
    (∫ z, g z*df z ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, f z*(z i*g z-dg z) ∂Measure.pi fun _ => gaussianReal 0 1 := by
  let μ : Measure (Fin (n+1) → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he : MeasurePreserving e ((gaussianReal 0 1).prod ν) μ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hfgp := he.integrable_comp_of_integrable hfg
  have hgdp := he.integrable_comp_of_integrable hgd
  have hfdp := he.integrable_comp_of_integrable hfd
  have hxfgp := he.integrable_comp_of_integrable hxfg
  have hr : Integrable (fun z => f z*(z i*g z-dg z)) μ := by
    convert hxfg.sub hfd using 1
    ext z; simp only [Pi.sub_apply]; ring
  rw [← he.integral_comp',
      ← he.integral_comp']
  have hrp := he.integrable_comp_of_integrable hr
  simp only [Function.comp_def] at hfgp hgdp hfdp hxfgp hrp
  rw [integral_prod_symm _ hgdp, integral_prod_symm _ hrp]
  apply integral_congr_ae
  filter_upwards [hfgp.prod_left_ae,hgdp.prod_left_ae,hfdp.prod_left_ae,hxfgp.prod_left_ae]
    with z h1 h2 h3 h4
  have heq (x : ℝ) : e (x,z) = i.insertNth x z := rfl
  simp only [Function.comp_def,heq] at h1 h2 h3 h4 ⊢
  have hi (x : ℝ) : i.insertNth (α := fun _ => ℝ) x z i = x := by simp
  simp only [hi] at h4 ⊢
  exact gaussian_product_rule_ibp (hf z) (hg z) h1 h2 h3 h4

end Asakura.FullAudit
