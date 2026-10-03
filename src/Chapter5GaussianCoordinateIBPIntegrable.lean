import FullAuditGaussianIBP
import Mathlib.MeasureTheory.Integral.Pi
import Chapter5HeatFDeriv

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 2400000

/-- Gaussian integration by parts in any one coordinate of the genuine
finite product normal measure, proved by disintegration into that coordinate
and the remaining coordinates and one-dimensional integration by parts. -/
theorem gaussian_product_coordinate_ibp_integrable
    (n : ℕ) (i : Fin (n+1))
    (f df : (Fin (n+1) → ℝ) → ℝ) (hf : Measurable f) (hdf : Measurable df)
    (hif0 : Integrable f (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))
    (hid0 : Integrable df (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))
    (hixf0 : Integrable (fun z => z i*f z) (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))
    (hd : ∀ x : Fin n → ℝ,∀ y,
      HasDerivAt (fun u => f (i.insertNth u x)) (df (i.insertNth y x)) y) :
    (∫ z,df z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      ∫ z,z i*f z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  let μ := gaussianReal 0 1
  let ν := Measure.pi (fun _ : Fin (n+1) => μ)
  let ρ := Measure.pi (fun _ : Fin n => μ)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he (y : ℝ) (x : Fin n → ℝ) : e (y,x) = i.insertNth y x := rfl
  have hm : MeasurePreserving e (μ.prod ρ) ν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
  have hid : Integrable df ν := hid0
  have hif : Integrable (fun z : Fin (n+1) → ℝ => z i*f z) ν := hixf0
  have h0p : Integrable (fun p => f (e p)) (μ.prod ρ) := (hm.integrable_comp_emb e.measurableEmbedding).mpr hif0
  have hdp : Integrable (fun p => df (e p)) (μ.prod ρ) := (hm.integrable_comp_emb e.measurableEmbedding).mpr hid
  have hfp : Integrable (fun p => (e p) i*f (e p)) (μ.prod ρ) := (hm.integrable_comp_emb e.measurableEmbedding).mpr hif
  change (∫ z,df z ∂ν) = ∫ z,z i*f z ∂ν
  rw [← hm.integral_comp',← hm.integral_comp',integral_prod_symm _ hdp,integral_prod_symm _ hfp]
  apply integral_congr_ae
  filter_upwards [h0p.prod_left_ae,hdp.prod_left_ae,hfp.prod_left_ae] with x hx hdx hxx
  simp only [he,Fin.insertNth_apply_same] at hx hdx hxx ⊢
  simpa only [sub_zero,NNReal.coe_one,div_one] using
    gaussian_integration_by_parts (m := 0) (v := 1) (by norm_num) (hd x) hx hdx
      (by simpa only [sub_zero,NNReal.coe_one,div_one] using hxx)

end Asakura.Chapter5
