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
theorem gaussian_product_coordinate_ibp
    (n : ℕ) (i : Fin (n+1))
    (f df : (Fin (n+1) → ℝ) → ℝ) (hf : Measurable f) (hdf : Measurable df)
    (C D : ℝ) (hb : ∀ z,‖f z‖ ≤ C) (hdb : ∀ z,‖df z‖ ≤ D)
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
  have hid : Integrable df ν := Integrable.of_bound hdf.aestronglyMeasurable D (ae_of_all _ hdb)
  have hiid : Integrable (fun z : Fin (n+1) → ℝ => z i) ν :=
    integrable_comp_eval (μ := fun _ : Fin (n+1) => gaussianReal 0 1) (i := i) (f := fun z : ℝ => z)
      ((memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num))
  have hif : Integrable (fun z : Fin (n+1) → ℝ => z i*f z) ν :=
    hiid.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hb)
  have hdp : Integrable (fun p => df (e p)) (μ.prod ρ) := (hm.integrable_comp_emb e.measurableEmbedding).mpr hid
  have hfp : Integrable (fun p => (e p) i*f (e p)) (μ.prod ρ) := (hm.integrable_comp_emb e.measurableEmbedding).mpr hif
  change (∫ z,df z ∂ν) = ∫ z,z i*f z ∂ν
  rw [← hm.integral_comp',← hm.integral_comp',integral_prod_symm _ hdp,integral_prod_symm _ hfp]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [he,Fin.insertNth_apply_same]
  have hdm : Measurable (fun y => df (i.insertNth y x)) := by
    simpa only [Function.comp_def,id_eq,he] using hdf.comp (e.measurable.comp (measurable_id.prodMk measurable_const))
  simpa only [sub_zero,NNReal.coe_one,div_one] using
    gaussian_ibp_bounded (m := 0) (v := 1) (by norm_num) (hd x) hdm C D
      (fun y => hb _) (fun y => hdb _)

end Asakura.Chapter5
