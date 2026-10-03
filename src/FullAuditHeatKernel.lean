import FullAuditGaussianIBP
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

noncomputable def heatAverage (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  ∫ z, f (x + Real.sqrt t*z) ∂gaussianReal 0 1

theorem heatAverage_zero (f : ℝ → ℝ) (x : ℝ) : heatAverage f x 0 = f x := by
  simp [heatAverage]

/-- Dominated convergence gives joint continuity, including time zero. -/
theorem heatAverage_continuous {f : ℝ → ℝ} (hf : Continuous f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Continuous (fun p : ℝ × ℝ => heatAverage f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall fun q => (hf.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun q => ae_of_all _ fun z => hb _
  · exact integrable_const C
  · exact ae_of_all _ fun z => (hf.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => q.1+Real.sqrt q.2*z))).continuousAt

/-- Uniform bound for the actual Gaussian convolution. -/
theorem heatAverage_bound {f : ℝ → ℝ} (hf : Continuous f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x t : ℝ) : ‖heatAverage f x t‖ ≤ C := by
  unfold heatAverage
  have hi : Integrable (fun z => f (x+Real.sqrt t*z)) (gaussianReal 0 1) :=
    Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hb _)
  calc
    _ ≤ ∫ z, ‖f (x+Real.sqrt t*z)‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C ∂gaussianReal 0 1 := integral_mono hi.norm (integrable_const C) (fun z => hb _)
    _ = C := by simp

/-- Space differentiation under the integral, justified by a uniform derivative bound. -/
theorem heatAverage_space_derivative {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdf : Continuous df)
    (C D : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) (hb : ∀ x, ‖df x‖ ≤ D) (x t : ℝ) :
    HasDerivAt (fun y => heatAverage f y t) (heatAverage df x t) x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := univ) (bound := fun _ => D) (F' := fun y z => df (y+Real.sqrt t*z))
    (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_const D) ?_).2
  · exact Eventually.of_forall fun y => (hfc.comp (by fun_prop)).aestronglyMeasurable
  · exact Integrable.of_bound (hfc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hf _)
  · exact (hdf.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ fun z y _ => hb _
  · exact ae_of_all _ fun z y _ => by
      simpa only [mul_one,Function.comp_def,id_eq] using (hd (y+Real.sqrt t*z)).comp y ((hasDerivAt_id y).add_const (Real.sqrt t*z))

/-- The raw time derivative for positive times, before Gaussian integration by parts. -/
theorem heatAverage_time_raw {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdf : Continuous df)
    (C D : ℝ) (hf : ∀ x, ‖f x‖ ≤ C) (hb : ∀ x, ‖df x‖ ≤ D)
    (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (heatAverage f x)
      (∫ z, df (x+Real.sqrt t*z)*(z/(2*Real.sqrt t)) ∂gaussianReal 0 1) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hD : 0 ≤ D := (norm_nonneg (df 0)).trans (hb 0)
  have hs : 0 < Real.sqrt (t/2) := Real.sqrt_pos.2 (by linarith)
  have hiZ : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 1 (by norm_num)).integrable (by norm_num)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Ioi (t/2))
    (bound := fun z => D*‖z‖/(2*Real.sqrt (t/2)))
    (F' := fun u z => df (x+Real.sqrt u*z)*(z/(2*Real.sqrt u)))
    (Ioi_mem_nhds (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun u => (hfc.comp (by fun_prop)).aestronglyMeasurable
  · exact Integrable.of_bound (hfc.comp (by fun_prop)).aestronglyMeasurable C (ae_of_all _ fun z => hf _)
  · exact ((hdf.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · apply ae_of_all
    intro z u hu
    have hu0 : 0 < u := lt_trans (by linarith : 0 < t/2) hu
    rw [norm_mul,norm_div,Real.norm_eq_abs (2*Real.sqrt u),abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hu0))]
    calc
      _ ≤ D*(‖z‖/(2*Real.sqrt u)) := mul_le_mul_of_nonneg_right (hb _) (div_nonneg (norm_nonneg _) (by positivity))
      _ = D*‖z‖/(2*Real.sqrt u) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hD (norm_nonneg _)) (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu.le) (by norm_num))
  · exact (hiZ.norm.const_mul D).div_const _
  · apply ae_of_all
    intro z u hu
    have hu0 : 0 < u := lt_trans (by linarith : 0 < t/2) hu
    convert (hd (x+Real.sqrt u*z)).comp u (((Real.hasDerivAt_sqrt hu0.ne').mul_const z).const_add x) using 1
    · rfl
    · ring

/-- Gaussian integration by parts identifies the raw derivative with half the
second space derivative of the convolution. -/
theorem heatAverage_heat_equation {f df ddf : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hcdd : Continuous ddf) (C D E : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ C) (hdf : ∀ x, ‖df x‖ ≤ D) (hddf : ∀ x, ‖ddf x‖ ≤ E)
    (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (heatAverage f x) ((1/2)*heatAverage ddf x t) t := by
  have hcdf : Continuous df := continuous_iff_continuousAt.mpr fun x => (hdd x).continuousAt
  have hs := Real.sqrt_pos.2 ht
  have hcomp : ∀ z, HasDerivAt (fun z => df (x+Real.sqrt t*z))
      (Real.sqrt t*ddf (x+Real.sqrt t*z)) z := by
    intro z
    convert (hdd (x+Real.sqrt t*z)).comp z (((hasDerivAt_id z).const_mul (Real.sqrt t)).const_add x) using 1
    · rfl
    · simp only [mul_one]; ring
  have hibp := gaussian_ibp_bounded (m := 0) (v := 1) (by norm_num)
    hcomp (by fun_prop) D (Real.sqrt t*E) (fun z => hdf _) (fun z => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left (hddf _) hs.le)
  simp only [NNReal.coe_one,sub_zero,div_one,integral_const_mul] at hibp
  have hraw := heatAverage_time_raw hd hcdf C D hf hdf x t ht
  convert hraw using 1
  calc
    (1/2)*heatAverage ddf x t = (Real.sqrt t*heatAverage ddf x t)/(2*Real.sqrt t) := by field_simp
    _ = (∫ z, z*df (x+Real.sqrt t*z) ∂gaussianReal 0 1)/(2*Real.sqrt t) := by rw [← hibp]; rfl
    _ = ∫ z, df (x+Real.sqrt t*z)*(z/(2*Real.sqrt t)) ∂gaussianReal 0 1 := by
      rw [← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by ring

end Asakura.FullAudit
