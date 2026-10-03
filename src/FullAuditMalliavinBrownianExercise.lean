import FullAuditGaussianIBP
import FullAuditFiniteBrownianHitting
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianTimeVector (T : ℝ≥0) : Lp ℝ 2 (volume.restrict (Icc (0:ℝ) T)) :=
  (memLp_const (1:ℝ)).toLp (fun _ => 1)

/-- The Malliavin covariance is the actual L2[0,T] norm squared of D W_T=1. -/
theorem brownian_malliavin_covariance (T : ℝ≥0) :
    ⟪brownianTimeVector T,brownianTimeVector T⟫_ℝ = (T:ℝ) := by
  rw [L2.inner_def]
  have h := (memLp_const (μ := volume.restrict (Icc (0:ℝ) T)) (p := 2) (1:ℝ)).coeFn_toLp
  calc
    _ = ∫ _ : ℝ, (1:ℝ) ∂volume.restrict (Icc (0:ℝ) T) := by
      apply integral_congr_ae
      filter_upwards [h] with x hx
      change inner ℝ (brownianTimeVector T x) (brownianTimeVector T x) = 1
      change brownianTimeVector T x = 1 at hx
      rw [hx]
      norm_num
    _ = (T:ℝ) := by
      rw [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
      rw [Real.volume_Icc,sub_zero]
      exact ENNReal.toReal_ofReal T.property

/-- U_1 is the deterministic function 1/T on [0,T]. -/
theorem brownian_malliavin_inverse_direction (T : ℝ≥0) :
    ((1/(T:ℝ)) • brownianTimeVector T : Lp ℝ 2 (volume.restrict (Icc (0:ℝ) T))) =ᵐ[volume.restrict (Icc (0:ℝ) T)]
      (fun _ => 1/(T:ℝ)) := by
  have h := (memLp_const (μ := volume.restrict (Icc (0:ℝ) T)) (p := 2) (1:ℝ)).coeFn_toLp
  filter_upwards [Lp.coeFn_smul (1/(T:ℝ)) (brownianTimeVector T),h] with x hx h1
  rw [hx]
  change (1/(T:ℝ))*brownianTimeVector T x = 1/(T:ℝ)
  change brownianTimeVector T x = 1 at h1
  rw [h1,mul_one]

/-- For deterministic directions the divergence is the Wiener integral.
 Its linearity and integral of 1 give H_1(W_T,1)=W_T/T. -/
theorem brownian_malliavin_weight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℝ≥0) (WT : Ω → ℝ)
    (I : Lp ℝ 2 (volume.restrict (Icc (0:ℝ) T)) →ₗ[ℝ] Lp ℝ 2 P)
    (hI : I (brownianTimeVector T) =ᵐ[P] WT) :
    I ((1/(T:ℝ)) • brownianTimeVector T) =ᵐ[P] (fun ω => WT ω/(T:ℝ)) := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (1/(T:ℝ)) (I (brownianTimeVector T)),hI] with ω hω he
  rw [hω]
  simp only [Pi.smul_apply,smul_eq_mul,he]
  ring

/-- Substitution of the Brownian marginal law in the proved Gaussian IBP
 gives exactly the weighted Malliavin formula in the exercise. -/
theorem brownian_weighted_ibp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (T : ℝ≥0) (hT : T ≠ 0)
    (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x)
    (hf : Integrable f (gaussianReal 0 T)) (hdf : Integrable df (gaussianReal 0 T))
    (hxf : Integrable (fun x => (x/(T:ℝ))*f x) (gaussianReal 0 T)) :
    (∫ ω, df (B T ω) ∂P) = ∫ ω, f (B T ω)*B T ω/(T:ℝ) ∂P := by
  have h := gaussian_integration_by_parts hT hd hf hdf (by simpa only [sub_zero] using hxf)
  simp only [sub_zero] at h
  have he1 := (hB.hasLaw_eval T).integral_comp hdf.aestronglyMeasurable
  have he2 := (hB.hasLaw_eval T).integral_comp hxf.aestronglyMeasurable
  change (∫ ω, df (B T ω) ∂P) = _ at he1
  change (∫ ω, (B T ω/(T:ℝ))*f (B T ω) ∂P) = _ at he2
  rw [he1,h,← he2]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by ring

end Asakura.FullAudit
