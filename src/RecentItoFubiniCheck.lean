import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Abstract functional-analytic steps in the CURRENT manuscript proof.
These declarations do not construct stochastic integration or quadratic variation.
K models the weighted integrand Hilbert space and V models M₂. The concrete
identifications and measurability of x ↦ [H(x)] remain explicit bridge obligations.
-/
open MeasureTheory
open scoped ENNReal
namespace Asakura.RecentItoFubini
variable {E K V B J : Type*} [MeasurableSpace E]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- No simple-function approximation is required AGAIN once strong measurability
and integrability of the norm have been established. -/
theorem integrable_from_norm (μ : Measure E) (Z : E → V)
    (hm : AEStronglyMeasurable Z μ) (hn : Integrable (fun x => ‖Z x‖) μ) :
    Integrable Z μ := (integrable_norm_iff hm).mp hn

/-- The isometry makes the manuscript's mixed-norm hypothesis exactly L¹
integrability of the M₂-valued integral family. -/
theorem ito_family_L1 (μ : Measure E) (I : K →ₗᵢ[ℝ] V) (H : E → K)
    (hm : AEStronglyMeasurable H μ) (hn : Integrable (fun x => ‖H x‖) μ) :
    Integrable (fun x => I (H x)) μ := by
  apply I.toContinuousLinearMap.integrable_comp
  exact (integrable_norm_iff hm).mp hn

theorem ito_family_norm_integral (μ : Measure E) (I : K →ₗᵢ[ℝ] V) (H : E → K) :
    (∫ x, ‖I (H x)‖ ∂μ) = ∫ x, ‖H x‖ ∂μ := by simp

/-- This is a consequence, NOT a construction, of the assumed Ito isometry. -/
theorem ito_norm_square (I : K →ₗᵢ[ℝ] V) (h : K) :
    ‖I h‖ ^ 2 = ‖h‖ ^ 2 := by rw [I.norm_map]

theorem covariance_integral (μ : Measure E) (C : V →L[ℝ] B) (Z : E → V)
    (hZ : Integrable Z μ) : C (∫ x, Z x ∂μ) = ∫ x, C (Z x) ∂μ := by
  exact (C.integral_comp_comm hZ).symm

/-- Written proof route: pass each covariance through the Bochner integral,
use the pointwise bracket identity, then apply separation. No Fubini equality
is included among the hypotheses. -/
theorem fubini_by_covariance_separation (μ : Measure E)
    (I : K →L[ℝ] V) (C : J → V →L[ℝ] B) (D : J → K →L[ℝ] B)
    (sep : ∀ u v : V, (∀ y, C y u = C y v) → u = v)
    (bracket_identity : ∀ y h, C y (I h) = D y h)
    (H : E → K) (hH : Integrable H μ) :
    (∫ x, I (H x) ∂μ) = I (∫ x, H x ∂μ) := by
  apply sep
  intro y
  calc
    C y (∫ x, I (H x) ∂μ) = ∫ x, C y (I (H x)) ∂μ :=
      ((C y).integral_comp_comm (I.integrable_comp hH)).symm
    _ = ∫ x, D y (H x) ∂μ := by simp only [bracket_identity]
    _ = D y (∫ x, H x ∂μ) := (D y).integral_comp_comm hH
    _ = C y (I (∫ x, H x ∂μ)) := (bracket_identity _ _).symm

/-- Actual Bochner integral existence and norm bound in a complete target. -/
theorem integral_norm_bound (μ : Measure E) (Z : E → V) :
    ‖∫ x, Z x ∂μ‖ ≤ ∫ x, ‖Z x‖ ∂μ := norm_integral_le_integral_norm Z

/-- Covariance determines a Hilbert-space element: concrete nondegenerate
model of the separation step (not the manuscript's quadratic covariation). -/
theorem hilbert_separation {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (u v : W) (h : ∀ y, inner ℝ u y = inner ℝ v y) : u = v := by
  have hzero : inner ℝ (u-v) (u-v) = 0 := by rw [inner_sub_left, h]; simp
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hzero)

end Asakura.RecentItoFubini
#print axioms Asakura.RecentItoFubini.integrable_from_norm
#print axioms Asakura.RecentItoFubini.ito_family_L1
#print axioms Asakura.RecentItoFubini.ito_family_norm_integral
#print axioms Asakura.RecentItoFubini.ito_norm_square
#print axioms Asakura.RecentItoFubini.covariance_integral
#print axioms Asakura.RecentItoFubini.fubini_by_covariance_separation
#print axioms Asakura.RecentItoFubini.integral_norm_bound
#print axioms Asakura.RecentItoFubini.hilbert_separation
