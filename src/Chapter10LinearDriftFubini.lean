import Chapter10LinearProductMeanZero
import Chapter8DynkinFubini

open MeasureTheory Set Filter
open scoped NNReal
namespace Asakura.Chapter10
open Asakura.Chapter8
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The finite-horizon L2 path estimate proves Fubini for the quadratic
linear drift, without assuming integrability of the product space integrand. -/
theorem linear_drift_fubini {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (T : ℝ) (hT : 0≤T) (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hm : Measurable X) (hX : MemLp X 2 P)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K) (i j : Fin d) (r : ℝ) (hr : 0≤r) :
    let R := fun w s => X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i
    Integrable (fun w => ∫ s in 0..r,R w s) P ∧
      (∫ w,(∫ s in 0..r,R w s) ∂P)=∫ s in 0..r,∫ w,R w s ∂P := by
  dsimp only
  let U := fun s w => X w (projIcc 0 T hT s)
  have hUc w : Continuous (fun s => U s w) := (X w).continuous.comp continuous_projIcc
  have hUm s : Measurable (U s) := (continuous_eval_const _).measurable.comp hm
  have hRc w : Continuous (fun s => U s w j*(A s (U s w)) i) :=
    ((continuous_apply j).comp (hUc w)).mul
      ((continuous_apply i).comp (hA.clm_apply (hUc w)))
  have hRm s : Measurable (fun w => U s w j*(A s (U s w)) i) :=
    ((measurable_pi_apply j).comp (hUm s)).mul
      ((measurable_pi_apply i).comp ((A s).continuous.measurable.comp (hUm s)))
  apply dynkin_fubini P r hr (fun w s => U s w j*(A s (U s w)) i)
    ((measurable_uncurry_of_continuous_of_measurable hRc hRm).comp measurable_swap)
    (fun w => (K:ℝ)*‖X w‖^2) (hX.norm.integrable_sq.const_mul K)
  apply ae_of_all
  intro w s _
  have hu : ‖U s w‖≤‖X w‖ := (X w).norm_coe_le_norm _
  have hui : ‖U s w j‖≤‖X w‖ := (norm_le_pi_norm _ j).trans hu
  have hai : ‖(A s (U s w)) i‖≤(K:ℝ)*‖X w‖ :=
    (norm_le_pi_norm _ i).trans (((A s).le_opNorm _).trans
      (mul_le_mul (hAK s) hu (norm_nonneg _) K.coe_nonneg))
  rw [norm_mul]
  have hh := mul_le_mul hui hai (norm_nonneg _) (norm_nonneg (X w))
  nlinarith

end Asakura.Chapter10
