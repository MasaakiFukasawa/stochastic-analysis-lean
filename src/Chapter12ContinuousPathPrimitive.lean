import Chapter12ContinuousMapOperator
import Chapter8ForcedIntegralExistence

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def pathPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0≤T) : C(Icc (0:ℝ) T,E) →L[ℝ] C(Icc (0:ℝ) T,E) := by
  let L : C(Icc (0:ℝ) T,E) →ₗ[ℝ] C(Icc (0:ℝ) T,E) :=
    { toFun := fun f => ⟨fun t => ∫ s in 0..t.val,f (projIcc 0 T hT s),
        (intervalIntegral.differentiable_integral_of_continuous
          (f.continuous.comp continuous_projIcc)).continuous.comp continuous_subtype_val⟩
      map_add' := by
        intro f g
        ext t
        exact intervalIntegral.integral_add ((f.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((g.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := by
        intro a f
        ext t
        exact intervalIntegral.integral_smul a _ }
  refine L.mkContinuous T ?_
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg _))).mpr
  intro t
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=t.val) (f:=fun s => f (projIcc 0 T hT s)) (C:=‖f‖)
    (fun s _ => f.norm_coe_le_norm _)
  change ‖∫ s in 0..t.val,f (projIcc 0 T hT s)‖≤T*‖f‖
  apply hh.trans
  rw [sub_zero,abs_of_nonneg t.property.1]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left t.property.2 (norm_nonneg f)

@[simp] theorem pathPrimitive_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0≤T) (f : C(Icc (0:ℝ) T,E)) (t : Icc (0:ℝ) T) :
    pathPrimitive T hT f t=∫ s in 0..t.val,f (projIcc 0 T hT s) := rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.pathPrimitive
