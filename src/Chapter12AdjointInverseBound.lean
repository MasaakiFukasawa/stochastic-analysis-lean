import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped RealInnerProductSpace InnerProduct
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem adjoint_norm_lower_of_inverse_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : E ≃L[ℝ] E) (C : ℝ) (hC : ‖J.symm.toContinuousLinearMap‖≤C) (v : E) :
    ‖v‖≤C*‖(ContinuousLinearMap.adjoint J.toContinuousLinearMap) v‖ := by
  have he : J.toContinuousLinearMap.comp J.symm.toContinuousLinearMap=ContinuousLinearMap.id ℝ E := by
    ext x
    exact J.apply_symm_apply x
  have ha : (ContinuousLinearMap.adjoint J.symm.toContinuousLinearMap) ((ContinuousLinearMap.adjoint J.toContinuousLinearMap) v)=v := by
    change ((ContinuousLinearMap.adjoint J.symm.toContinuousLinearMap).comp (ContinuousLinearMap.adjoint J.toContinuousLinearMap)) v=v
    rw [←ContinuousLinearMap.adjoint_comp,he]
    simp
  calc
    ‖v‖=‖(ContinuousLinearMap.adjoint J.symm.toContinuousLinearMap) ((ContinuousLinearMap.adjoint J.toContinuousLinearMap) v)‖ := congrArg norm ha.symm
    _≤‖(ContinuousLinearMap.adjoint J.symm.toContinuousLinearMap)‖*‖(ContinuousLinearMap.adjoint J.toContinuousLinearMap) v‖ := ContinuousLinearMap.le_opNorm _ _
    _≤C*‖(ContinuousLinearMap.adjoint J.toContinuousLinearMap) v‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_right hC (norm_nonneg _)

theorem adjoint_square_lower_of_exponential_inverse_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : E ≃L[ℝ] E) (K t : ℝ) (hJ : ‖J.symm.toContinuousLinearMap‖≤Real.exp (K*t)) (v : E) :
    Real.exp (-2*K*t)*‖v‖^2≤‖(ContinuousLinearMap.adjoint J.toContinuousLinearMap) v‖^2 := by
  have hh := adjoint_norm_lower_of_inverse_bound J (Real.exp (K*t)) hJ v
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-K*t)).le
  have he : Real.exp (-K*t)*Real.exp (K*t)=1 := by rw [←Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [←mul_assoc,he,one_mul] at hm
  have hs := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (norm_nonneg _)).mpr hm
  have he2 : (Real.exp (-K*t))^2=Real.exp (-2*K*t) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow,he2] using hs

end Asakura.Chapter12
