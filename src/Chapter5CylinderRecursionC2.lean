import Chapter5HeatC2Preservation
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- With bounded second derivatives the backwards cylinder recursion
can really be iterated. Averaging and identifying variables preserve
C² and explicit bounds for both derivatives. -/
theorem cylinder_recursion_preserves_bounded_C2
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ≥0) (hDb : ∀ x,‖D x‖ ≤ C) (hDDb : ∀ x,‖DD x‖ ≤ K)
    (L : V →L[ℝ] E) (t : ℝ) :
    let g := fun x => ∫ z,f (L x+Real.sqrt t • z) ∂ν
    ContDiff ℝ 2 g ∧ (∀ x,‖fderiv ℝ g x‖ ≤ C*‖L‖) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K*‖L‖^2) := by
  dsimp only
  obtain ⟨hs,_,_⟩ := averaging_preserves_bounded_C2 ν hi f D DD hd hdd hDc hDDc C K hDb hDDb t
  obtain ⟨h0,_,hb0,_⟩ := averaged_bounded_fderiv ν hi f D hd hDc C hDb
  obtain ⟨h1,_,hb1,_⟩ := averaged_bounded_fderiv ν hi D DD hdd hDDc K hDDb
  have he : fderiv ℝ (fun x => ∫ z,f (L x+Real.sqrt t • z) ∂ν) =
      fun x => (∫ z,D (L x+Real.sqrt t • z) ∂ν).comp L := by
    funext x
    exact ((h0 (L x) t).comp x L.hasFDerivAt).fderiv
  refine ⟨hs.comp L.contDiff,?_,?_⟩
  · intro x
    rw [he]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb0 (L x) t) (norm_nonneg L))
  · intro x
    rw [he]
    have hh := ((h1 (L x) t).comp x L.hasFDerivAt).clm_comp (hasFDerivAt_const L x)
    simp only [ContinuousLinearMap.comp_zero,zero_add,Function.comp_def] at hh
    rw [hh.fderiv]
    have hp : ‖(ContinuousLinearMap.compL ℝ V E ℝ).flip L‖ ≤ ‖L‖ := by
      calc
        _ ≤ ‖(ContinuousLinearMap.compL ℝ V E ℝ).flip‖ * ‖L‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1*‖L‖ := by rw [ContinuousLinearMap.opNorm_flip]; gcongr; exact ContinuousLinearMap.norm_compL_le ℝ V E ℝ
        _ = _ := one_mul _
    calc
      _ ≤ ‖(ContinuousLinearMap.compL ℝ V E ℝ).flip L‖ * ‖(∫ z,DD (L x+Real.sqrt t • z) ∂ν).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖ * (‖∫ z,DD (L x+Real.sqrt t • z) ∂ν‖ * ‖L‖) :=
        mul_le_mul hp (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg ((∫ z,DD (L x+Real.sqrt t • z) ∂ν).comp L)) (norm_nonneg L)
      _ ≤ ‖L‖ * ((K:ℝ)*‖L‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hb1 (L x) t) (norm_nonneg L)) (norm_nonneg L)
      _ = K*‖L‖^2 := by ring

end Asakura.Chapter5
