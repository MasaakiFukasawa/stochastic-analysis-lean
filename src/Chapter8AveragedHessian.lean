import Chapter8NewtonVectorPaths

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The averaged Hessian in the Newton proof is constructed by a Bochner integral. -/
theorem averaged_hessian_gradient_difference (g : E → E) (H : E → E →L[ℝ] E)
    (hD : ∀ x, HasFDerivAt g (H x) x) (hc : Continuous H) (x y : E) :
    (∫ s in (0:ℝ)..1, H (y+s • (x-y))) (x-y) = g x-g y := by
  have hp : Continuous (fun s : ℝ => y+s • (x-y)) := by fun_prop
  have hI : IntervalIntegrable (fun s : ℝ => H (y+s • (x-y))) volume 0 1 :=
    (hc.comp hp).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hI]
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => g (y+s • (x-y)))
      (H (y+s • (x-y)) (x-y)) s := by
    apply (hD _).comp_hasDerivAt s
    simpa using (((hasDerivAt_id s).smul_const (x-y)).const_add y)
  have hi : IntervalIntegrable (fun s : ℝ => H (y+s • (x-y)) (x-y)) volume 0 1 :=
    ((hc.comp hp).clm_apply continuous_const).intervalIntegrable 0 1
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi

/-- Integration preserves both quadratic bounds on the Hessian. -/
theorem averaged_hessian_bounds (H : ℝ → E →L[ℝ] E) (hc : Continuous H)
    (l u : ℝ) (hb : ∀ s ∈ Icc (0:ℝ) 1, ∀ x,
      l*‖x‖^2 ≤ ⟪x,H s x⟫ ∧ ⟪x,H s x⟫ ≤ u*‖x‖^2) (x : E) :
    l*‖x‖^2 ≤ ⟪x,(∫ s in (0:ℝ)..1,H s) x⟫ ∧
      ⟪x,(∫ s in (0:ℝ)..1,H s) x⟫ ≤ u*‖x‖^2 := by
  have hi := hc.intervalIntegrable (μ := volume) 0 1
  have hix : IntervalIntegrable (fun s => H s x) volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  have he : ⟪x,(∫ s in (0:ℝ)..1,H s) x⟫ = ∫ s in (0:ℝ)..1,⟪x,H s x⟫ := by
    rw [ContinuousLinearMap.intervalIntegral_apply hi]
    exact ((innerSL ℝ x).intervalIntegral_comp_comm hix).symm
  rw [he]
  have hcinner : Continuous (fun s => ⟪x,H s x⟫) := continuous_const.inner (hc.clm_apply continuous_const)
  constructor
  · have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
      (continuous_const.intervalIntegrable 0 1) (hcinner.intervalIntegrable 0 1)
      (fun s hs => (hb s hs x).1)
    simpa using hh
  · have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
      (hcinner.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
      (fun s hs => (hb s hs x).2)
    simpa using hh

theorem averaged_hessian_symmetric (H : ℝ → E →L[ℝ] E) (hc : Continuous H)
    (hs : ∀ s, (H s).toLinearMap.IsSymmetric) :
    (∫ s in (0:ℝ)..1,H s).toLinearMap.IsSymmetric := by
  intro x y
  have hi := hc.intervalIntegrable (μ := volume) 0 1
  change ⟪(∫ s in (0:ℝ)..1,H s) x,y⟫ = ⟪x,(∫ s in (0:ℝ)..1,H s) y⟫
  rw [ContinuousLinearMap.intervalIntegral_apply hi,ContinuousLinearMap.intervalIntegral_apply hi,
    real_inner_comm y (∫ s in (0:ℝ)..1,H s x)]
  have hix : IntervalIntegrable (fun s => H s x) volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  have hiy : IntervalIntegrable (fun s => H s y) volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  have hxint := (innerSL ℝ y).intervalIntegral_comp_comm hix
  have hyint := (innerSL ℝ x).intervalIntegral_comp_comm hiy
  simp only [innerSL_apply_apply] at hxint hyint
  rw [← hxint,← hyint]
  apply intervalIntegral.integral_congr
  intro s _
  have hh := hs s x y
  change ⟪H s x,y⟫ = ⟪x,H s y⟫ at hh
  change ⟪y,H s x⟫ = ⟪x,H s y⟫
  rw [real_inner_comm (H s x) y]
  exact hh

end Asakura.Chapter8
