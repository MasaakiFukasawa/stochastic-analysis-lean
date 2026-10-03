import Chapter10MeasurableFlow

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Continuous time-dependent linear coefficients give a measurable solution
family on every finite horizon; no uniform bound over the entire half-line is
assumed. The forcing may be an actual stochastic integral path. -/
theorem continuous_linear_forced_family {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω]
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (W : ℝ → Ω → E) (hWm : ∀ t,Measurable (W t))
    (hWc : ∀ w,Continuous (fun t => W t w)) (T : ℝ) (hT : 0≤T) :
    ∃ X : E → ℝ → Ω → E,
      (∀ t,Measurable (fun p : E × Ω => X p.1 t p.2)) ∧
      (∀ x w,Continuous (fun t => X x t w)) ∧
      ∀ x w t,t∈Icc 0 T → X x t w=x+(∫ s in 0..t,A s (X x s w))+W t w := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let B := fun t => A (projIcc 0 T hT t).val
  have hBc : Continuous B := hA.comp (continuous_subtype_val.comp continuous_projIcc)
  have hb : ∀ t,LipschitzWith K (B t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((B t).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((hC _ (projIcc 0 T hT t).property).trans (le_max_left C 0)) (norm_nonneg _))
  obtain ⟨X,hm,hc,he⟩ := time_dependent_measurable_flow_exists
    (fun t x => B t x) K (hBc.comp continuous_fst |>.clm_apply continuous_snd) hb W hWm hWc T hT
  refine ⟨X,hm,hc,?_⟩
  intro x w t ht
  rw [he x w t ht]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s∈Icc 0 T := by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1,hs.2.trans ht.2⟩
  have hp : (projIcc 0 T hT s).val=s := by simp [projIcc,hs'.1,hs'.2]
  simp only [B,hp]

end Asakura.Chapter10
