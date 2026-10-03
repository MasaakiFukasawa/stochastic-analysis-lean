import Chapter8LipschitzTransition

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Synchronous contraction controls an observable whose local Lipschitz
constant grows linearly, using only second moments. This covers entries of
Phi(x)^T a^{-1} Phi(x). -/
theorem weighted_coupling_expectation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → E) (A : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hY : MemLp Y 2 P) (hA : MemLp A 2 P) (hAn : ∀ w,0≤A w)
    (a C : ℝ) (ha : 0≤a) (ha1 : a≤1) (hC : 0≤C)
    (hXY : ∀ᵐ w ∂P,‖X w-Y w‖≤a*A w)
    (f : E → ℝ) (hf : Continuous f)
    (hLip : ∀ x y,|f x-f y|≤C*‖x-y‖*(1+‖x‖+‖y‖)) :
    Integrable (fun w => f (X w)-f (Y w)) P ∧
      (∫ w,|f (X w)-f (Y w)| ∂P) ≤
        C*a*(1+3*(∫ w,(A w)^2 ∂P)+2*(∫ w,‖Y w‖^2 ∂P)) := by
  have hp : ∀ᵐ w ∂P, |f (X w)-f (Y w)|≤C*a*(1+3*(A w)^2+2*‖Y w‖^2) := by
    filter_upwards [hXY] with w hXYw
    have hnorm : ‖X w‖≤A w+‖Y w‖ := by
      have hh := norm_add_le (X w-Y w) (Y w)
      rw [sub_add_cancel] at hh
      exact hh.trans (add_le_add (hXYw.trans (mul_le_of_le_one_left (hAn w) ha1)) le_rfl)
    have hq : A w*(1+‖X w‖+‖Y w‖)≤1+3*(A w)^2+2*‖Y w‖^2 := by
      have hn := norm_nonneg (Y w)
      have he := mul_le_mul_of_nonneg_left hnorm (hAn w)
      nlinarith [sq_nonneg (A w-1),sq_nonneg (A w-‖Y w‖)]
    calc
      _ ≤ C*‖X w-Y w‖*(1+‖X w‖+‖Y w‖) := hLip _ _
      _ ≤ C*(a*A w)*(1+‖X w‖+‖Y w‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXYw hC) (by positivity)
      _ = C*a*(A w*(1+‖X w‖+‖Y w‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (mul_nonneg hC ha)
  have hAi : Integrable (fun w => (A w)^2) P :=
    (memLp_two_iff_integrable_sq hA.aestronglyMeasurable).mp hA
  have hYi : Integrable (fun w => ‖Y w‖^2) P := hY.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hbound : Integrable (fun w => C*a*(1+3*(A w)^2+2*‖Y w‖^2)) P :=
    (((integrable_const (1:ℝ)).add (hAi.const_mul 3)).add (hYi.const_mul 2)).const_mul (C*a)
  have hi : Integrable (fun w => f (X w)-f (Y w)) P := by
    apply hbound.mono' ((hf.measurable.comp hXm).sub (hf.measurable.comp hYm)).aestronglyMeasurable
    simpa only [Real.norm_eq_abs,Pi.sub_apply,Function.comp_def] using hp
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi.abs hbound hp
  rw [integral_const_mul,integral_add (f := fun w => 1+3*(A w)^2) (g := fun w => 2*‖Y w‖^2)
    ((integrable_const (1:ℝ)).add (hAi.const_mul 3)) (hYi.const_mul 2),
    integral_add (f := fun _ => (1:ℝ)) (g := fun w => 3*(A w)^2) (integrable_const _) (hAi.const_mul 3),
    integral_const_mul,integral_const_mul,integral_const,probReal_univ,one_smul] at hh
  exact hh

end Asakura.Chapter8
