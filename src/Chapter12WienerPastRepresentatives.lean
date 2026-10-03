import Chapter12WienerFiniteFamilies

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The past coordinates may be the original continuous Brownian process,
which agrees coordinatewise almost everywhere with Wiener representatives.
No uncountable intersection of these almost-everywhere equalities is taken. -/
theorem wiener_future_independent_past_representatives {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (n : ℕ) (u : Fin n → H) (v : ι → H) (I : ι → Ω → ℝ)
    (hI : ∀ j,Measurable (I j)) (heq : ∀ j,I j =ᵐ[P] (W (v j) : Ω → ℝ))
    (huv : ∀ i j,inner ℝ (u i) (v j)=0) :
    IndepFun (fun w i => W (u i) w) (fun w j => I j w) P := by
  classical
  have hm (h : H) : (∫ w,W h w ∂P)=0 := by
    simpa only [integral_id_gaussianReal] using (hlaw h).integral_eq
  apply Asakura.Chapter10.gaussian_error_independent_history P _ _
    (Measurable.of_eval (fun i => (Lp.stronglyMeasurable (W (u i))).measurable)) hI
  · intro J
    apply (wiener_pair_finite_gaussian P W hlaw u (fun j : J => v j.val)).congr
    filter_upwards [ae_all_iff.mpr (fun j : J => heq j.val)] with w hw
    apply Prod.ext
    · rfl
    · funext j
      exact (hw j).symm
  · intro i j
    have hIj : MemLp (I j) 2 P := MemLp.ae_eq (heq j).symm (Lp.memLp _)
    have hmean : (∫ w,I j w ∂P)=0 := (integral_congr_ae (heq j)).trans (hm _)
    rw [covariance_eq_sub (Lp.memLp _) hIj,hm,hmean,mul_zero,sub_zero]
    have hh := W.inner_map_map (u i) (v j)
    rw [L2.inner_def,huv] at hh
    have hprod : (fun w => W (u i) w*I j w) =ᵐ[P]
        (fun w => W (u i) w*W (v j) w) := by
      filter_upwards [heq j] with w hw
      rw [hw]
    change (∫ w,W (u i) w*I j w ∂P)=0
    rw [integral_congr_ae hprod]
    simpa only [real_inner_comm,Real.inner_apply,Pi.mul_apply] using hh

end Asakura.Chapter12
