import Chapter8AveragedHessian

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic Taylor error needed to justify differentiating the
additive-noise solution with respect to its initial value. -/
theorem drift_quadratic_taylor_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ x,HasFDerivAt b (D x) x)
    (K : ℝ≥0) (hK : LipschitzWith K D) (x y : E) :
    ‖b x-b y-D y (x-y)‖ ≤ (K:ℝ)*‖x-y‖^2 := by
  have hc : Continuous (fun s : ℝ => (D (y+s • (x-y))-D y) (x-y)) := by
    apply Continuous.clm_apply
    · exact (hK.continuous.comp (by fun_prop)).sub continuous_const
    · exact continuous_const
  have he : (∫ s in (0:ℝ)..1,(D (y+s • (x-y))-D y) (x-y))=b x-b y-D y (x-y) := by
    simp_rw [ContinuousLinearMap.sub_apply]
    rw [intervalIntegral.integral_sub
      (f := fun s => D (y+s • (x-y)) (x-y)) (g := fun _ => D y (x-y))
      (((hK.continuous.comp (by fun_prop : Continuous (fun s : ℝ => y+s • (x-y)))).clm_apply continuous_const).intervalIntegrable 0 1)
      intervalIntegrable_const,intervalIntegral.integral_const]
    have hh := averaged_hessian_gradient_difference b D hD hK.continuous x y
    rw [ContinuousLinearMap.intervalIntegral_apply (φ := fun s => D (y+s • (x-y)))
      ((hK.continuous.comp (by fun_prop : Continuous (fun s : ℝ => y+s • (x-y)))).intervalIntegrable 0 1)] at hh
    simpa using hh
  rw [← he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun s => (D (y+s • (x-y))-D y) (x-y)) (C := (K:ℝ)*‖x-y‖^2) (by
      intro s hs
      have hso : s∈Ioc (0:ℝ) 1 := by simpa using hs
      have hs' : s∈Icc (0:ℝ) 1 := ⟨hso.1.le,hso.2⟩
      have hd := hK.norm_sub_le (y+s • (x-y)) y
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs'.1] at hd
      have hd' : ‖D (y+s • (x-y))-D y‖ ≤ (K:ℝ)*‖x-y‖ :=
        hd.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hs'.2) K.coe_nonneg)
      exact ((D (y+s • (x-y))-D y).le_opNorm (x-y)).trans
        (by simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_right hd' (norm_nonneg (x-y))))
  simpa using hh

end Asakura.Chapter8
