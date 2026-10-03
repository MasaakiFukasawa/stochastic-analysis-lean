import Chapter8LinearPathContinuity

open Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Continuity of the constructed first derivative in forcing parameters.
The deterministic forcing derivative may vary with time. -/
theorem forcing_variation_parameter_continuous {E F P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P]
    (T : ℝ) (hT : 0≤T) (L : ℝ) (hL : 0<L)
    (D : E → E →L[ℝ] E) (hcD : Continuous D) (hDb : ∀ z,‖D z‖≤L)
    (X : P → C(Icc (0:ℝ) T,E)) (J : P → C(Icc (0:ℝ) T,F →L[ℝ] E))
    (R : C(Icc (0:ℝ) T,F →L[ℝ] E)) (hcX : Continuous X)
    (hJ : ∀ p t,J p t=R t+∫ s in 0..t.val,
      (D (X p (projIcc 0 T hT s))).comp (J p (projIcc 0 T hT s))) :
    Continuous J := by
  let A : P → C(Icc (0:ℝ) T,(F →L[ℝ] E) →L[ℝ] (F →L[ℝ] E)) := fun p =>
    ⟨fun t => ContinuousLinearMap.compL ℝ F E E (D (X p t)),
      (ContinuousLinearMap.compL ℝ F E E).continuous.comp (hcD.comp (X p).continuous)⟩
  let Q : P → C(Icc (0:ℝ) T,F →L[ℝ] E) := fun p =>
    ⟨fun t => (D (X p t)).comp (R t),(hcD.comp (X p).continuous).clm_comp R.continuous⟩
  let G := fun p => J p-R
  have hXev : Continuous (fun q : P × Icc (0:ℝ) T => X q.1 q.2) :=
    continuous_eval.comp ((hcX.comp continuous_fst).prodMk continuous_snd)
  have hAc : Continuous A := ContinuousMap.continuous_of_continuous_uncurry A
    ((ContinuousLinearMap.compL ℝ F E E).continuous.comp (hcD.comp hXev))
  have hQc : Continuous Q := ContinuousMap.continuous_of_continuous_uncurry Q
    ((hcD.comp hXev).clm_comp (R.continuous.comp continuous_snd))
  have hGc : Continuous G := by
    apply Asakura.Chapter8.linear_solution_parameter_continuous T hT L hL A Q G hAc hQc
    · intro p
      apply (ContinuousMap.norm_le _ hL.le).mpr
      intro t
      change ‖A p t‖≤L
      apply ContinuousLinearMap.opNorm_le_bound _ hL.le
      intro V
      change ‖(D (X p t)).comp V‖≤L*‖V‖
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hDb _) (norm_nonneg _))
    · intro p t
      change J p t-R t=∫ s in 0..t.val,
        (D (X p (projIcc 0 T hT s))).comp (J p (projIcc 0 T hT s)-R (projIcc 0 T hT s))+
          (D (X p (projIcc 0 T hT s))).comp (R (projIcc 0 T hT s))
      rw [hJ p t]
      simp only [add_sub_cancel_left]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [ContinuousLinearMap.comp_sub,sub_add_cancel]
  have hh := hGc.add (continuous_const (y := R))
  convert hh using 1
  funext p
  exact (sub_add_cancel (J p) R).symm

end Asakura.Chapter12
