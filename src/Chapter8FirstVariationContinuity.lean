import Chapter8LinearPathContinuity
import Chapter8VariationalConstruction

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Joint continuity of the first variation in any parameter on which
the solution path depends continuously, including the forcing path. -/
theorem first_variation_parameter_continuous {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace P]
    (T : ℝ) (hT : 0 ≤ T) (L : ℝ) (hL : 0<L)
    (D : E → E →L[ℝ] E) (hcD : Continuous D) (hDb : ∀ z,‖D z‖ ≤ L)
    (X : P → C(Icc (0:ℝ) T,E)) (J : P → C(Icc (0:ℝ) T,E →L[ℝ] E))
    (hcX : Continuous X)
    (hJ : ∀ p t,J p t=1+∫ s in 0..t.val,D (X p (projIcc 0 T hT s))*J p (projIcc 0 T hT s)) :
    Continuous J := by
  let A : P → C(Icc (0:ℝ) T,(E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) :=
    fun p => ⟨fun t => ContinuousLinearMap.compL ℝ E E E (D (X p t)),
      (ContinuousLinearMap.compL ℝ E E E).continuous.comp (hcD.comp (X p).continuous)⟩
  let R : P → C(Icc (0:ℝ) T,E →L[ℝ] E) := fun p =>
    ⟨fun t => D (X p t),hcD.comp (X p).continuous⟩
  let G := fun p => J p-ContinuousMap.const (Icc (0:ℝ) T) (1 : E →L[ℝ] E)
  have hXev : Continuous (fun q : P × Icc (0:ℝ) T => X q.1 q.2) :=
    continuous_eval.comp ((hcX.comp continuous_fst).prodMk continuous_snd)
  have hAc : Continuous A := ContinuousMap.continuous_of_continuous_uncurry A
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp (hcD.comp hXev))
  have hRc : Continuous R := ContinuousMap.continuous_of_continuous_uncurry R (hcD.comp hXev)
  have hGc : Continuous G := by
    apply linear_solution_parameter_continuous T hT L hL A R G hAc hRc
    · intro p
      apply (ContinuousMap.norm_le _ hL.le).mpr
      intro t
      have hh := (ContinuousLinearMap.compL ℝ E E E).le_opNorm (D (X p t))
      exact hh.trans ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ E E E)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hDb (X p t)))
    · intro p t
      change J p t-1=∫ s in 0..t.val,D (X p (projIcc 0 T hT s))*(J p (projIcc 0 T hT s)-1)+D (X p (projIcc 0 T hT s))
      rw [hJ p t]
      simp only [add_sub_cancel_left]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [mul_sub,mul_one,sub_add_cancel]
  have hh := hGc.add (continuous_const (y := ContinuousMap.const (Icc (0:ℝ) T) (1 : E →L[ℝ] E)))
  convert hh using 1
  funext p
  exact (sub_add_cancel (J p) _).symm

end Asakura.Chapter8
