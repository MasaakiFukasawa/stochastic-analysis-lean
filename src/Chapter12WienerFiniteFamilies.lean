import Chapter12WienerCoordinates
import Chapter10GaussianHistory

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem wiener_fintype_joint_gaussian {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (v : ι → H) : HasGaussianLaw (fun w i => W (v i) w) P := by
  classical
  let e := Fintype.equivFin ι
  let L : (Fin (Fintype.card ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))
  have hg := (wiener_joint_gaussian P W hlaw (fun j => v (e.symm j))).map L
  convert hg using 1
  funext w i
  change W (v i) w=W (v (e.symm (e i))) w
  rw [Equiv.symm_apply_apply]

theorem wiener_pair_finite_gaussian {Ω H ι κ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (u : ι → H) (v : κ → H) :
    HasGaussianLaw (fun w => ((fun i => W (u i) w),(fun j => W (v j) w))) P := by
  let L : (ι ⊕ κ → ℝ) →L[ℝ] ((ι → ℝ) × (κ → ℝ)) :=
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inl i))).prod
      (ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (Sum.inr j)))
  exact (wiener_fintype_joint_gaussian P W hlaw (Sum.elim u v)).map L

/-- Orthogonality of deterministic directions gives independence from the
whole past coordinate family, not only from an individual past variable. -/
theorem wiener_orthogonal_history_independent {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (n : ℕ) (u : Fin n → H) (v : ι → H)
    (huv : ∀ i j,inner ℝ (u i) (v j)=0) :
    IndepFun (fun w i => W (u i) w) (fun w j => W (v j) w) P := by
  classical
  have hm (h : H) : (∫ w,W h w ∂P)=0 := by
    simpa only [integral_id_gaussianReal] using (hlaw h).integral_eq
  apply Asakura.Chapter10.gaussian_error_independent_history P _ _
    (Measurable.of_eval (fun i => (Lp.stronglyMeasurable (W (u i))).measurable))
    (fun j => (Lp.stronglyMeasurable (W (v j))).measurable)
    (fun J => wiener_pair_finite_gaussian P W hlaw u (fun j : J => v j.val))
  intro i j
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),hm,hm,mul_zero,sub_zero]
  have hh := W.inner_map_map (u i) (v j)
  rw [L2.inner_def,huv] at hh
  simpa only [real_inner_comm,Real.inner_apply,Pi.mul_apply] using hh

end Asakura.Chapter12
