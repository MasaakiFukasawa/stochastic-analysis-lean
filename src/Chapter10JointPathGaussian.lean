import Chapter10GaussianIntervalPath

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Joint Gaussianity of an initial vector and a continuous forcing path is
obtained from their finite-dimensional joint distributions. -/
theorem initial_path_joint_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (T : ℝ) (hT : 0≤T) (ξ : Ω → E) (hξ : MemLp ξ 2 P)
    (Z : Ω → C(Icc (0:ℝ) T,F)) (hZ : MemLp Z 2 P)
    (hg : ∀ n (τ : Fin (n+1) → Icc (0:ℝ) T),
      HasGaussianLaw (fun w k => (ξ w,Z w (τ k))) P) :
    HasGaussianLaw (fun w => (ξ w,Z w)) P := by
  let J₁ : E →L[ℝ] C(Icc (0:ℝ) T,E × F) :=
    (ContinuousLinearMap.const ℝ (Icc (0:ℝ) T)).comp (ContinuousLinearMap.inl ℝ E F)
  let J₂ : C(Icc (0:ℝ) T,F) →L[ℝ] C(Icc (0:ℝ) T,E × F) :=
    ContinuousLinearMap.compLeftContinuous ℝ _ (ContinuousLinearMap.inr ℝ E F)
  let W := fun w => J₁ (ξ w)+J₂ (Z w)
  have hWe w t : W w t=(ξ w,Z w t) := by
    simp [W,J₁,J₂]
  have hWm : AEStronglyMeasurable W P :=
    (J₁.continuous.comp_aestronglyMeasurable hξ.aestronglyMeasurable).add
      (J₂.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
  have hW : MemLp W 2 P := by
    apply (hξ.norm.add hZ.norm).of_le hWm
    apply ae_of_all
    intro w
    change ‖W w‖ ≤ ‖‖ξ w‖+‖Z w‖‖
    rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro t
    rw [hWe]
    rw [Prod.norm_def]
    exact max_le ((le_add_of_nonneg_right (norm_nonneg _)))
      (((Z w).norm_coe_le_norm t).trans (le_add_of_nonneg_left (norm_nonneg _)))
  have hWg : HasGaussianLaw W P := gaussian_interval_path P T hT W hW (by
    intro n τ
    simpa only [hWe] using hg n τ)
  let L₁ : C(Icc (0:ℝ) T,E × F) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E F).comp (ContinuousMap.evalCLM ℝ ⟨0,le_rfl,hT⟩)
  let L₂ : C(Icc (0:ℝ) T,E × F) →L[ℝ] C(Icc (0:ℝ) T,F) :=
    ContinuousLinearMap.compLeftContinuous ℝ _ (ContinuousLinearMap.snd ℝ E F)
  have hh := hWg.map (L₁.prod L₂)
  apply hh.congr
  apply ae_of_all
  intro w
  apply Prod.ext
  · change (W w ⟨0,le_rfl,hT⟩).1=ξ w
    rw [hWe]
  · ext t
    change (W w t).2=Z w t
    rw [hWe]

end Asakura.Chapter10
