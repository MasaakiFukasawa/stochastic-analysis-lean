import Chapter8CanonicalSmoothFlow

noncomputable section
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

local instance scalarOpNormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance scalarOpSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance scalarBiNormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance scalarBiSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

noncomputable def observableSecondDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Df : E →L[ℝ] ℝ) (D₂f : E →L[ℝ] E →L[ℝ] ℝ)
    (J : E →L[ℝ] E) (K : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E E ℝ Df).comp K+
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip J).comp (D₂f.comp J)

theorem observable_second_derivative_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Df : E →L[ℝ] ℝ) (D₂f : E →L[ℝ] E →L[ℝ] ℝ)
    (J : E →L[ℝ] E) (K : E →L[ℝ] E →L[ℝ] E) (h k : E) :
    observableSecondDerivative Df D₂f J K h k=Df (K h k)+D₂f (J h) (J k) := rfl

theorem observable_second_derivative_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Df : E →L[ℝ] ℝ) (D₂f : E →L[ℝ] E →L[ℝ] ℝ)
    (J : E →L[ℝ] E) (K : E →L[ℝ] E →L[ℝ] E) :
    ‖observableSecondDerivative Df D₂f J K‖ ≤ ‖Df‖*‖K‖+‖D₂f‖*‖J‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro k
  rw [observable_second_derivative_apply]
  have hK : ‖K h k‖ ≤ ‖K‖*‖h‖*‖k‖ :=
    ((K h).le_opNorm k).trans (mul_le_mul_of_nonneg_right (K.le_opNorm h) (norm_nonneg k))
  have h1 : ‖Df (K h k)‖ ≤ ‖Df‖*(‖K‖*‖h‖*‖k‖) :=
    (Df.le_opNorm _).trans (mul_le_mul_of_nonneg_left hK (norm_nonneg Df))
  have h2 : ‖D₂f (J h) (J k)‖ ≤ ‖D₂f‖*(‖J‖*‖h‖)*(‖J‖*‖k‖) := by
    have hh := ((D₂f (J h)).le_opNorm (J k)).trans
      (mul_le_mul_of_nonneg_right (D₂f.le_opNorm (J h)) (norm_nonneg (J k)))
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left (J.le_opNorm h) (norm_nonneg D₂f))
      (J.le_opNorm k) (norm_nonneg (J k)) (by positivity))
  have hh := (norm_add_le _ _).trans (add_le_add h1 h2)
  convert hh using 1 <;> ring

theorem observable_composition_derivatives {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E → E) (J : E → E →L[ℝ] E) (x : E) (K : E →L[ℝ] E →L[ℝ] E)
    (hX : HasFDerivAt X (J x) x) (hJ : HasFDerivAt J K x)
    (f : E → ℝ) (Df : E → E →L[ℝ] ℝ) (D₂f : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : HasFDerivAt f (Df (X x)) (X x)) (hDf : HasFDerivAt Df D₂f (X x)) :
    HasFDerivAt (fun z => f (X z)) ((Df (X x)).comp (J x)) x ∧
      HasFDerivAt (fun z => (Df (X z)).comp (J z))
        (observableSecondDerivative (Df (X x)) D₂f (J x) K) x :=
  ⟨hf.comp x hX,(hDf.comp x hX).clm_comp hJ⟩

end Asakura.Chapter8
