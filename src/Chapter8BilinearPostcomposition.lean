import Chapter8SecondVariationConstruction

noncomputable section
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

-- Pin the standard intermediate instances so synthesis of iterated
-- operator spaces does not have to rediscover them through nested maps.
local instance nestedOpNormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance nestedOpSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance nestedBiNormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance nestedBiSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

noncomputable def bilinearPostcomposition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E) : (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)
    (ContinuousLinearMap.compL ℝ E E E D)

 theorem bilinear_postcomposition_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E) (K : E →L[ℝ] E →L[ℝ] E) (h k : E) :
    bilinearPostcomposition D K h k=D (K h k) := rfl

theorem bilinear_postcomposition_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E) : ‖bilinearPostcomposition D‖ ≤ ‖D‖ := by
  have h1 : ‖ContinuousLinearMap.compL ℝ E E E D‖ ≤ ‖D‖ := by
    exact ((ContinuousLinearMap.compL ℝ E E E).le_opNorm D).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.norm_compL_le ℝ E E E) (norm_nonneg D)))
  have h2 := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)).le_opNorm
    (ContinuousLinearMap.compL ℝ E E E D)
  exact h2.trans ((mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.norm_compL_le ℝ E (E →L[ℝ] E) (E →L[ℝ] E))
    (norm_nonneg (ContinuousLinearMap.compL ℝ E E E D))).trans (by simpa only [one_mul] using h1))

theorem bilinear_postcomposition_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (bilinearPostcomposition (E := E)) :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)).continuous.comp
    (ContinuousLinearMap.compL ℝ E E E).continuous

end Asakura.Chapter8
