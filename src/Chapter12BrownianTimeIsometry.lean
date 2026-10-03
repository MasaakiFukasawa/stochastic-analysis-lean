import Chapter12BrownianTimeInner

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def brownianTimeIsometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) :
    Lp (FiniteWienerHilbert d T) 2 P →ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (P.prod (compactTimeMeasure T hT))) := by
  let K : Lp (FiniteWienerHilbert d T) 2 P →L[ℝ]
      (Fin (d+1) → Lp ℝ 2 (P.prod (compactTimeMeasure T hT))) :=
    ContinuousLinearMap.pi (fun i => (timeRealizationIsometry P T hT).toContinuousLinearMap.comp
      ((brownianCoordinateProjection T i).compLpL 2 P))
  let J := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (d+1) => Lp ℝ 2 (P.prod (compactTimeMeasure T hT)))).symm.toContinuousLinearMap.comp K
  refine ⟨J.toLinearMap,?_⟩
  intro U
  have he : inner ℝ (J U) (J U)=inner ℝ U U := by
    rw [PiLp.inner_apply,brownian_time_inner P T hT U U]
    rfl
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

theorem brownianTimeIsometry_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T)
    (U : Lp (FiniteWienerHilbert d T) 2 P) (i : Fin (d+1)) :
    brownianTimeIsometry P T hT U i=brownianDerivativeTime P T hT U i := rfl

end Asakura.Chapter12
