import Chapter10FiniteBlockProjection
import Chapter10ContinuousPastOrthogonality
import Chapter10StateCoordinate

open MeasureTheory Set Matrix
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The same-time error/innovation orthogonality propagates to every earlier
innovation time, through the closed error equation. -/
theorem innovation_past_orthogonality {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (F : ℝ → Matrix (Fin d) (Fin d) ℝ) (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (E : Fin (d+r) → Fin n → ℝ → ℝ) (hE : ∀ i j,Continuous (E i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (h : LinearStateWitness P B
      (fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))) E ξ T hT N X)
    (hzero : ∀ s : Icc (0:ℝ) T,∀ i j,(∫ w,X w s (headIndex i)*X w s (tailIndex j) ∂P)=0) :
    ∀ s t : Icc (0:ℝ) T,s.val≤t.val → ∀ i j,
      (∫ w,X w t (headIndex i)*X w s (tailIndex j) ∂P)=0 := by
  let A := fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))
  let F₀ := fun t => matrixOperatorMap (F t)
  let κ := headIndex (d := d) (r := r)
  let Q := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (coordinateProjection κ)
  let Y := fun w => Q (X w)
  let ξ₀ := fun w => coordinateProjection κ (ξ w)
  have hp : LinearStateWitness P B F₀ (fun i => E (κ i)) ξ₀ T hT (fun i => N (κ i)) Y :=
    h.project P B A F₀ κ (fun s x i => finiteBlocks_head_action (F s) (L s) x i) E ξ T hT N X
  have hξ₀ : MemLp ξ₀ 2 P := by
    apply hξ.norm.of_le ((coordinateProjection κ).continuous.comp_aestronglyMeasurable hξ.aestronglyMeasurable)
    exact ae_of_all _ fun w => by simpa only [norm_norm] using coordinateProjection_norm_le κ (ξ w)
  intro s t hst i j
  let η := fun w => X w s (tailIndex j)
  have hηm := h.coordinate_adapted P B A E ξ T hT N X s (tailIndex j)
  have hη := h.coordinate_memLp P B A E ξ T hT N X s (tailIndex j)
  have hh := hp.continuous_past_orthogonality P B F₀ (matrixOperatorMap.continuous.comp hF)
    (fun i => E (κ i)) (fun i j => hE (κ i) j) ξ₀ hξ₀ T hT (fun i => N (κ i)) Y s η hηm hη
    (by
      intro k
      change (∫ w,X w s (tailIndex j)*X w s (headIndex k) ∂P)=0
      simpa only [mul_comm] using hzero s k j) t hst i
  change (∫ w,X w s (tailIndex j)*X w t (headIndex i) ∂P)=0 at hh
  simpa only [mul_comm] using hh

end Asakura.Chapter10
