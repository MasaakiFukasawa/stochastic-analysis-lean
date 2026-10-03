import Chapter12ConcreteCylinderOperator
import Chapter12TensorCylinderOperator

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology TensorProduct RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def tensorRightEmbedding {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) :
    H →L[ℝ] CompletedHilbertTensor H E :=
  (UniformSpace.Completion.toComplL : (H ⊗[ℝ] E) →L[ℝ] CompletedHilbertTensor H E).comp
    ((TensorProduct.mkL ℝ H E).flip e)

@[simp] theorem tensorRightEmbedding_apply {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) (h : H) :
    tensorRightEmbedding e h=hilbertPureTensor h e := rfl

variable {Ω H E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

noncomputable def vectorCylinderValue (c : SmoothCylinder H) (e : E)
    (p : ℝ≥0∞) (hp : p≠⊤) : Lp E p P :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLp (c.valueLp P W S hS hcore p hp)

noncomputable def vectorCylinderDerivative (c : SmoothCylinder H) (e : E)
    (p : ℝ≥0∞) (hp : p≠⊤) : Lp (CompletedHilbertTensor H E) p P :=
  (tensorRightEmbedding e).compLp (c.gradientLp P W S hS hcore p hp)

theorem vector_cylinder_ibp (c d : SmoothCylinder H) (v e : E) (h : H)
    (p q : ℝ≥0∞) (hp : p≠⊤) (hq : q≠⊤) :
    (∫ w,inner ℝ (hilbertPureTensor h e) (vectorCylinderDerivative P W S hS hcore c v p hp w)*
      d.valueLp P W S hS hcore q hq w ∂P)=
    ∫ w,inner ℝ e (vectorCylinderValue P W S hS hcore c v p hp w)*
      d.ibpTestLp P W S hS hcore h q hq w ∂P := by
  let F := c.valueLp P W S hS hcore p hp
  let U := c.gradientLp P W S hS hcore p hp
  let G := d.valueLp P W S hS hcore q hq
  let Z := d.ibpTestLp P W S hS hcore h q hq
  have hd := (tensorRightEmbedding v).coeFn_compLp U
  have hv := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).coeFn_compLp F
  calc
    _=(∫ w,inner ℝ h (U w)*G w ∂P)*inner ℝ e v := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hd] with w hw
      change inner ℝ (hilbertPureTensor h e) ((tensorRightEmbedding v).compLp U w)*G w=_
      rw [hw,tensorRightEmbedding_apply,hilbert_pure_inner]
      ring
    _=(∫ w,F w*Z w ∂P)*inner ℝ e v := by
      rw [c.Lp_ibp P W S hS hcore d h p q hp hq]
    _=_ := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hv] with w hw
      change (F w*Z w)*inner ℝ e v=inner ℝ e (((ContinuousLinearMap.id ℝ ℝ).smulRight v).compLp F w)*Z w
      rw [hw]
      simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,inner_smul_right]
      ring

end Asakura.Chapter12
