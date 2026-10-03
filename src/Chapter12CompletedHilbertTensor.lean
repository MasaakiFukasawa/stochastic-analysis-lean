import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion

open UniformSpace Set
open scoped TensorProduct RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev CompletedHilbertTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] := Completion (E ⊗[ℝ] F)

noncomputable def hilbertPureTensor {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (e : E) (f : F) : CompletedHilbertTensor E F :=
  (e ⊗ₜ[ℝ] f : E ⊗[ℝ] F)

theorem hilbert_pure_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (e e' : E) (f f' : F) :
    inner ℝ (hilbertPureTensor e f) (hilbertPureTensor e' f')=inner ℝ e e'*inner ℝ f f' := by
  simp [hilbertPureTensor,Completion.inner_coe]

theorem hilbert_pure_norm {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (e : E) (f : F) :
    ‖hilbertPureTensor e f‖=‖e‖*‖f‖ := by
  simp [hilbertPureTensor,TensorProduct.norm_tmul]

/-- Testing against all elementary tensors separates points even after
Hilbert completion. This supplies uniqueness of tensor-valued derivatives. -/
theorem hilbert_pure_separate {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : CompletedHilbertTensor E F)
    (hu : ∀ e f,inner ℝ (hilbertPureTensor e f) u=0) : u=0 := by
  have ha (v : E ⊗[ℝ] F) : inner ℝ (v : CompletedHilbertTensor E F) u=0 := by
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [Completion.coe_zero,inner_zero_left]
    | tmul e f => exact hu e f
    | add a b ha hb => simpa only [Completion.coe_add,inner_add_left,ha,hb,add_zero]
  have hall : ∀ v : CompletedHilbertTensor E F,inner ℝ v u=0 := by
    apply isClosed_property (Completion.denseRange_coe (α := E ⊗[ℝ] F))
      (isClosed_eq (by fun_prop) continuous_const)
    exact ha
  exact inner_self_eq_zero.mp (hall u)

end Asakura.Chapter12
