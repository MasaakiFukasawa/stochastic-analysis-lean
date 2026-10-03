import Mathlib.Topology.ContinuousMap.Compact

import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Set
open scoped BigOperators unitInterval
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Bernstein reconstruction is a deterministic continuous linear map of
finitely many path values. -/
noncomputable def bernsteinSynthesisGeneral (n : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (Fin (n+1) → E) →L[ℝ] C(unitInterval,E) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => ∑ k : Fin (n+1),bernstein n k • ContinuousMap.const _ (x k)
    map_add' := by
      intro x y
      ext t
      simp [Finset.sum_add_distrib,smul_add]
    map_smul' := by
      intro c x
      ext t
      simp [Finset.smul_sum,smul_smul,mul_comm] }

lemma bernsteinSynthesisGeneral_apply (n : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : C(unitInterval,E)) :
    bernsteinSynthesisGeneral n E (fun k => f (bernstein.z k))=bernsteinApproximation n f := rfl

/-- Bernstein reconstruction is a deterministic linear map of finitely many
path values. -/
noncomputable def bernsteinSynthesis (n d : ℕ) :
    (Fin (n+1) → Fin d → ℝ) →L[ℝ] C(unitInterval,Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => ∑ k : Fin (n+1),bernstein n k • ContinuousMap.const _ (x k)
    map_add' := by
      intro x y
      ext t i
      simp [Finset.sum_add_distrib,smul_add]
    map_smul' := by
      intro c x
      ext t i
      simp [Finset.mul_sum,mul_assoc,mul_left_comm] }

lemma bernsteinSynthesis_apply (n d : ℕ) (f : C(unitInterval,Fin d → ℝ)) :
    bernsteinSynthesis n d (fun k => f (bernstein.z k))=bernsteinApproximation n f := rfl

lemma bernstein_path_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : C(unitInterval,E)) : ‖bernsteinApproximation n f‖≤‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  rw [bernsteinApproximation.apply]
  calc
    _ ≤ ∑ k : Fin (n+1),‖bernstein n k t • f (bernstein.z k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin (n+1),bernstein n k t * ‖f‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg bernstein_nonneg]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) bernstein_nonneg
    _ = ‖f‖ := by rw [← Finset.sum_mul,bernstein.probability,one_mul]

end Asakura.Chapter10
