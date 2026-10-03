import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def continuousMapApply {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    C(K,E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E →L[ℝ] F) →ₗ[ℝ] C(K,E) →ₗ[ℝ] C(K,F) :=
    { toFun := fun A =>
        { toFun := fun h => ⟨fun t => A t (h t),A.continuous.clm_apply h.continuous⟩
          map_add' := by intro h g;ext t;exact map_add (A t) _ _
          map_smul' := by intro a h;ext t;exact map_smul (A t) a _ }
      map_add' := by intro A B;ext h t;rfl
      map_smul' := by intro a A;ext h t;rfl }
  refine LinearMap.mkContinuous₂ (𝕜:=ℝ) (𝕜₂:=ℝ) (𝕜₃:=ℝ) (σ₁₃:=RingHom.id ℝ) (σ₂₃:=RingHom.id ℝ) (E:=C(K,E →L[ℝ] F)) (F:=C(K,E)) (G:=C(K,F)) L 1 ?_
  intro A h
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖A t (h t)‖≤1*‖A‖*‖h‖
  simpa only [one_mul] using ((A t).le_opNorm _).trans
    (mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

@[simp] theorem continuousMapApply_apply {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : C(K,E →L[ℝ] F)) (h : C(K,E)) (t : K) : continuousMapApply A h t=A t (h t) := rfl

noncomputable def continuousMapSuperposition {K E F : Type*} [TopologicalSpace K]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (f : E → F) (hf : Continuous f) : C(K,E) → C(K,F) :=
  fun u => ⟨fun t => f (u t),hf.comp u.continuous⟩

@[simp] theorem continuousMapSuperposition_apply {K E F : Type*} [TopologicalSpace K]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (f : E → F) (hf : Continuous f)
    (u : C(K,E)) (t : K) : continuousMapSuperposition f hf u t=f (u t) := rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.continuousMapApply
