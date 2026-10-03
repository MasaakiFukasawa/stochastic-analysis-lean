import Chapter10LinearStateWitness
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinateProjection {d D : ℕ} (κ : Fin d → Fin D) :
    (Fin D → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x i => x (κ i)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

lemma coordinateProjection_norm_le {d D : ℕ} (κ : Fin d → Fin D) (x : Fin D → ℝ) :
    ‖coordinateProjection κ x‖≤‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x (κ i)

/-- A group of coordinates with a closed drift equation inherits the actual
state witness, including its driving integrals and path moment. -/
theorem LinearStateWitness.project {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d D n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin D → ℝ) →L[ℝ] (Fin D → ℝ))
    (F : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (κ : Fin d → Fin D)
    (hclosed : ∀ s x i,(A s x) (κ i)=F s (coordinateProjection κ x) i)
    (G : Fin D → Fin n → ℝ → ℝ) (ξ : Ω → Fin D → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin D → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin D → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) :
    let L := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (coordinateProjection κ)
    LinearStateWitness P B F (fun i => G (κ i)) (fun w => coordinateProjection κ (ξ w)) T hT
      (fun i => N (κ i)) (fun w => L (X w)) := by
  let L := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (coordinateProjection κ)
  have hm : Measurable (fun w => L (X w)) := L.continuous.measurable.comp h.measurable
  have hLp : MemLp (fun w => L (X w)) 2 P := by
    apply h.moment.norm.of_le hm.aestronglyMeasurable
    apply ae_of_all
    intro w
    simp only [norm_norm]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    exact (coordinateProjection_norm_le κ (X w t)).trans ((X w).norm_coe_le_norm t)
  refine ⟨fun i j => h.noise (κ i) j,fun i j => h.ito (κ i) j,hm,hLp,?_⟩
  intro i
  have hh := h.decomposition (κ i)
  have he : (fun (t : HalfClosedTime) w => coordinateProjection κ (ξ w) i+
      ∫ s in 0..(finitePrefixTime T hT t).val,F s (L (X w) (projIcc 0 T hT s)) i)=
      (fun t w => ξ w (κ i)+∫ s in 0..(finitePrefixTime T hT t).val,(A s (X w (projIcc 0 T hT s))) (κ i)) := by
    funext t w
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    exact (hclosed s _ i).symm
  change SemimartingaleDecomposition P B.F
    (fun t w => X w (finitePrefixTime T hT t) (κ i))
    (fun t w => coordinateProjection κ (ξ w) i+∫ s in 0..(finitePrefixTime T hT t).val,F s (L (X w) (projIcc 0 T hT s)) i)
    (fun t w => ∑ j,N (κ i) j (min (realTimeClamp T) t) w)
  rw [he]
  exact hh

end Asakura.Chapter10
