import Chapter12GaussianClosedDerivativeBound
import Chapter12PathRemainderContinuity

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianPathTensor (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K]
    (e : Fin N → H) (X : (Fin N → ℝ) → C(K,ℝ)) (k : ℕ) (z : Fin N → ℝ) :
    C(K,positiveMalliavinTensorPower H k) :=
  ∑a : Fin (k+1) → Fin N,
    (ContinuousLinearMap.compLeftContinuous ℝ K
      ((1 : ℝ →L[ℝ] ℝ).smulRight (tensorCoordinateFrame H e k a)))
      (iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1))

theorem gaussianPathTensor_apply (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K]
    (e : Fin N → H) (X : (Fin N → ℝ) → C(K,ℝ)) (k : ℕ) (z : Fin N → ℝ) (t : K) :
    gaussianPathTensor H e X k z t=∑a : Fin (k+1) → Fin N,
      (iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1)) t • tensorCoordinateFrame H e k a := by
  simp [gaussianPathTensor]

theorem gaussianPathTensor_continuous (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K]
    (e : Fin N → H) (X : (Fin N → ℝ) → C(K,ℝ)) (hX : ContDiff ℝ ∞ X) (k : ℕ) :
    Continuous (gaussianPathTensor H e X k) := by
  unfold gaussianPathTensor
  apply continuous_finset_sum
  intro a _
  apply Continuous.comp (ContinuousLinearMap.continuous _) 
  have hd := hX.continuous_iteratedFDeriv (show ((k+1:ℕ):ℕ∞ω)≤∞ by simp)
  fun_prop

theorem gaussianPathTensor_difference_norm (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K]
    (e : Fin N → H) (he : Orthonormal ℝ e)
    (X Y : (Fin N → ℝ) → C(K,ℝ)) (k : ℕ) (z : Fin N → ℝ) (t : K) :
    ‖gaussianPathTensor H e X k z t-gaussianPathTensor H e Y k z t‖=
      Real.sqrt (∑a : Fin (k+1) → Fin N,
        ‖(iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1)) t-
          (iteratedFDeriv ℝ (k+1) Y z (fun i => Pi.single (a i) 1)) t‖^2) := by
  rw [gaussianPathTensor_apply,gaussianPathTensor_apply,←Finset.sum_sub_distrib]
  simp_rw [←sub_smul]
  rw [tensor_coordinate_sum_norm H e he k]
  simp only [Real.norm_eq_abs,sq_abs]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussianPathTensor_continuous
#print axioms Asakura.Chapter12.gaussianPathTensor_difference_norm
