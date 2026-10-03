import Chapter12GaussianPathTensor

open MeasureTheory Set
open scoped ContDiff ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem gaussianPathTensor_norm (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K] (e : Fin N → H) (he : Orthonormal ℝ e)
    (X : (Fin N → ℝ) → C(K,ℝ)) (k : ℕ) (z : Fin N → ℝ) (t : K) :
    ‖gaussianPathTensor H e X k z t‖=Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖(iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1)) t‖^2) := by
  rw [gaussianPathTensor_apply,tensor_coordinate_sum_norm H e he k]
  simp only [Real.norm_eq_abs,sq_abs]

theorem gaussianPathTensor_norm_le (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K] (e : Fin N → H) (he : Orthonormal ℝ e)
    (X : (Fin N → ℝ) → C(K,ℝ)) (k : ℕ) (z : Fin N → ℝ) (C : ℝ) (hC : 0≤C)
    (hb : ∀t,Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖(iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1)) t‖^2)≤C) :
    ‖gaussianPathTensor H e X k z‖≤C := by
  apply (ContinuousMap.norm_le _ hC).mpr
  intro t
  rw [gaussianPathTensor_norm H e he]
  exact hb t

theorem gaussianPathTensor_difference_le (H : RealHilbertSpaceData) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K] (e : Fin N → H) (he : Orthonormal ℝ e)
    (X Y : (Fin N → ℝ) → C(K,ℝ)) (k : ℕ) (z : Fin N → ℝ) (C : ℝ) (hC : 0≤C)
    (hb : ∀t,Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖(iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1)) t-
        (iteratedFDeriv ℝ (k+1) Y z (fun i => Pi.single (a i) 1)) t‖^2)≤C) :
    ‖gaussianPathTensor H e X k z-gaussianPathTensor H e Y k z‖≤C := by
  apply (ContinuousMap.norm_le _ hC).mpr
  intro t
  change ‖gaussianPathTensor H e X k z t-gaussianPathTensor H e Y k z t‖≤C
  rw [gaussianPathTensor_difference_norm H e he]
  exact hb t
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussianPathTensor_difference_le
