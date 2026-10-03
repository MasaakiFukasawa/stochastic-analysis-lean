import Chapter12GaussianPathTensorBounds

open MeasureTheory
open scoped ContDiff ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_path_tensor_memLp {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) (P : Measure Ω) [IsFiniteMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) {N : ℕ} {K : Type*}
    [TopologicalSpace K] [CompactSpace K] (e : Fin N → H) (he : Orthonormal ℝ e)
    (X : (Fin N → ℝ) → C(K,ℝ)) (hX : ContDiff ℝ ∞ X) (k : ℕ)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀z t,Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖(iteratedFDeriv ℝ (k+1) X z (fun i => Pi.single (a i) 1)) t‖^2)≤C)
    (p : ℝ≥0∞) :
    MemLp (fun w => gaussianPathTensor H e X k (fun i => W (e i) w)) p P := by
  have hz : Measurable (fun w i => W (e i) w) := Measurable.of_eval
    (fun i => (Lp.stronglyMeasurable (W (e i))).measurable)
  have hm : AEStronglyMeasurable (fun w => gaussianPathTensor H e X k (fun i => W (e i) w)) P := (gaussianPathTensor_continuous H e X hX k).comp_aestronglyMeasurable hz.aestronglyMeasurable
  exact MemLp.of_bound hm C (ae_of_all _ (fun w => gaussianPathTensor_norm_le H e he X k _ C hC (hb _)))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_path_tensor_memLp
