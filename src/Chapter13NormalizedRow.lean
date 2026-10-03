import Chapter13UnitNoiseBrownian
import Chapter13NoiseAlgebra

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2000000

lemma normalized_coordinate_bound {d:ℕ} (x:EuclideanSpace ℝ (Fin d)) (i:Fin d) :
    |x i/‖x‖|≤1 := by
  by_cases hx:x=0
  · simp [hx]
  · rw [abs_div,abs_of_nonneg (norm_nonneg _)]
    exact (div_le_one (norm_pos_iff.mpr hx)).mpr (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)

lemma normalized_coordinate_unit {d:ℕ} (x:EuclideanSpace ℝ (Fin d)) (hx:x≠0) :
    ∑i,(x i/‖x‖)^2=1 := by
  simp_rw [div_pow]
  rw [←Finset.sum_div,←EuclideanSpace.real_norm_sq_eq,div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))]

theorem normalized_row_data {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (σ:Ω × ℝ → EuclideanSpace ℝ (Fin d)) (hσ:Measurable σ)
    (hσp:∀b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => σ (z.1,z.2.val)))
    (hn:∀ᵐw∂P,∀ᵐr∂volume,0≤r → σ (w,r)≠0) :
    let H:=fun i z => σ z i/‖σ z‖
    (∀i,Measurable (H i)) ∧
    (∀i b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => H i (z.1,z.2.val))) ∧
    (∀i z,|H i z|≤1) ∧
    (∀ᵐw∂P,∀ᵐr∂volume,0≤r → ∑i,(H i (w,r))^2=1) := by
  intro H
  have hm i:Measurable (fun x:EuclideanSpace ℝ (Fin d) => x i) := (PiLp.continuous_apply 2 _ i).measurable
  refine ⟨fun i => (hm i |>.comp hσ).div hσ.norm,?_,fun i z => normalized_coordinate_bound (σ z) i,?_⟩
  · intro i b hb
    letI:MeasurableSpace (Ω × Icc (0:ℝ) b):=progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))
    exact ((hm i).comp (hσp b hb)).div (hσp b hb).norm
  · filter_upwards [hn] with w hw
    filter_upwards [hw] with r hr
    intro hr0
    exact normalized_coordinate_unit (σ (w,r)) (hr hr0)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.normalized_coordinate_bound
#print axioms Asakura.Chapter13.normalized_coordinate_unit
#print axioms Asakura.Chapter13.normalized_row_data
