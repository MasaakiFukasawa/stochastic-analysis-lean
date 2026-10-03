import Chapter8LinearClock

open MeasureTheory Set
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7

/-- Deterministic multiplication scales quadratic variation by its square. -/
theorem covariance_scalar_rescaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (M C : HalfClosedTime → Ω → ℝ)
    (hC : LocalCovarianceWitness P F M M C) (c : ℝ) :
    LocalCovarianceWitness P F (fun t ω => c*M t ω) (fun t ω => c*M t ω)
      (fun t ω => c^2*C t ω) := by
  refine ⟨?_,hC.variation.smul F (c^2)⟩
  have hh := hC.defect.smul P F (c^2)
  convert hh using 1
  funext t ω
  ring

/-- The long-time normalized process and its bracket are actual local
martingale/covariance witnesses for the rescaled filtration. -/
theorem long_time_martingale_rescaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (M C : HalfClosedTime → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hC : LocalCovarianceWitness P F M M C)
    (T c : ℝ) (hT : 0 < T) (hc : 0 < c) :
    let G := fun t => F (linearClock T hT t)
    let N := fun t ω => M (linearClock T hT t) ω / Real.sqrt (T*c)
    let D := fun t ω => C (linearClock T hT t) ω / (T*c)
    LocalMProcessWitness P G N ∧ LocalCovarianceWitness P G N N D := by
  dsimp only
  have hMt := order_time_change_local P F (linearClock T hT) (linear_clock_continuous T hT) M hM
  have hCt := order_time_change_covariance P F (linearClock T hT) (linear_clock_continuous T hT) M M C hC
  have he : (Real.sqrt (T*c))⁻¹^2 = (T*c)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (mul_pos hT hc).le]
  constructor
  · have hh := hMt.smul P (fun t => F (linearClock T hT t)) ((Real.sqrt (T*c))⁻¹)
    convert hh using 1
    funext t ω
    simp [div_eq_mul_inv,mul_comm]
  · have hh := covariance_scalar_rescaling P (fun t => F (linearClock T hT t))
      (fun t => M (linearClock T hT t)) (fun t => C (linearClock T hT t)) hCt ((Real.sqrt (T*c))⁻¹)
    rw [he] at hh
    convert hh using 1 <;> funext t ω <;> simp [div_eq_mul_inv,mul_comm]

end Asakura.Chapter8
