import Chapter10KalmanErrorTransformation
import Chapter10InnovationFiniteCovariance

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The state-minus-estimate error inherits the actual SDE witness, with
drift A-KC and Brownian coefficients (G,-KD), from the coupled original
state/filter equations. This checks the subtraction step in the written proof. -/
theorem kalman_actual_error_state {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (K : ℝ → Matrix (Fin d) (Fin r) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (D : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hK : Continuous K) (hC : Continuous C)
    (ξ : Ω → Fin (d+d) → ℝ) (T : ℝ) (hT : 0≤T)
    (N : Fin (d+d) → Fin (q+r) → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+d) → ℝ))
    (h : LinearStateWitness P B
      (fun s => matrixOperatorMap (finiteBlocks (A s) 0 (K s*C s) (A s-K s*C s)))
      (fun i j s => finiteBlocks (G s) (0 : Matrix (Fin d) (Fin r) ℝ)
        (0 : Matrix (Fin d) (Fin q) ℝ) (K s*D s) i j) ξ T hT N X) :
    let L := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (rectangularMatrixMap (differenceMatrix d))
    LinearStateWitness P B (fun s => matrixOperatorMap (A s-K s*C s))
      (fun i j s => errorNoise (G s) (K s) (D s) i j)
      (fun w => differenceMatrix d*ᵥξ w) T hT
      (fun i j t w => ∑ k,differenceMatrix d i k*N k j t w) (fun w => L (X w)) := by
  have hAc : Continuous (fun s => matrixOperatorMap (finiteBlocks (A s) 0 (K s*C s) (A s-K s*C s))) :=
    matrixOperatorMap.continuous.comp (finiteBlocks_continuous A _ _ _ hA continuous_const
      (hK.matrix_mul hC) (hA.sub (hK.matrix_mul hC)))
  have hh := h.matrix_map P B _ hAc (fun s => matrixOperatorMap (A s-K s*C s)) (differenceMatrix d)
    (by
      intro s x
      rw [matrixOperatorMap_apply]
      exact kalman_error_drift_transformation (A s) (K s) (C s) x)
    _ ξ T hT N X
  simpa only [kalman_error_noise_transformation] using hh

end Asakura.Chapter10
