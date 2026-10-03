import Chapter10KalmanAugmentedAlgebra
import Chapter10InnovationFiniteCovariance

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Transform the actual original state/filter/innovation SDE into the
error/innovation SDE used for Gaussian orthogonality. The transformed noises
are the actual weighted Ito integrals, with no assumed covariance identities. -/
theorem kalman_actual_augmented_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d q r : ℕ} (B : BrownianSystem P (q+r))
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (K : ℝ → Matrix (Fin d) (Fin r) ℝ)
    (C : ℝ → Matrix (Fin r) (Fin d) ℝ) (G : ℝ → Matrix (Fin d) (Fin q) ℝ)
    (D J : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hA : Continuous A) (hK : Continuous K) (hC : Continuous C) (hJ : Continuous J)
    (ξ : Ω → Fin ((d+d)+r) → ℝ) (T : ℝ) (hT : 0≤T)
    (N : Fin ((d+d)+r) → Fin (q+r) → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin ((d+d)+r) → ℝ)) :
    let Q := finiteBlocks (differenceMatrix d) (0 : Matrix (Fin d) (Fin r) ℝ)
      (0 : Matrix (Fin r) (Fin (d+d)) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
    let U := fun s => finiteBlocks (finiteBlocks (A s) 0 (K s*C s) (A s-K s*C s))
      (0 : Matrix (Fin (d+d)) (Fin r) ℝ) ((J s*C s)*differenceMatrix d) (0 : Matrix (Fin r) (Fin r) ℝ)
    let E := fun s => finiteBlocks (stackRows (G s) (0 : Matrix (Fin d) (Fin q) ℝ))
      (stackRows (0 : Matrix (Fin d) (Fin r) ℝ) (K s*D s))
      (0 : Matrix (Fin r) (Fin q) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ)
    LinearStateWitness P B (fun s => matrixOperatorMap (U s)) (fun i j s => E s i j) ξ T hT N X →
    let L := ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (rectangularMatrixMap Q)
    LinearStateWitness P B
      (fun s => matrixOperatorMap (finiteBlocks (A s-K s*C s) (0 : Matrix (Fin d) (Fin r) ℝ)
        (J s*C s) (0 : Matrix (Fin r) (Fin r) ℝ)))
      (fun i j s => finiteBlocks (G s) (-(K s*D s)) (0 : Matrix (Fin r) (Fin q) ℝ)
        (1 : Matrix (Fin r) (Fin r) ℝ) i j)
      (fun w => Q*ᵥξ w) T hT (fun i j t w => ∑ k,Q i k*N k j t w) (fun w => L (X w)) := by
  intro Q U E h L
  have hUc : Continuous U := finiteBlocks_continuous _ _ _ _
    (finiteBlocks_continuous A _ _ _ hA continuous_const (hK.matrix_mul hC)
      (hA.sub (hK.matrix_mul hC))) continuous_const
    ((hJ.matrix_mul hC).matrix_mul continuous_const) continuous_const
  have hh := h.matrix_map P B (fun s => matrixOperatorMap (U s))
    (matrixOperatorMap.continuous.comp hUc)
    (fun s => matrixOperatorMap (finiteBlocks (A s-K s*C s) (0 : Matrix (Fin d) (Fin r) ℝ)
      (J s*C s) (0 : Matrix (Fin r) (Fin r) ℝ))) Q
    (by
      intro s x
      rw [matrixOperatorMap_apply,matrixOperatorMap_apply,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
      exact congrArg (fun M => M*ᵥx) (kalman_augmented_drift_transformation (A s) (K s) (C s) (J s)))
    (fun i j s => E s i j) ξ T hT N X
  have he i j s : (∑ k,Q i k*E s k j)=
      finiteBlocks (G s) (-(K s*D s)) (0 : Matrix (Fin r) (Fin q) ℝ)
        (1 : Matrix (Fin r) (Fin r) ℝ) i j :=
    congrArg (fun M : Matrix (Fin (d+r)) (Fin (q+r)) ℝ => M i j)
      (kalman_augmented_noise_transformation (G s) (K s) (D s))
  simpa only [he] using hh

end Asakura.Chapter10
