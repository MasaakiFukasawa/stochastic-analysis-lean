import Chapter12AdditiveDensityPositive
import Chapter12MatrixNoiseReduction
import Chapter12BrownianForcingProjection

open MeasureTheory Set Matrix
open scoped Topology NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem rectangular_density_positive {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (v:Fin d → (Fin n → ℝ)) (hσ: let σ:Matrix (Fin n) (Fin d) ℝ := fun i j => v j i; (σ*σ.transpose).PosDef)
    (x:Fin n → ℝ) (b:(Fin n → ℝ) → Fin n → ℝ) (K:ℝ≥0) (hb:LipschitzWith K b)
    (M:ℝ) (hM:0≤M) (hbg:∀y,‖WithLp.toLp 2 (b y)‖≤M*(1+‖WithLp.toLp 2 y‖))
    (T:ℝ) (hT:0<T)
    (S:C(Icc (0:ℝ) T,Fin n → ℝ) → C(Icc (0:ℝ) T,Fin n → ℝ)) (hSc:Continuous S)
    (hSeq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (p:(Fin n → ℝ) → ℝ) (hpc:Continuous p) (hpn:∀y,0≤p y)
    (hmap:P.map (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ _
      (brownianSystemCompactPath B T w)) ⟨T,hT.le,le_rfl⟩)=volume.withDensity (fun y => ENNReal.ofReal (p y))) :
    ∀y,0<p y := by
  obtain ⟨L,C,hLC⟩ := matrix_noise_reduction P B (fun i j => v j i) hσ
  have he:∀w,L.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T) (brownianSystemCompactPath C T w)=
      (columnOperator v).compLeftContinuous ℝ _ (brownianSystemCompactPath B T w) := by
    intro w
    ext t i
    have h := congrArg (fun z:Fin n → ℝ => z i) (hLC (realTimeClamp t.val) w)
    change L (fun j => C.W j (realTimeClamp t.val) w) i =
      columnOperator v (fun j => B.W j (realTimeClamp t.val) w) i
    simpa only [columnOperator_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Matrix.mulVec,dotProduct,mul_comm] using h
  apply additive_density_positive P C L x b K hb M hM hbg T hT S hSc hSeq p hpc hpn
  simpa only [he] using hmap
end Asakura.Chapter12
#print axioms Asakura.Chapter12.rectangular_density_positive
