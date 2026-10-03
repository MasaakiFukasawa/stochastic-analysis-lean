import Chapter12CoordinateForcing
import Chapter12ColumnEllipticity

open MeasureTheory Set
open scoped Topology NNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem elliptic_density_positive {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (v:Fin d → EuclideanSpace ℝ (Fin n)) (ell:ℝ) (hell:0<ell)
    (hv:∀z:EuclideanSpace ℝ (Fin n),ell*‖z‖^2≤∑j,(inner ℝ z (v j))^2)
    (x:EuclideanSpace ℝ (Fin n)) (b:EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (K:ℝ≥0) (hb:LipschitzWith K b) (T:ℝ) (hT:0<T)
    (S:C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin n)) → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin n)))
    (hSc:Continuous S) (hSeq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (p:EuclideanSpace ℝ (Fin n) → ℝ) (hpc:Continuous p) (hpn:∀y,0≤p y)
    (hmap:P.map (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ _
      (brownianSystemCompactPath B T w)) ⟨T,hT.le,le_rfl⟩)=volume.withDensity (fun y => ENNReal.ofReal (p y))) :
    ∀y,0<p y := by
  let e:(Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin n => ℝ)).symm
  let b' := fun y => e.symm (b (e y))
  let S' := coordinateForcing e T S
  let v' := fun j => e.symm (v j)
  let K' := ‖e.symm.toContinuousLinearMap‖₊*(K*‖e.toContinuousLinearMap‖₊)
  have hb':LipschitzWith K' b' := e.symm.toContinuousLinearMap.lipschitzWith.comp (hb.comp e.toContinuousLinearMap.lipschitzWith)
  let M := ‖b 0‖+(K:ℝ)
  have hM:0≤M := add_nonneg (norm_nonneg _) K.coe_nonneg
  have hbg:∀y,‖WithLp.toLp 2 (b' y)‖≤M*(1+‖WithLp.toLp 2 y‖) := by
    intro y
    change ‖b (e y)‖≤M*(1+‖e y‖)
    have hh := hb.norm_sub_le (e y) 0
    simp only [sub_zero] at hh
    have hn : ‖b (e y)‖≤‖b (e y)-b 0‖+‖b 0‖ := by simpa only [norm_sub_rev,add_comm] using norm_le_insert (b 0) (b (e y))
    dsimp [M]
    nlinarith [K.coe_nonneg,mul_nonneg K.coe_nonneg (norm_nonneg (e y)),mul_nonneg (norm_nonneg (b 0)) (norm_nonneg (e y))]
  let X := fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ _
    (brownianSystemCompactPath B T w)) ⟨T,hT.le,le_rfl⟩
  have hXm:Measurable X := ((ContinuousMap.evalCLM ℝ (⟨T,hT.le,le_rfl⟩:Icc (0:ℝ) T) :
    C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n)).continuous.comp
    (hSc.comp (continuous_const.add ((columnOperator v).compLeftContinuous ℝ _).continuous))).measurable.comp
      (brownian_system_compact_measurable B T)
  have hm := euclidean_density_ofLp P X hXm p hpc.measurable hmap
  have hpath:∀w,e.toContinuousLinearMap.compLeftContinuous ℝ _
      (ContinuousMap.const (Icc (0:ℝ) T) (e.symm x)+(columnOperator v').compLeftContinuous ℝ _
        (brownianSystemCompactPath B T w))=
      ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ _ (brownianSystemCompactPath B T w) := by
    intro w
    apply ContinuousMap.ext
    intro t
    change e (e.symm x+columnOperator v' (brownianSystemCompactPath B T w t))=x+columnOperator v (brownianSystemCompactPath B T w t)
    rw [map_add,e.apply_symm_apply,columnOperator_apply,columnOperator_apply,map_sum]
    congr 1
  have hm':P.map (fun w => S' (ContinuousMap.const _ (e.symm x)+(columnOperator v').compLeftContinuous ℝ _
      (brownianSystemCompactPath B T w)) ⟨T,hT.le,le_rfl⟩)=volume.withDensity (fun y => ENNReal.ofReal (p (e y))) := by
    change P.map (fun w => e.symm (S (e.toContinuousLinearMap.compLeftContinuous ℝ _
      (ContinuousMap.const _ (e.symm x)+(columnOperator v').compLeftContinuous ℝ _
        (brownianSystemCompactPath B T w))) ⟨T,hT.le,le_rfl⟩))=_
    simp only [hpath]
    exact hm
  have hpos := rectangular_density_positive P B v' (column_ellipticity_posDef v ell hell hv)
    (e.symm x) b' K' hb' M hM hbg T hT S' (coordinate_forcing_continuous e T S hSc)
    (coordinate_forcing_equation e T hT.le b hb.continuous S hSeq)
    (fun y => p (e y)) (hpc.comp e.continuous) (fun y => hpn (e y)) hm'
  intro y
  simpa only [e.apply_symm_apply] using hpos (e.symm y)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.elliptic_density_positive
