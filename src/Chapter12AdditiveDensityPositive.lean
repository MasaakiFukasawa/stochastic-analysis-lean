import Chapter12PositiveDensityDriver
import Chapter12GirsanovCompactEquation
import Chapter12ForcingPathUniqueness
import Chapter12ContinuousDensityEquality
import Chapter6AffineLinearGrowth

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem additive_density_positive {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (L:(Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x:Fin d → ℝ)
    (b:(Fin d → ℝ) → Fin d → ℝ) (K:ℝ≥0) (hb:LipschitzWith K b)
    (M:ℝ) (hM:0≤M) (hbg:∀y,‖WithLp.toLp 2 (b y)‖≤M*(1+‖WithLp.toLp 2 y‖))
    (T:ℝ) (hT:0<T)
    (S:C(Icc (0:ℝ) T,Fin d → ℝ) → C(Icc (0:ℝ) T,Fin d → ℝ)) (hSc:Continuous S)
    (hSeq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (p:(Fin d → ℝ) → ℝ) (hpc:Continuous p) (hpn:∀y,0≤p y)
    (hmap:P.map (fun w => S (ContinuousMap.const _ x+L.toContinuousLinearMap.compLeftContinuous ℝ _
      (brownianSystemCompactPath B T w)) ⟨T,hT.le,le_rfl⟩)=volume.withDensity (fun y => ENNReal.ofReal (p y))) :
    ∀y,0<p y := by
  let μ := fun z:ℝ×(Fin d → ℝ) => b z.2
  have hμ:Continuous μ := hb.continuous.comp continuous_snd
  obtain ⟨C,hC,hCg⟩ := affine_transformed_linear_growth L x μ M hM (fun z => hbg z.2)
  obtain ⟨N,V,Q,hQp,BQ,q,hqm,hqn,hF,hW,hN,hNI,hV,hQD,hbase,hqmap,hCE,hlower,hpos⟩ :=
    linear_growth_positive_density_driver P B L x μ hμ T hT C hC hCg
  letI := hQp
  let t:Icc (0:ℝ) T := ⟨T,hT.le,le_rfl⟩
  let a := fun y:C(Icc (0:ℝ) T,Fin d → ℝ) => ContinuousMap.const _ x+L.toContinuousLinearMap.compLeftContinuous ℝ _ y
  let Φ := fun y:C(Icc (0:ℝ) T,Fin d → ℝ) => S (a y) t
  have hΦ:Measurable Φ := ((ContinuousMap.evalCLM ℝ t : C(Icc (0:ℝ) T,Fin d → ℝ) →L[ℝ] (Fin d → ℝ)).continuous.comp
    (hSc.comp (continuous_const.add (L.toContinuousLinearMap.compLeftContinuous ℝ _).continuous))).measurable
  have hident := (brownian_compact_common_law P Q B BQ T).comp hΦ
  have hweak := girsanov_compact_equation P Q B BQ L x b hb.continuous T hT.le hW
  have he:(fun w => Φ (brownianSystemCompactPath BQ T w))=ᵐ[Q]
      (fun w => x+L (fun i => B.W i (realTimeClamp T) w)) := by
    filter_upwards [hweak] with w hw
    have hsol := forcing_path_uniqueness b K hb T hT.le (a (brownianSystemCompactPath BQ T w))
      (S (a (brownianSystemCompactPath BQ T w))) (a (brownianSystemCompactPath B T w))
      (hSeq _) hw
    exact congrArg (fun u:C(Icc (0:ℝ) T,Fin d → ℝ) => u t) hsol
  have hlaw:P.map (fun w => Φ (brownianSystemCompactPath B T w))=
      Q.map (fun w => x+L (fun i => B.W i (realTimeClamp T) w)) :=
    hident.map_eq.trans (Measure.map_congr he)
  have heq:volume.withDensity (fun y => ENNReal.ofReal (p y))=
      volume.withDensity (fun y => ENNReal.ofReal (q y)) := hmap.symm.trans (hlaw.trans hqmap)
  exact hpos p hpc (real_density_ae_equality volume p q hpc.measurable hqm (ae_of_all _ hpn) hqn heq)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.additive_density_positive
