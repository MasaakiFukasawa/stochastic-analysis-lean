import EndToEndMalliavinConstruction
import EndToEndBrownianPathMoments
import Chapter12BrownianEllipticPositiveSmoothDensity
import Chapter12FiniteBrownianTrim
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology ContDiff NNReal RealInnerProductSpace
namespace Asakura.EndToEnd
open Asakura.Chapter12 Asakura.FullAudit
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the Wiener isometry and the closed derivative before applying
 the elliptic density theorem. No derivative, covariance, or Sobolev density
 is supplied as an assumption. -/
theorem brownian_density_constructed {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (d n:ℕ) (T:ℝ) (hT:0<T)
    (B:Asakura.Chapter4.BrownianSystem P (d+1))
    (hgen : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤),
      ∀ f : Lp ℝ q (P.trim (B.le (Asakura.FullAudit.realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w z => brownianTimeCoordinate P B T z w) inferInstance] f
          (P.trim (B.le (Asakura.FullAudit.realTimeClamp T))))
    (v:Fin (d+1) → EuclideanSpace ℝ (Fin (n+1))) (x:EuclideanSpace ℝ (Fin (n+1)))
    (b:EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (ell:ℝ) (hell:0<ell)
    (hv:∀z:EuclideanSpace ℝ (Fin (n+1)),ell*‖z‖^2≤∑j,(inner ℝ z (v j))^2) :
    ∃S:C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))) → C(Icc (0:ℝ) T,EuclideanSpace ℝ (Fin (n+1))),
      ContDiff ℝ ∞ S ∧ (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s))) ∧
      ∃p:EuclideanSpace ℝ (Fin (n+1)) → ℝ,ContDiff ℝ ∞ p ∧ (∀y,0<p y) ∧
        @Measure.map Ω _ m _ (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T w)) ⟨T,hT.le,le_rfl⟩) P=
          volume.withDensity (fun y => ENNReal.ofReal (p y)) := by
  have hYp := brownian_system_path_memLp P B T hT.le
  have hYm : Measurable[B.F (realTimeClamp T)]
      (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact Measurable.of_eval (fun i => @brownian_time_coordinate_measurable Ω m P inferInstance d B T (i,t))
  have hYpt (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp
      (@brownianSystemCompactPath Ω m P inferInstance (d+1) B T) p
        (P.trim (B.le (realTimeClamp T))) := by
    rw [memLp_iff]
    exact (eLpNorm_trim (B.le _) hYm.stronglyMeasurable).trans_lt (hYp p hp)
  let X := brownianTimeCoordinate P B T
  have hXm := brownian_time_coordinate_measurable P B T
  have hXc := brownian_time_coordinate_continuous P B T
  obtain ⟨W,hW,hcoord⟩ := finite_brownian_trim_wiener P B T hT.le
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI := finite_horizon_L2_nontrivial T hT
  letI : Nonempty (BrownianTimeCoordinates d T) := ⟨(0,⟨0,le_rfl,hT.le⟩)⟩
  obtain ⟨times,htimes⟩ := TopologicalSpace.exists_dense_seq (α := BrownianTimeCoordinates d T)
  obtain ⟨D,hD,hgraph,hdom,hdense⟩ := malliavin_constructed_domain
    (P.trim (B.le (realTimeClamp T))) W univ dense_univ (fun h _ => hW h)
    X hXm hXc brownianTimeDirection hcoord times htimes hgen
  exact @brownian_elliptic_positive_smooth_density Ω m P inferInstance d n T hT
    (B.F (realTimeClamp T)) (B.le _) inferInstance inferInstance W hW B hcoord hYm hYpt
    D hD hgraph hdom hdense v x b hb hbound ell hell hv

#print axioms brownian_density_constructed
end Asakura.EndToEnd
