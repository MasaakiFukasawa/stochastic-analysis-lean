import EndToEndBrownianDensity
import Chapter12VectorNaturalInformation

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology ContDiff NNReal RealInnerProductSpace
namespace Asakura.EndToEnd
open Asakura.Chapter12 Asakura.FullAudit
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Under the chapter's completed Brownian-information convention, constant
 elliptic diffusion and smooth drift with bounded positive-order derivatives
 give a strictly positive smooth density. All Wiener/Malliavin operators,
 path moments, and dense domains are constructed in the proof. -/
theorem natural_brownian_positive_smooth_density {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (d n:ℕ) (T:ℝ) (hT:0<T)
    (B:Asakura.Chapter4.BrownianSystem P (d+1))
    (hnat : B.F (realTimeClamp T) = Asakura.nullAugmentation (m:=m) P
      (MeasurableSpace.comap (fun w z => brownianTimeCoordinate P B T z w) inferInstance))
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
  apply brownian_density_constructed P d n T hT B _ v x b hb hbound ell hell hv
  intro q _ hq f
  exact vector_natural_information_on_trim P B T T le_rfl hnat f
    (Lp.stronglyMeasurable f).measurable

#print axioms natural_brownian_positive_smooth_density
end Asakura.EndToEnd
