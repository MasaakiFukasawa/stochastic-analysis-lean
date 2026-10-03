import Chapter12FiniteBrownianTrim
import Chapter12ProbabilityTrim
import Chapter12CylinderOperatorDomain
import Chapter12GraphClosure
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory ProbabilityTheory Set Filter ENNReal
open scoped Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Construction on F_T, not on the larger sigma algebra containing future
Brownian information. The natural-filtration hypothesis is imposed only
on random variables on this terminal probability space. -/
theorem brownian_finite_malliavin_operator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0 < T)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hgen : ∀ f : Lp ℝ q (P.trim (B.le (realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w z => brownianTimeCoordinate P B T z w) inferInstance] f
          (P.trim (B.le (realTimeClamp T)))) :
    let X := brownianTimeCoordinate P B T
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial T hT
    ∃ W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
    ∃ hW : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩)
      (P.trim (B.le (realTimeClamp T))),
    ∃ D : Lp ℝ p (P.trim (B.le (realTimeClamp T))) →ₗ.[ℝ]
      Lp (FiniteWienerHilbert d T) p (P.trim (B.le (realTimeClamp T))),
      D.IsClosable ∧ D.closure.IsClosed ∧ CompleteSpace D.closure.graph ∧
      (D.graph : Set _) = range (cylinderPair (P.trim (B.le (realTimeClamp T)))
        W univ dense_univ (fun h _ => hW h) p hp) ∧
      (D.closure.graph : Set _) = closure
        (range (cylinderPair (P.trim (B.le (realTimeClamp T))) W univ dense_univ (fun h _ => hW h) p hp)) ∧
      (∀ F, F ∈ D.domain ↔ ∃ c : SmoothCylinder (FiniteWienerHilbert d T),
        c.valueLp (P.trim (B.le (realTimeClamp T))) W univ dense_univ (fun h _ => hW h) p hp = F) ∧
      (∀ z, X z =ᵐ[P.trim (B.le (realTimeClamp T))]
        (W (brownianTimeDirection z) : Ω → ℝ)) := by
  let X := brownianTimeCoordinate P B T
  have hXm := brownian_time_coordinate_measurable P B T
  have hXc := brownian_time_coordinate_continuous P B T
  obtain ⟨W,hW,hcoord⟩ := finite_brownian_trim_wiener P B T hT.le
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  letI : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : Nonempty (BrownianTimeCoordinates d T) := ⟨(0,⟨0,le_rfl,hT.le⟩)⟩
  obtain ⟨times,htimes⟩ := TopologicalSpace.exists_dense_seq (α := BrownianTimeCoordinates d T)
  have hdense := concrete_cylinder_dense (P.trim (B.le (realTimeClamp T))) W univ dense_univ
    (fun h _ => hW h) X hXm hXc
    brownianTimeDirection hcoord times htimes q hq hgen
  obtain ⟨D,hD,hgraph,hdom⟩ := concrete_cylinder_operator_exact_domain
    (P.trim (B.le (realTimeClamp T))) W univ dense_univ (fun h _ => hW h) p q hp hq hdense
  refine ⟨W,hW,D,hD,hD.closure_isClosed,derivative_graph_complete D hD,hgraph,?_,hdom,hcoord⟩
  rw [← hD.graph_closure_eq_closure_graph]
  rw [Submodule.topologicalClosure_coe,hgraph]

end Asakura.Chapter12
