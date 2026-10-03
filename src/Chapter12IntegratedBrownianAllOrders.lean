import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Chapter12CylinderAllSobolevOrders
import Chapter12IntegratedBrownianDensity

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

local instance : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

@[reducible] noncomputable def finiteScalarWienerHilbertData (T : ℝ) : RealHilbertSpaceData where
  carrier := Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  separable := inferInstance

/-- Both coordinates of the integrated Brownian example belong to every
Sobolev order, on the same Wiener core that gives their Gram matrix. -/
theorem integrated_brownian_all_sobolev_orders {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T)
    (W : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (B : Icc (0:ℝ) T × Ω → ℝ) (hm : Measurable B)
    (he : ∀ t,(W (finiteTimeIntervalVector T 0 t.val) : Ω → ℝ)=ᵐ[P] (fun w => B (t,w))) :
    letI := finite_horizon_L2_nontrivial T hT
    HasAllSobolevJets (finiteScalarWienerHilbertData T) P W univ dense_univ (fun h _ => hW h)
      (fun w => B (⟨T,hT.le,le_rfl⟩,w)) ∧
    HasAllSobolevJets (finiteScalarWienerHilbertData T) P W univ dense_univ (fun h _ => hW h)
      (fun w => ∫ t : Icc (0:ℝ) T,B (t,w) ∂compactTimeMeasure T hT.le) := by
  letI := finite_horizon_L2_nontrivial T hT
  constructor
  · exact (wiener_linear_square_all_orders (finiteScalarWienerHilbertData T) P W univ dense_univ
      (fun h _ => hW h) (finiteTimeIntervalVector T 0 T) _ (he ⟨T,hT.le,le_rfl⟩)).1
  · exact (wiener_linear_square_all_orders (finiteScalarWienerHilbertData T) P W univ dense_univ
      (fun h _ => hW h) (integratedBrownianDirection T hT.le) _
      (integrated_wiener_coordinate P T hT.le W B hm he)).1

end Asakura.Chapter12
