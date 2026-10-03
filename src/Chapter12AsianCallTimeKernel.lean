import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Chapter12AsianCallPayoffGraph
import Chapter12AsianWeightedDerivativeTime

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The discounted Asian call belongs to the constructed closed derivative,
and its joint time derivative is the exact kernel used in the hedge formula. -/
theorem asian_call_time_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (i : Fin (d+1))
    (T : ℝ) (hT : 0<T) [Nontrivial (FiniteWienerHilbert d T)]
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp))))
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (hXW : ∀ t,(fun w => X w t) =ᵐ[P] (W (brownianTimeDirection (i,t)) : Ω → ℝ))
    (x σ r K : ℝ) (G : Ω → ℝ) (hG : MemLp G 2 P)
    (hSb : ∀ t,∀ᵐ w ∂P,‖stockPathValue x σ r T (X w) t‖≤‖G w‖)
    (hno : P {w | asianPathAverage x r T hT.le σ (X w)=K}=0) :
    ∃ hF : MemLp (fun w => Real.exp (-r*T)*max (asianPathAverage x r T hT.le σ (X w)-K) 0) 2 P,
    ∃ U : Lp (FiniteWienerHilbert d T) 2 P,
      (hF.toLp _,U) ∈ D.graph ∧
      (brownianDerivativeTime P T hT.le U i : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod (compactTimeMeasure T hT.le)]
        (fun z => (Real.exp (-r*T)*σ/T)*(if K<asianPathAverage x r T hT.le σ (X z.1) then (1:ℝ) else 0)*
          asianRemainingMoment T hT.le x σ r 0 (X z.1) z.2) := by
  letI : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : MeasurableSpace (FiniteWienerHilbert d T) := borel _
  letI : BorelSpace (FiniteWienerHilbert d T) := ⟨rfl⟩
  have hh : Continuous (fun t : Icc (0:ℝ) T => brownianTimeDirection (i,t)) :=
    (singleCoordinateIsometry i).continuous.comp (finite_time_prefix_continuous T)
  have hb (t : Icc (0:ℝ) T) : ‖brownianTimeDirection (i,t)‖≤Real.sqrt T := by
    change ‖singleCoordinateIsometry i (finiteTimeIntervalVector T 0 t.val)‖≤_
    rw [LinearIsometry.norm_map,finite_time_interval_norm T 0 t.val le_rfl t.property.1 t.property.2,sub_zero]
    exact Real.sqrt_le_sqrt t.property.2
  obtain ⟨hF,hDF,hgraph⟩ := asian_call_payoff_graph P W univ dense_univ (fun h _ => hW h) D hD hg
    T hT X hXm _ hh hb hXW x σ r K G hG hSb hno
  refine ⟨hF,hDF.toLp _,hgraph,?_⟩
  let q := fun w => Real.exp (-r*T)/T*(if K<asianPathAverage x r T hT.le σ (X w) then (1:ℝ) else 0)
  have hA := (asian_path_average_measurable x r T hT.le σ).comp hXm
  have hqm : Measurable q := by
    exact (Measurable.ite (measurableSet_lt measurable_const hA) measurable_const measurable_const).const_mul _
  have hk := asian_weighted_moment_derivative_time P i T hT.le x σ r 0 X hXm q hqm
    (hDF.toLp _) hDF.coeFn_toLp
  refine hk.trans (ae_of_all _ fun z => ?_)
  dsimp only [q]
  ring

end Asakura.Chapter12
