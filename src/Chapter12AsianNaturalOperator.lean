import Chapter12AsianCallBrownianDerivative
import Chapter12NaturalBrownianLpInformation
import Chapter12BrownianCompactPath
import Chapter12BrownianMalliavinOperator

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The Asian payoff and its time derivative belong to the closed derivative
constructed from the given Brownian motion on its completed natural filtration. -/
theorem asian_natural_malliavin_operator {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T)
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    let BS := naturalBrownianSystem P B hB hm hc
    let X := brownianCompactPath B hc T
    let R := P.trim (BS.le (realTimeClamp T))
    letI := probability_trim P _ (BS.le (realTimeClamp T))
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
    ∃ W : FiniteWienerHilbert 0 T →ₗᵢ[ℝ] Lp ℝ 2 R,
    ∃ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) R,
    ∃ D : Lp ℝ 2 R →ₗ.[ℝ] Lp (FiniteWienerHilbert 0 T) 2 R,
      D.IsClosed ∧
      (D.graph : Set _) = closure (range (cylinderPair R W univ dense_univ (fun h _ => hW h) 2 (by simp))) ∧
      (∀ z,@brownianTimeCoordinate Ω m P inferInstance 0 BS T z =ᵐ[R] (W (brownianTimeDirection z) : Ω → ℝ)) ∧
      ∃ hF : MemLp (fun w => Real.exp (-r*T)*max (asianPathAverage x r T T.property σ (X w)-K) 0) 2 R,
      ∃ U : Lp (FiniteWienerHilbert 0 T) 2 R,
        (hF.toLp _,U) ∈ D.graph ∧
        (brownianDerivativeTime R T T.property U 0 : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[R.prod (compactTimeMeasure T T.property)]
          (fun z => (Real.exp (-r*T)*σ/T)*(if K<asianPathAverage x r T T.property σ (X z.1) then (1:ℝ) else 0)*
            asianRemainingMoment T T.property x σ r 0 (X z.1) z.2) := by
  let BS := naturalBrownianSystem P B hB hm hc
  let X := brownianCompactPath B hc T
  have hop := brownian_finite_malliavin_operator P BS T (show (0:ℝ)<T from hT) 2 2
    (by simp) (by simp) (natural_brownian_Lp_information P B hB hm hc T T.property 2)
  have hasian := asian_call_brownian_time_derivative P B hB hm hc T hT
    (BS.F (realTimeClamp T)) (BS.le _) X
    (brownian_compact_path_terminal_measurable P B hB hm hc T) (fun _ _ => rfl) x σ r K hx hσ
  have hcoord := natural_brownian_coordinate P B hB hm hc T
  letI := probability_trim P _ (BS.le (realTimeClamp T))
  letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  dsimp only at hop ⊢
  obtain ⟨W,hW,D,hclos,hclosed,hcomplete,hgraph,hgraphClosed,hdom,hX⟩ := hop
  refine ⟨W,hW,D.closure,hclosed,hgraphClosed,hX,?_⟩
  apply hasian W hW D.closure hclosed hgraphClosed
  intro t
  have hh := hX (0,t)
  have he : @brownianTimeCoordinate Ω m P inferInstance 0 BS T (0,t) = fun w => X w t := by
    funext w
    exact hcoord (0,t) w
  rw [← he]
  exact hh

end Asakura.Chapter12
