import Chapter12CylinderAllSobolevOrders
import Chapter12BrownianMalliavinOperator
import Chapter12NaturalBrownianLpInformation
import Chapter12DeterministicDivergenceClosure
import Chapter12OrthogonalWienerLaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

local instance : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

@[reducible] noncomputable def finiteWienerHilbertData (d : ℕ) (T : ℝ) : RealHilbertSpaceData where
  carrier := FiniteWienerHilbert d T
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  separable := inferInstance

/-- The chapter's final exercise on the actual closed Malliavin derivative
constructed from the given Brownian motion: D B_T=h, Gamma=T, U=h/T,
and delta(U)=B_T/T. -/
theorem natural_brownian_density_exercise_all_orders {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T) :
    let BS := naturalBrownianSystem P B hB hm hc
    let R := P.trim (BS.le (realTimeClamp T))
    letI := probability_trim P _ (BS.le (realTimeClamp T))
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
    let h : FiniteWienerHilbert 0 T := brownianTimeDirection (0,⟨T,T.property,le_rfl⟩)
    ∃ W : FiniteWienerHilbert 0 T →ₗᵢ[ℝ] Lp ℝ 2 R,
    ∃ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) R,
      HasAllSobolevJets (finiteWienerHilbertData 0 T) R W univ dense_univ (fun h _ => hW h) (B T) ∧
      HasAllSobolevJets (finiteWienerHilbertData 0 T) R W univ dense_univ (fun h _ => hW h) (fun w => B T w^2) ∧
    ∃ D : Lp ℝ 2 R →ₗ.[ℝ] Lp (FiniteWienerHilbert 0 T) 2 R,
      D.IsClosed ∧
      (W h : Ω → ℝ) =ᵐ[R] (B T) ∧
      (W h,(memLp_const (μ := R) (p := 2) h).toLp (fun _ => h))∈D.graph ∧
      inner ℝ h h=(T:ℝ) ∧ inner ℝ h ((1/(T:ℝ)) • h)=1 ∧
      IsDivergence D ((memLp_const (μ := R) (p := 2) ((1/(T:ℝ)) • h)).toLp
        (fun _ => (1/(T:ℝ)) • h)) (W ((1/(T:ℝ)) • h)) ∧
      (W ((1/(T:ℝ)) • h) : Ω → ℝ) =ᵐ[R] (fun w => B T w/(T:ℝ)) := by
  let BS := naturalBrownianSystem P B hB hm hc
  have hop := brownian_finite_malliavin_operator P BS T (show (0:ℝ)<T from hT) 2 2
    (by simp) (by simp) (natural_brownian_Lp_information P B hB hm hc T T.property 2)
  have hcoord := natural_brownian_coordinate P B hB hm hc T
  letI := probability_trim P _ (BS.le (realTimeClamp T))
  letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  let R := P.trim (BS.le (realTimeClamp T))
  dsimp only at hop ⊢
  obtain ⟨W,hW,D,hclos,hclosed,hcomplete,hgraph,hgraphClosed,hdom,hX⟩ := hop
  let h : FiniteWienerHilbert 0 T := brownianTimeDirection (0,⟨T,T.property,le_rfl⟩)
  have he : (W h : Ω → ℝ) =ᵐ[R] B T := by
    filter_upwards [hX (0,⟨T,T.property,le_rfl⟩)] with w hw
    exact hw.symm.trans (hcoord (0,⟨T,T.property,le_rfl⟩) w)
  have hinner : inner ℝ h h=(T:ℝ) := by
    simpa [h] using brownian_terminal_direction_inner 0 T T.property 0 0
  have hall := wiener_linear_square_all_orders (finiteWienerHilbertData 0 T) R W
    univ dense_univ (fun h _ => hW h) h (B T) he
  refine ⟨W,hW,hall.1,hall.2,D.closure,hclosed,he,?_,hinner,?_,?_,?_⟩
  · apply wiener_coordinate_derivative_graph R W univ dense_univ (fun h _ => hW h) D.closure _ h
    intro c
    change cylinderPair R W univ dense_univ (fun h _ => hW h) 2 (by simp) c∈(D.closure.graph : Set _)
    rw [hgraphClosed]
    exact subset_closure (mem_range_self c)
  · rw [inner_smul_right,hinner]
    exact div_mul_cancel₀ 1 (show (T:ℝ)≠0 from ne_of_gt hT)
  · exact deterministic_divergence_closure_from_core R W univ dense_univ (fun h _ => hW h)
      D hclos hgraph _
  · rw [map_smul]
    filter_upwards [Lp.coeFn_smul (1/(T:ℝ)) (W h),he] with w hw hew
    rw [hw]
    change (1/(T:ℝ))*W h w=B T w/(T:ℝ)
    rw [hew]
    ring

end Asakura.Chapter12
