import Chapter12MalliavinCallChain
import Chapter12BrownianMalliavinOperator

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The two scalar chain rules stated together in the manuscript. -/
def ScalarChainRules {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) : Prop :=
  ∀ (F : Lp ℝ 2 P) (U : Lp H 2 P), (F,U)∈D.graph →
    (∀ (f df : ℝ → ℝ) (hd : ∀ x,HasDerivAt f (df x) x) (_ : Continuous df)
      (C : ℝ) (hC : 0≤C) (hb : ∀ x,|df x|≤C),
      ∃ hi : MemLp (fun w => df (F w) • U w) 2 P,
      (lipschitzCompositionLp P 2 (bounded_derivative_lipschitz f df hd C hC hb) F,hi.toLp _)∈D.graph) ∧
    (∀ K : ℝ,P {w | F w=K}=0 →
      ∃ (hi : MemLp (fun w => max (F w-K) 0) 2 P)
        (hdi : MemLp (fun w => (if K<F w then (1:ℝ) else 0) • U w) 2 P),
        (hi.toLp _,hdi.toLp _)∈D.graph)

theorem scalar_chain_rules_from_core {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure
      (range (cylinderPair P W univ dense_univ (fun h _ => hW h) 2 (by simp)))) :
    ScalarChainRules P D := by
  intro F U hFU
  constructor
  · intro f df hd hdc C hC hb
    exact closed_malliavin_C1_chain P W univ dense_univ (fun h _ => hW h) 2 (by simp)
      D hD hg F U hFU f df hd hdc C hC hb
  · intro K hno
    exact closed_malliavin_call_chain P W univ dense_univ (fun h _ => hW h) 2 (by simp)
      D hD hg F U hFU K hno

/-- The operator is constructed from the actual finite-horizon Brownian
integral, rather than assumed as an abstract closed operator. -/
theorem brownian_constructed_scalar_chain_rules {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (hgen : ∀ f : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w z => brownianTimeCoordinate P B T z w) inferInstance] f
          (P.trim (B.le (realTimeClamp T)))) :
    letI := probability_trim P _ (B.le (realTimeClamp T))
    letI : MeasurableSpace Ω := B.F (realTimeClamp T)
    letI := finite_horizon_L2_nontrivial T hT
    ∃ W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 (P.trim (B.le (realTimeClamp T))),
    ∃ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩)
      (P.trim (B.le (realTimeClamp T))),
    ∃ D : Lp ℝ 2 (P.trim (B.le (realTimeClamp T))) →ₗ.[ℝ]
      Lp (FiniteWienerHilbert d T) 2 (P.trim (B.le (realTimeClamp T))),
      D.IsClosed ∧
      (D.graph : Set _) = closure (range (cylinderPair (P.trim (B.le (realTimeClamp T)))
        W univ dense_univ (fun h _ => hW h) 2 (by simp))) ∧
      ScalarChainRules (P.trim (B.le (realTimeClamp T))) D := by
  obtain ⟨W,hW,D,_,hcD,_,_,hg,_,_⟩ := brownian_finite_malliavin_operator P B T hT
    2 2 (by simp) (by simp) hgen
  letI := probability_trim P _ (B.le (realTimeClamp T))
  letI : MeasurableSpace Ω := B.F (realTimeClamp T)
  letI := finite_horizon_L2_nontrivial T hT
  exact ⟨W,hW,D.closure,hcD,hg,
    scalar_chain_rules_from_core (P.trim (B.le (realTimeClamp T))) W hW D.closure hcD hg⟩

end Asakura.Chapter12
