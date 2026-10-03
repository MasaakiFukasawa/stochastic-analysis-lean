import Chapter12AsianCallTimeKernel
import Chapter12AsianAtomlessTrim
import Chapter12StockEnvelopeTrim
import Chapter12ProbabilityTrim

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- Brownian input supplies the no-atom and stock-envelope hypotheses in
the Asian hedge derivative. No Sobolev membership or moment bound is assumed. -/
theorem asian_call_brownian_time_derivative {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T)
    (mT : MeasurableSpace Ω) (hle : mT≤m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T),X w s=B ⟨s.val,s.property.1⟩ w)
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    letI := probability_trim P mT hle
    letI : MeasurableSpace Ω := mT
    letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
    ∀ (W : FiniteWienerHilbert 0 T →ₗᵢ[ℝ] Lp ℝ 2 (P.trim hle)),
    ∀ hW : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) (P.trim hle),
    ∀ (D : Lp ℝ 2 (P.trim hle) →ₗ.[ℝ] Lp (FiniteWienerHilbert 0 T) 2 (P.trim hle)),D.IsClosed →
      (D.graph : Set _) = closure (range (cylinderPair (P.trim hle) W univ dense_univ (fun h _ => hW h) 2 (by simp))) →
      (∀ t,(fun w => X w t) =ᵐ[P.trim hle] (W (brownianTimeDirection (0,t)) : Ω → ℝ)) →
    ∃ hF : MemLp (fun w => Real.exp (-r*T)*max (asianPathAverage x r T T.property σ (X w)-K) 0) 2 (P.trim hle),
    ∃ U : Lp (FiniteWienerHilbert 0 T) 2 (P.trim hle),
      (hF.toLp _,U) ∈ D.graph ∧
      (brownianDerivativeTime (P.trim hle) T T.property U 0 : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[(P.trim hle).prod (compactTimeMeasure T T.property)]
        (fun z => (Real.exp (-r*T)*σ/T)*(if K<asianPathAverage x r T T.property σ (X z.1) then (1:ℝ) else 0)*
          asianRemainingMoment T T.property x σ r 0 (X z.1) z.2) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨G,hG,hGb,_⟩ := stock_path_envelope_on_trim P mT hle B hB hm hc T X hXm he x σ r 2 (by simp)
  have hno := asian_average_no_atom_on_trim P B hB hm hc T hT mT hle X hXm he x σ r K hx hσ
  letI := probability_trim P mT hle
  letI : MeasurableSpace Ω := mT
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  intro W hW D hD hg hXW
  exact asian_call_time_derivative (P.trim hle) 0 T (show (0:ℝ)<T from hT) W hW D hD hg X hXm hXW
    x σ r K G hG (fun t => ae_of_all _ (hGb t)) hno

end Asakura.Chapter12
