import Chapter11BoundedStrategyIntegral
import FullAuditLogWealth

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The printed log-utility identity and optimizer, with the actual stochastic
integral constructed from a bounded progressive strategy. Its zero mean is
proved, rather than supplied as an independent hypothesis. -/
theorem actual_log_utility {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hπ : Measurable π)
    (hπp : ∀ b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => π (z.1,z.2.val)))
    (K x r μ σ T : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (hx : 0<x) (hσ : σ≠0) (hT : 0≤T) :
    ∃ N : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*π z) N ∧
      let V := terminalLogWealth (fun w t => π (w,t)) (N (realTimeClamp T)) x r μ σ T
      Integrable (fun w => Real.log (V w)) P ∧
      (∫ w,Real.log (V w) ∂P)=Real.log x+(r+(μ-r)^2/(2*σ^2))*T-
        σ^2/2*(∫ w,(∫ t in Icc 0 T,(π (w,t)-(μ-r)/σ^2)^2) ∂P) ∧
      (∫ w,Real.log (V w) ∂P)≤Real.log x+(r+(μ-r)^2/(2*σ^2))*T ∧
      ((∀ z,π z=(μ-r)/σ^2) →
        (∫ w,Real.log (V w) ∂P)=Real.log x+(r+(μ-r)^2/(2*σ^2))*T) := by
  obtain ⟨N,C,hN,hNI,_,_,_,_,hmean⟩ := bounded_strategy_integral P B
    (fun z => σ*π z) (hπ.const_mul σ) (fun b h => (hπp b h).const_mul σ)
    (|σ| *K) (mul_nonneg (abs_nonneg _) hK) (fun z => by
      rw [abs_mul];exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg σ))
  have hh := logarithmic_wealth_identity P (fun w t => π (w,t)) (N (realTimeClamp T))
    x r μ σ T K hx hσ hT hπ (fun w t => by simpa only [Real.norm_eq_abs] using hb (w,t))
    (hmean T hT).1 (hmean T hT).2
  have ho := logarithmic_wealth_optimal P (fun w t => π (w,t)) (N (realTimeClamp T))
    x r μ σ T K hx hσ hT hπ (fun w t => by simpa only [Real.norm_eq_abs] using hb (w,t))
    (hmean T hT).1 (hmean T hT).2
  exact ⟨N,hN,hNI,hh.1,hh.2,ho.1,fun hp => ho.2 (fun w t => hp (w,t))⟩

end Asakura.Chapter11
