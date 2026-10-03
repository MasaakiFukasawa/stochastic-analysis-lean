import Chapter11GeneralAssociativity
import Chapter11ReplicationIntegrability

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The representation integrand is converted into actual stock holdings
 by associativity of Ito integrals, not by formal differential notation. -/
theorem replication_stock_integral {Ω : Type*} {m : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → Q E=0 → MeasurableSet[F t] E)
    (W N M J : ClosedTime T → Ω → ℝ) (S φ : Ω × ℝ → ℝ) (σ : ℝ) (hσ : σ≠0)
    (hS : ∀ z,S z≠0) (hSm : ∀ w,Measurable (fun r => S (w,r)))
    (hφm : ∀ w,Measurable (fun r => φ (w,r)))
    (hW : LocalMProcessWitness Q F W) (hN : LocalMProcessWitness Q F N)
    (hM : LocalMProcessWitness Q F M) (hJ : LocalMProcessWitness Q F J)
    (hNI : ItoCovarianceFormula Q F W (fun z => σ*S z) N)
    (hMI : ItoCovarianceFormula Q F W φ M)
    (hJI : ItoCovarianceFormula Q F N (fun z => φ z/(σ*S z)) J) :
    ∀ᵐ w ∂Q,∀ t,t<⊤ → J t w=M t w := by
  have he : (fun z => (φ z/(σ*S z))*(σ*S z))=φ := by
    funext z
    exact div_mul_cancel₀ _ (mul_ne_zero hσ (hS z))
  have hMI' : ItoCovarianceFormula Q F W (fun z => (φ z/(σ*S z))*(σ*S z)) M := by
    rw [he];exact hMI
  exact ito_integral_associativity Q hT F hF hle hnull W N J M (fun z => σ*S z) (fun z => φ z/(σ*S z))
    hW hN hJ hM (fun w => (hSm w).const_mul σ) (fun w => (hφm w).div ((hSm w).const_mul σ)) hNI hJI hMI'

/-- Both holdings inherit progressive measurability from the price and
 representation process. No continuity of the representation integrand is used. -/
theorem replication_holdings_progressive {Ω D : Type*} [MeasurableSpace D] [Preorder D]
    (F : D → MeasurableSpace Ω) (φ S U : Ω × D → ℝ) (σ : ℝ)
    (hφ : @Measurable _ _ (progressiveSpace F) inferInstance φ)
    (hS : @Measurable _ _ (progressiveSpace F) inferInstance S)
    (hU : @Measurable _ _ (progressiveSpace F) inferInstance U) :
    @Measurable _ _ (progressiveSpace F) inferInstance (fun z => φ z/(σ*S z)) ∧
      @Measurable _ _ (progressiveSpace F) inferInstance (fun z => U z-φ z/σ) := by
  exact ⟨hφ.div (hS.const_mul σ),hU.sub (hφ.div_const σ)⟩

end Asakura.Chapter11
