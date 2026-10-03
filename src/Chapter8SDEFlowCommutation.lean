import Chapter8FlowLawSemigroup
import Chapter4LipschitzSemigroup

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The commuting law evolutions used to upgrade discrete invariance to
continuous time follow from the already proved SDE semigroup identity. -/
theorem sde_flow_commutation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W b σ (fun _ => x) (Z x))
    (F : ℝ → E → Ω → E) (hF : ∀ r≥0,Measurable (Function.uncurry (F r)))
    (hrep : ∀ r≥0,∀ x,(fun w => F r (e x) w)=ᵐ[P] fun w => e (Z x (realTimeClamp r) w))
    (μ : Measure E) [IsProbabilityMeasure μ] (s t : ℝ) (hs : 0≤s) (ht : 0≤t) :
    flowLaw (flowLaw μ P (F t)) P (F s)=flowLaw (flowLaw μ P (F s)) P (F t) := by
  apply flow_law_commutes μ P (F s) (F t) (hF s hs) (hF t ht)
  intro f hf K hK x
  have hQ r (hr : 0≤r) (g : E → ℝ) y :
      (∫ w,g (F r y w) ∂P)=∫ w,g (e (Z (e.symm y) (realTimeClamp r) w)) ∂P := by
    apply integral_congr_ae
    filter_upwards [hrep r hr (e.symm y)] with w hw
    simpa only [e.apply_symm_apply] using congrArg g hw
  rw [hQ t ht (fun y => ∫ z,f (F s y z) ∂P) x,
    hQ s hs (fun y => ∫ z,f (F t y z) ∂P) x]
  simp_rw [hQ s hs f,hQ t ht f,e.symm_apply_apply]
  have hst := congrFun (lipschitz_transition_semigroup P B L hL b σ hLip Z hZ
    (fun y => f (e y)) (hf.comp e.continuous.measurable) K (fun y => hK (e y)) ⟨s,hs⟩ ⟨t,ht⟩) (e.symm x)
  have hts := congrFun (lipschitz_transition_semigroup P B L hL b σ hLip Z hZ
    (fun y => f (e y)) (hf.comp e.continuous.measurable) K (fun y => hK (e y)) ⟨t,ht⟩ ⟨s,hs⟩) (e.symm x)
  rw [add_comm (⟨s,hs⟩ : ℝ≥0) ⟨t,ht⟩] at hst
  exact hts.symm.trans hst

end Asakura.Chapter8
