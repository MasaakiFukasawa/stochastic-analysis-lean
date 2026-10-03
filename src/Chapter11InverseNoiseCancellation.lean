import Chapter11BrownianAssociativity

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The two actual stochastic integrals in the inverse-factor product
 cancel by associativity and linearity, for any continuous local martingale. -/
theorem inverse_product_noise_cancels
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (D X Y M N U V : ClosedTime T → Ω → ℝ)
    (hD : LocalMProcessWitness P F D) (hM : LocalMProcessWitness P F M)
    (hN : LocalMProcessWitness P F N) (hU : LocalMProcessWitness P F U)
    (hV : LocalMProcessWitness P F V)
    (hXa : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hYa : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (hMI : ItoCovarianceFormula P F D (fun z => X (realTimeClamp z.2) z.1) M)
    (hNI : ItoCovarianceFormula P F D (fun z => -Y (realTimeClamp z.2) z.1) N)
    (hUI : ItoCovarianceFormula P F M (fun z => Y (realTimeClamp z.2) z.1) U)
    (hVI : ItoCovarianceFormula P F N (fun z => X (realTimeClamp z.2) z.1) V) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → U t w+V t w=0 := by
  have hr := open_process_real_regularity F (fun t w => Y t w*X t w)
    (fun t ht => (hYa t ht).mul (hXa t ht))
    (fun w t ht => (hYc w t ht).mul (hXc w t ht))
  obtain ⟨L,hL,hLI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull D hD
    (fun z => Y (realTimeClamp z.2) z.1*X (realTimeClamp z.2) z.1) hr.1 hr.2
  have hneg : LocalMProcessWitness P F (fun t w => -L t w) := by
    simpa only [neg_one_mul] using hL.smul P F (-1)
  have hnegI : ItoCovarianceFormula P F D
      (fun z => X (realTimeClamp z.2) z.1*(-Y (realTimeClamp z.2) z.1)) (fun t w => -L t w) := by
    have hh := hLI.add_smul P F hF hle D L L _ _ hLI (-2)
    convert hh using 1 <;> ext <;> ring
  have hu := ito_integral_associativity P hT F hF hle hnull D M U L
    (fun z => X (realTimeClamp z.2) z.1) (fun z => Y (realTimeClamp z.2) z.1)
    hD hM hU hL (fun w => open_path_real_measurable _ (hXc w))
    (fun w => open_path_real_measurable _ (hYc w)) hMI hUI hLI
  have hv := ito_integral_associativity P hT F hF hle hnull D N V (fun t w => -L t w)
    (fun z => -Y (realTimeClamp z.2) z.1) (fun z => X (realTimeClamp z.2) z.1)
    hD hN hV hneg (fun w => (open_path_real_measurable _ (hYc w)).neg)
    (fun w => open_path_real_measurable _ (hXc w)) hNI hVI hnegI
  filter_upwards [hu,hv] with w huw hvw
  intro t ht
  rw [huw t ht,hvw t ht]
  exact add_neg_cancel _

end Asakura.Chapter11
