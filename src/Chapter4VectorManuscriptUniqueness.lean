import Chapter4VectorGlobalUniqueness
import Chapter4VectorCoefficientBridge

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem sde_unique_from_manuscript_hypotheses
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ 2 P)
    (X₁ X₂ : ClosedTime T → Ω → Fin dim → ℝ)
    (ha₁ : ∀ t,t<⊤ → Measurable[F t] (X₁ t)) (ha₂ : ∀ t,t<⊤ → Measurable[F t] (X₂ t))
    (hc₁ : ∀ w t,t<⊤ → ContinuousAt (fun s => X₁ s w) t)
    (hc₂ : ∀ w t,t<⊤ → ContinuousAt (fun s => X₂ s w) t)
    (N₁ N₂ : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn₁ : ∀ i j,LocalMProcessWitness P F (N₁ i j))
    (hn₂ : ∀ i j,LocalMProcessWitness P F (N₂ i j))
    (hI₁ : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X₁ (realTimeClamp z.2) z.1)) (N₁ i j))
    (hI₂ : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X₂ (realTimeClamp z.2) z.1)) (N₂ i j))
    (he₁ : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X₁ (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X₁ (realTimeClamp s) w))+∑ j,N₁ i j (realTimeClamp r) w)
    (he₂ : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X₂ (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X₂ (realTimeClamp s) w))+∑ j,N₂ i j (realTimeClamp r) w) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → X₁ t w=X₂ t w := by
  obtain ⟨hμ,hσ,hm,hs⟩ := manuscript_lipschitz_coordinates μ σ L hL hLip
  exact vector_sde_global_unique P hT F hF hle hnull W C hW hC hclock μ σ hμ hσ
    (L*(dim:ℝ)) (by positivity) hm hs ξ hξm hξi X₁ X₂ ha₁ ha₂ hc₁ hc₂ N₁ N₂ hn₁ hn₂ hI₁ hI₂ he₁ he₂

end Asakura.Chapter4.Vector
