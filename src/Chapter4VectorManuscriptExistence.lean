import Chapter4VectorCoefficientBridge

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The original finite-dimensional sum-of-squares hypothesis constructs
an adapted continuous solution and its Ito integrals on all finite horizons.
Square-integrable path bounds are conclusions, not supplied estimates. -/
theorem sde_exists_from_manuscript_hypotheses
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    : ∃ (X : ClosedTime T → Ω → Fin dim → ℝ)
        (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ),
      (∀ t,t<⊤ → Measurable[F t] (X t)) ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t) ∧
      (∀ i j,LocalMProcessWitness P F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j)) ∧
      (∀ R : ℝ,0≤R → (R:EReal)<T → ∃ V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ),
        MemLp V 2 P ∧ ∀ w r,V w r=X (realTimeClamp r.val) w) ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
        X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w := by
  obtain ⟨hμ,hσ,hm,hs⟩ := manuscript_lipschitz_coordinates μ σ L hL hLip
  exact vector_sde_global_exists P hT F hF hle hnull W C hW hC hclock
    (L*(dim:ℝ)) (by positivity) μ σ hμ hσ hm hs ξ hξ hξi

end Asakura.Chapter4.Vector
