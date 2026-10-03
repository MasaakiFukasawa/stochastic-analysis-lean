import Chapter4VectorFiniteUniqueness
import Chapter4VectorBorelMoment
import Chapter4VectorLipschitzGrowth

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness for arbitrary continuous adapted solutions. The needed L2
path moments are consequences of the SDE, not extra assumptions. -/
theorem vector_sde_finite_unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ 2 P)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂)
    (ha₁ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₁ w r))
    (ha₂ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₂ w r))
    (N₁ N₂ : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn₁ : ∀ i j,LocalMProcessWitness P F (N₁ i j))
    (hn₂ : ∀ i j,LocalMProcessWitness P F (N₂ i j))
    (hI₁ : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y₁ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N₁ i j))
    (hI₂ : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y₂ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N₂ i j))
    (he₁ : ∀ᵐ w ∂P,∀ r i,Y₁ w r i=ξ w i+(∫ s in 0..r.val,μ i (Y₁ w (projIcc 0 R hR s)))+∑ j,N₁ i j (realTimeClamp r.val) w)
    (he₂ : ∀ᵐ w ∂P,∀ r i,Y₂ w r i=ξ w i+(∫ s in 0..r.val,μ i (Y₂ w (projIcc 0 R hR s)))+∑ j,N₂ i j (realTimeClamp r.val) w)
    : Y₁=ᵐ[P] Y₂ := by
  obtain ⟨K,hK,hμg,hσg⟩ := vector_lipschitz_growth μ σ L hL hμLip hσLip
  have hξi' : MemLp ξ (ENNReal.ofReal (2:ℝ)) P := by simpa using hξi
  have hi₁ : MemLp Y₁ 2 P := by
    simpa using sde_power_moment_from_borel_growth P hT F hF hle hnull W C hW hC hclock R hR hRT
      μ σ (fun i => (hμ i).measurable) (fun i j => (hσ i j).measurable) K hK hμg hσg 2 le_rfl
      ξ hξm hξi' Y₁ hm₁ ha₁ N₁ hn₁ hI₁ he₁
  have hi₂ : MemLp Y₂ 2 P := by
    simpa using sde_power_moment_from_borel_growth P hT F hF hle hnull W C hW hC hclock R hR hRT
      μ σ (fun i => (hμ i).measurable) (fun i j => (hσ i j).measurable) K hK hμg hσg 2 le_rfl
      ξ hξm hξi' Y₂ hm₂ ha₂ N₂ hn₂ hI₂ he₂
  exact vector_sde_finite_unique_L2 P hT F hF hle hnull W C hW hC hclock R hR hRT L hL
    μ σ hμ hσ hμLip hσLip ξ Y₁ Y₂ hm₁ hm₂ hi₁ hi₂ ha₁ ha₂ N₁ N₂ hn₁ hn₂ hI₁ hI₂ he₁ he₂

end Asakura.Chapter4.Vector
