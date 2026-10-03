import Chapter4LipschitzSemigroup
import Chapter4SDEInitialStability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- End-to-end construction of the deterministic solution family, its
measurable transition laws, the Borel Markov property for every L2-initial
solution, and both forms of Chapman-Kolmogorov. -/
theorem markov_lipschitz_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise) (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2) :
    ∃ Z : (Fin dim → ℝ) → HalfClosedTime → Ω → Fin dim → ℝ,
      (∀ x,VectorSDESolution P B.F B.W μ σ (fun _ => x) (Z x)) ∧
      (∀ u : ℝ,0≤u → Measurable (fun x => @Measure.map Ω _ m _ (Z x (realTimeClamp u)) P)) ∧
      (∀ (ξ : Ω → Fin dim → ℝ),MemLp ξ 2 P →
        ∀ (X : HalfClosedTime → Ω → Fin dim → ℝ),VectorSDESolution P B.F B.W μ σ ξ X →
        ∀ s u : ℝ,0≤s → 0≤u → ∀ f : (Fin dim → ℝ) → ℝ,Measurable f →
        ∀ K : ℝ,(∀ x,‖f x‖≤K) →
          P[(fun w => f (X (realTimeClamp (s+u)) w)) | B.F (realTimeClamp s)]=ᵐ[P]
            fun w => ∫ y,f y ∂@Measure.map Ω _ m _ (Z (X (realTimeClamp s) w) (realTimeClamp u)) P) ∧
      (∀ f : (Fin dim → ℝ) → ℝ,Measurable f → ∀ K : ℝ,(∀ x,‖f x‖≤K) → ∀ s t : ℝ≥0,
        transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) (s+t) f=
          transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) s
            (transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) t f)) ∧
      (∀ f : (Fin dim → ℝ) → ℝ,transitionOperator P (fun x r => Z x (realTimeClamp (r:ℝ))) 0 f=f) ∧
      (∀ (s t : ℝ≥0) (A : Set (Fin dim → ℝ)),MeasurableSet A → ∀ x : Fin dim → ℝ,
        (@Measure.map Ω _ m _ (Z x (realTimeClamp ((s+t:ℝ≥0):ℝ))) P).real A=
          ∫ y,(@Measure.map Ω _ m _ (Z y (realTimeClamp (t:ℝ))) P).real A
            ∂@Measure.map Ω _ m _ (Z x (realTimeClamp (s:ℝ))) P) := by
  obtain ⟨Z,hZ⟩ := deterministic_sde_family_exists P B L hL μ σ hLip
  refine ⟨Z,hZ,?_,?_,?_,?_,?_⟩
  · intro u hu
    exact (markov_from_lipschitz_coefficients P B L hL μ σ hLip
      (fun _ => 0) (memLp_const 0) (Z 0) (hZ 0) Z hZ 0 u le_rfl hu).1
  · intro ξ hξ X hX s u hs hu f hf K hb
    exact (markov_from_lipschitz_coefficients P B L hL μ σ hLip ξ hξ X hX Z hZ s u hs hu).2 f hf K hb
  · intro f hf K hb s t
    exact lipschitz_transition_semigroup P B L hL μ σ hLip Z hZ f hf K hb s t
  · intro f
    exact lipschitz_transition_zero P B L hL μ σ hLip Z hZ f
  · intro s t A hA x
    exact lipschitz_transition_kernel_composition P B L hL μ σ hLip Z hZ s t A hA x

end Asakura.Chapter4
