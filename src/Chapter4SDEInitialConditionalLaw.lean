import Chapter4EulerEndpointLimit
import Chapter4EulerConditionalLaw
import Chapter4LipschitzExpectationLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Conditional law of an actual solution, from the independent noise law
and the proved approximation convergence. The reference family consists
of actual deterministic-initial-value solutions. -/
theorem sde_initial_conditional_transition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B B₀ : BrownianSystem P noise)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin dim → ℝ) (hX : VectorSDESolution P B.F B.W μ σ ξ X)
    (X₀ : (Fin dim → ℝ) → HalfClosedTime → Ω → Fin dim → ℝ)
    (hX₀ : ∀ x,VectorSDESolution P B₀.F B₀.W μ σ (fun _ => x) (X₀ x))
    (R : ℝ) (hR : 0≤R)
    (f : (Fin dim → ℝ) → ℝ) (Lf : ℝ≥0) (hf : LipschitzWith Lf f)
    (K : ℝ) (hb : ∀ x,‖f x‖≤K) :
    let q := fun x => ∫ w,f (X₀ x (realTimeClamp R) w) ∂P
    Measurable q ∧ (∀ x,‖q x‖≤K) ∧
      P[(fun w => f (X (realTimeClamp R) w)) | B.F ⊥]=ᵐ[P] fun w => q (ξ w) := by
  letI : MeasurableSpace Ω := m
  dsimp only
  let Y := fun n : ℕ => eulerGrid μ σ (fun j r => B.W j (realTimeClamp r)) ξ (R/((n:ℝ)+1)) (n+1)
  let Y₀ := fun x (n : ℕ) => eulerGrid μ σ (fun j r => B₀.W j (realTimeClamp r)) (fun _ => x) (R/((n:ℝ)+1)) (n+1)
  let qn := fun n x => ∫ w,f (Y₀ x n w) ∂P
  let q := fun x => ∫ w,f (X₀ x (realTimeClamp R) w) ∂P
  obtain ⟨hY,hXm,hXi,ht⟩ := euler_endpoint_L2_limit P B L hL μ σ hLip ξ hξ X hX R hR
  have hY₀ x := euler_endpoint_L2_limit P B₀ L hL μ σ hLip (fun _ => x) (memLp_const x) (X₀ x) (hX₀ x) R hR
  obtain ⟨hμ,hσ,_,_⟩ := Vector.manuscript_lipschitz_coordinates μ σ L hL hLip
  have he n : Measurable (qn n) ∧ (∀ x,‖qn n x‖≤K) ∧
      P[(fun w => f (Y n w)) | B.F ⊥]=ᵐ[P] fun w => qn n (ξ w) :=
    euler_conditional_transition P B B₀ μ σ hμ hσ ξ hX.initial_adapted
      (R/((n:ℝ)+1)) (div_nonneg hR (by positivity)) (n+1) f hf.continuous K hb
  have hqt x : Tendsto (fun n => qn n x) atTop (𝓝 (q x)) :=
    lipschitz_expectation_L2_limit P (Y₀ x) (X₀ x (realTimeClamp R))
      (fun n => ((hY₀ x).1 n).1) (hY₀ x).2.1 (fun n => ((hY₀ x).1 n).2)
      (hY₀ x).2.2.1 (hY₀ x).2.2.2 f Lf hf K hb
  have hqm : Measurable q := measurable_of_tendsto_metrizable (fun n => (he n).1) (tendsto_pi_nhds.mpr hqt)
  have hqb x : ‖q x‖≤K := le_of_tendsto (hqt x).norm (Filter.Eventually.of_forall (fun n => (he n).2.1 x))
  refine ⟨hqm,hqb,?_⟩
  have hξm : Measurable[m] ξ := hX.initial_adapted.mono (B.le ⊥) le_rfl
  apply conditional_L2_bounded_limit P (B.F ⊥) (B.le ⊥)
    (fun n w => f (Y n w)) (fun n w => qn n (ξ w)) (fun w => f (X (realTimeClamp R) w)) (fun w => q (ξ w))
    (fun n => bounded_lipschitz_image_memLp P (Y n) (hY n).1 f Lf hf K hb)
    (bounded_lipschitz_image_memLp P _ hXm f Lf hf K hb)
    (fun n => (he n).1.comp hξm) (hqm.comp hξm) K (fun n w => (he n).2.1 _) (fun w => hqb _)
    (lipschitz_image_L2_tendsto P Y _ (fun n => (hY n).1) hXm (fun n => (hY n).2) hXi ht f Lf hf K hb)
    (Filter.Eventually.of_forall (fun w => hqt (ξ w))) (fun n => (he n).2.2)

end Asakura.Chapter4
