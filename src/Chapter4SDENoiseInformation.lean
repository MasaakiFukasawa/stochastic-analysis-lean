import Chapter4L2MeasurableClosure

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Any completed information containing the initial state and Brownian
increments also contains the actual solution. This verifies the
"same information in the limit" step of the manuscript Markov proof. -/
theorem sde_measurable_from_initial_and_noise
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise) (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin dim → ℝ) (hX : VectorSDESolution P B.F B.W μ σ ξ X)
    (G : MeasurableSpace Ω) (hG : G≤m)
    (hnull : ∀ E,MeasurableSet[m] E → P E=0 → MeasurableSet[G] E)
    (hξG : Measurable[G] ξ)
    (hnoise : ∀ j (r : ℝ),0≤r → Measurable[G] (fun w => B.W j (realTimeClamp r) w-B.W j ⊥ w))
    (R : ℝ) (hR : 0≤R) : Measurable[G] (X (realTimeClamp R)) := by
  letI : MeasurableSpace Ω := m
  let Y := fun n : ℕ => eulerGrid μ σ (fun j r => B.W j (realTimeClamp r)) ξ (R/((n:ℝ)+1)) (n+1)
  obtain ⟨hY,hXm,hXi,ht⟩ := euler_endpoint_L2_limit P B L hL μ σ hLip ξ hξ X hX R hR
  obtain ⟨hμ,hσ,_,_⟩ := Vector.manuscript_lipschitz_coordinates μ σ L hL hLip
  have hYG n : Measurable[G] (Y n) := by
    let h := R/((n:ℝ)+1)
    have hh : 0≤h := div_nonneg hR (by positivity)
    let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h (n+1)
    have hZm : Measurable[G] Z := by
      letI : MeasurableSpace Ω := G
      apply measurable_pi_iff.mpr
      intro k
      apply measurable_pi_iff.mpr
      intro j
      have hstart := hnoise j ((k.val:ℝ)*h) (by positivity)
      have hend := hnoise j (((k.val:ℝ)+1)*h) (by positivity)
      convert hend.sub hstart using 1
      funext w
      dsimp only [Z,finiteNoiseGrid,Pi.sub_apply]
      ring
    have hm := (euler_noise_map_continuous μ σ hμ hσ h (n+1)).measurable.comp (hξG.prodMk hZm)
    have he : (fun w => eulerNoiseMap μ σ h (n+1) (ξ w) (Z w))=Y n :=
      funext (fun w => euler_noise_map_grid μ σ (fun j r => B.W j (realTimeClamp r)) ξ h (n+1) w)
    change Measurable[G] (fun w => eulerNoiseMap μ σ h (n+1) (ξ w) (Z w)) at hm
    rw [he] at hm
    exact hm
  exact vector_L2_limit_measurable P G hG hnull Y (X (realTimeClamp R)) hYG hXm
    (fun n => (hY n).2) hXi ht

end Asakura.Chapter4
