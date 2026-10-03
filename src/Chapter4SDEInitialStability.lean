import Chapter4SDEEndpointMoment
import Chapter4BrownianSystem
import Chapter4VectorInitialStability
import Chapter4EulerNormComparison

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Initial-state stability for the actual global SDE solutions, including
the Euclidean squared path maximum occurring in the manuscript. -/
theorem sde_initial_stability_euclidean
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise) (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ₁ ξ₂ : Ω → Fin dim → ℝ) (hξ₁ : MemLp ξ₁ 2 P) (hξ₂ : MemLp ξ₂ 2 P)
    (X₁ X₂ : HalfClosedTime → Ω → Fin dim → ℝ)
    (hX₁ : VectorSDESolution P B.F B.W μ σ ξ₁ X₁) (hX₂ : VectorSDESolution P B.F B.W μ σ ξ₂ X₂)
    (R : ℝ) (hR : 0≤R) :
    (∫ w,‖squaredEuclideanPath (Vector.realVectorPath X₁ hX₁.path R (EReal.coe_lt_top R) w-
      Vector.realVectorPath X₂ hX₂.path R (EReal.coe_lt_top R) w)‖ ∂P)≤
      ((dim:ℝ)*2*Real.exp ((2*((dim:ℝ)*(2*R+8*(noise:ℝ)^2)*(L*dim))+1)*R))*
        (∫ w,(∑ i,(ξ₁ w i-ξ₂ w i)^2) ∂P) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨hμ,hσ,hμL,hσL⟩ := Vector.manuscript_lipschitz_coordinates μ σ L hL hLip
  have hclock j w (r : ℝ) hr (_ : (r:EReal)<⊤) := B.diagonal_clock j w r hr
  let Y₁ := Vector.realVectorPath X₁ hX₁.path R (EReal.coe_lt_top R)
  let Y₂ := Vector.realVectorPath X₂ hX₂.path R (EReal.coe_lt_top R)
  obtain ⟨hm₁,hi₁,_⟩ := sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock L hL μ σ hLip ξ₁ hξ₁ X₁ hX₁ R hR (EReal.coe_lt_top R)
  obtain ⟨hm₂,hi₂,_⟩ := sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock L hL μ σ hLip ξ₂ hξ₂ X₂ hX₂ R hR (EReal.coe_lt_top R)
  obtain ⟨N₁,hn₁,hI₁,he₁⟩ := hX₁.integrals
  obtain ⟨N₂,hn₂,hI₂,he₂⟩ := hX₂.integrals
  obtain ⟨J₁,hj₁,hJI₁,hJe₁⟩ := Vector.global_sde_finite_restriction P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock μ σ hσ ξ₁ X₁ hX₁.adapted hX₁.path
    N₁ hn₁ hI₁ he₁ R hR (EReal.coe_lt_top R)
  obtain ⟨J₂,hj₂,hJI₂,hJe₂⟩ := Vector.global_sde_finite_restriction P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock μ σ hσ ξ₂ X₂ hX₂.adapted hX₂.path
    N₂ hn₂ hI₂ he₂ R hR (EReal.coe_lt_top R)
  have hh := Vector.finite_sde_initial_stability P (EReal.coe_lt_top 0) B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j) hclock R hR (EReal.coe_lt_top R)
    (L*dim) (by positivity) μ σ hμ hσ hμL hσL ξ₁ ξ₂
    (hX₁.initial_adapted.mono (B.le ⊥) le_rfl) (hX₂.initial_adapted.mono (B.le ⊥) le_rfl)
    hξ₁ hξ₂ Y₁ Y₂ hm₁ hm₂ hi₁ hi₂
    (fun r => hX₁.adapted _ (real_time_below r.val r.property.1 (EReal.coe_lt_top _)))
    (fun r => hX₂.adapted _ (real_time_below r.val r.property.1 (EReal.coe_lt_top _)))
    J₁ J₂ hj₁ hj₂ hJI₁ hJI₂ hJe₁ hJe₂
  have hnorm := (squared_euclidean_path_expected_bound P (fun w => Y₁ w-Y₂ w) (hm₁.sub hm₂) (hi₁.sub hi₂)).2
  have hξnorm := initial_supnorm_moment_le_euclidean P (fun w => ξ₁ w-ξ₂ w) (hξ₁.sub hξ₂)
  have hbound := hnorm.trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg dim))
  have he := hbound.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hξnorm (by positivity)) (Nat.cast_nonneg dim))
  convert he using 1 <;> simp only [Pi.sub_apply] <;> ring

end Asakura.Chapter4
