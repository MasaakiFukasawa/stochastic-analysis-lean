import Chapter3PolarizedQuadraticSum
import Chapter3PolarizedStieltjesMeasure
import Chapter2CovarianceStieltjes

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The full weighted covariation approximation: localization is removed,
both original martingales are allowed, and the limit is the integral for
the canonical BV signed Stieltjes measure of their covariance. -/
theorem general_covariation_approximation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (hbX : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (hbY : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖Y (min (τ n (j+1) ω) t) ω-Y (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (hHosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∀ᵐ ω ∂P,
      ∃ (hCv : BoundedVariationOn ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) univ)
        (hCr : ∀ x, ContinuousWithinAt ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) (Ici x) x),
      TendstoUniformly
        (fun n t => ∑' j, H (τ n j ω) ω*
          (X (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-X (min (τ n j ω) (min (realTimeClamp d) t)) ω)*
          (Y (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-Y (min (τ n j ω) (min (realTimeClamp d) t)) ω))
        (fun t => signedIntegralRaw
          (bvSigned ((fun r => C (realTimeClamp r) ω) ∘ intervalClamp 0 d hd) hCv hCr 0)
          ((Iic (finitePrefixTime d hd t).val).indicator (fun r => H (realTimeClamp r) ω))) atTop := by
  obtain ⟨A,hA⟩ := local_covariance_witness_exists P F hF hle hnull X X hX hX
  obtain ⟨B,hB⟩ := local_covariance_witness_exists P F hF hle hnull Y Y hY hY
  let U := fun t ω => (1/2:ℝ)*X t ω+(1/2:ℝ)*Y t ω
  let V := fun t ω => (1/2:ℝ)*X t ω+(-1/2:ℝ)*Y t ω
  let Qp := fun t ω => (1/2:ℝ)^2*A t ω+2*(1/2:ℝ)*(1/2:ℝ)*C t ω+(1/2:ℝ)^2*B t ω
  let Qm := fun t ω => (1/2:ℝ)^2*A t ω+2*(1/2:ℝ)*(-1/2:ℝ)*C t ω+(-1/2:ℝ)^2*B t ω
  have hU := (hX.smul P F (1/2:ℝ)).add P F hF hle (hY.smul P F (1/2:ℝ))
  have hV := (hX.smul P F (1/2:ℝ)).add P F hF hle (hY.smul P F (-1/2:ℝ))
  have hQp := quadratic_variation_linear_combination P F hF hle X Y A B C hA hB hC (1/2) (1/2)
  have hQm := quadratic_variation_linear_combination P F hF hle X Y A B C hA hB hC (1/2) (-1/2)
  have hbu (n j) : ∀ᵐ ω ∂P, ∀ t,
      ‖U (min (τ n (j+1) ω) t) ω-U (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n := by
    filter_upwards [hbX n j,hbY n j] with ω hx hy
    intro t
    exact (half_combination_increment_bounds (fun t => X t ω) (fun t => Y t ω)
      (τ n j ω) (τ n (j+1) ω) t _ (hx t) (hy t)).1
  have hbv (n j) : ∀ᵐ ω ∂P, ∀ t,
      ‖V (min (τ n (j+1) ω) t) ω-V (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n := by
    filter_upwards [hbX n j,hbY n j] with ω hx hy
    intro t
    exact (half_combination_increment_bounds (fun t => X t ω) (fun t => Y t ω)
      (τ n j ω) (τ n (j+1) ω) t _ (hx t) (hy t)).2
  have hp := general_diagonal_quadratic_approximation P F hF hle hnull U Qp H hU hQp hHm hHc
    c hcm hct hcc τ hτ hτmono hτtop hτ0 hcofinal hbu hHosc d hd hdT
  have hm := general_diagonal_quadratic_approximation P F hF hle hnull V Qm H hV hQm hHm hHc
    c hcm hct hcc τ hτ hτmono hτtop hτ0 hcofinal hbv hHosc d hd hdT
  filter_upwards [hp,hm] with ω hpω hmω
  obtain ⟨hpm,hpr,hpω⟩ := hpω
  obtain ⟨hmm,hmr,hmω⟩ := hmω
  let Cp := fun r => C (realTimeClamp r) ω
  have hCv := intervalClamp_boundedVariation 0 d hd Cp (hC.variation.finite_boundedVariation F ω d hd hdT)
  have hCr := intervalClamp_right_continuous 0 d hd Cp
    (fun r hr => (covariance_real_continuous_on P F X Y C hX hY hC d hdT ω r hr).mono inter_subset_left)
  refine ⟨hCv,hCr,?_⟩
  let α := (intervalStieltjes 0 d hd (fun r => Qp (realTimeClamp r) ω) hpm hpr).measure
  let β := (intervalStieltjes 0 d hd (fun r => Qm (realTimeClamp r) ω) hmm hmr).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite 0 d hd _ hpm hpr
  letI : IsFiniteMeasure β := intervalStieltjes_finite 0 d hd _ hmm hmr
  have hν : bvSigned (Cp ∘ intervalClamp 0 d hd) hCv hCr 0 = α.toSignedMeasure-β.toSignedMeasure := by
    apply polarized_stieltjes_measure d hd _ _ Cp hpm hmm hpr hmr hCv hCr
    intro r _
    dsimp only [Qp,Qm,Cp]
    ring
  have hip : Integrable (fun r => H (realTimeClamp r) ω) α :=
    continuous_weight_stieltjes_integrable d hd hdT _ (hHc ω) _ hpm hpr
  have him : Integrable (fun r => H (realTimeClamp r) ω) β :=
    continuous_weight_stieltjes_integrable d hd hdT _ (hHc ω) _ hmm hmr
  have hi (t : ClosedTime T) : signedIntegralRaw
      (bvSigned (Cp ∘ intervalClamp 0 d hd) hCv hCr 0)
      ((Iic (finitePrefixTime d hd t).val).indicator (fun r => H (realTimeClamp r) ω)) =
      (∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ω ∂α)-
      (∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ω ∂β) := by
    rw [hν,signed_difference_integral α β _
      (integrable_add_measure.mpr ⟨hip.indicator measurableSet_Iic,him.indicator measurableSet_Iic⟩),
      integral_indicator measurableSet_Iic,integral_indicator measurableSet_Iic]
  have hl := uniform_limit_sub _ _ _ _ hpω hmω
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  have hs (n : ℕ) (t : ClosedTime T) := partition_cross_sum_polarization (fun j => τ n j ω)
    (hτmono n ω) (hcofinal n ω) (fun t => X t ω) (fun t => Y t ω) (fun j => H (τ n j ω) ω)
    (realTimeClamp d) (min (realTimeClamp d) t) hdt (min_le_left _ _)
  have hsfun := funext (fun n => funext (fun t => hs n t))
  have hifun := funext hi
  rw [hsfun,hifun]
  exact hl

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.general_covariation_approximation
