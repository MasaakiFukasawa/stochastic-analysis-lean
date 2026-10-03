import Chapter3StoppedStieltjesApproximation
import Chapter2IncreasingLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic Riemann sum up to b uses no values after b, even though
its notation includes coefficients at every stopping time. -/
theorem quadratic_sum_congr_on_prefix
    {ι : Type*} [LinearOrder ι] (τ : ℕ → ι) (hτ : Monotone τ)
    (X Y H K : ι → ℝ) (b t : ι)
    (hX : ∀ s, s ≤ b → X s = Y s) (hH : ∀ s, s ≤ b → H s = K s) :
    (∑' j, H (τ j)*(X (min (τ (j+1)) (min b t))-X (min (τ j) (min b t)))^2) =
      ∑' j, K (τ j)*(Y (min (τ (j+1)) (min b t))-Y (min (τ j) (min b t)))^2 := by
  apply tsum_congr
  intro j
  rw [hX _ ((min_le_right _ _).trans (min_le_left _ _)),
    hX _ ((min_le_right _ _).trans (min_le_left _ _))]
  by_cases hj : τ j ≤ b
  · rw [hH _ hj]
  · have htj : min b t ≤ τ j := (min_le_left _ _).trans (le_of_not_ge hj)
    rw [min_eq_right htj,min_eq_right (htj.trans (hτ (Nat.le_succ j))),sub_self,
      zero_pow (by decide : 2 ≠ 0),mul_zero,mul_zero]

/-- The stochastic Riemann sum has the same prefix locality. -/
theorem linear_sum_congr_on_prefix
    {ι : Type*} [LinearOrder ι] (τ : ℕ → ι) (hτ : Monotone τ)
    (X Y H K : ι → ℝ) (b t : ι)
    (hX : ∀ s, s ≤ b → X s = Y s) (hH : ∀ s, s ≤ b → H s = K s) :
    (∑' j, H (τ j)*(X (min (τ (j+1)) (min b t))-X (min (τ j) (min b t)))) =
      ∑' j, K (τ j)*(Y (min (τ (j+1)) (min b t))-Y (min (τ j) (min b t))) := by
  apply tsum_congr
  intro j
  rw [hX _ ((min_le_right _ _).trans (min_le_left _ _)),
    hX _ ((min_le_right _ _).trans (min_le_left _ _))]
  by_cases hj : τ j ≤ b
  · rw [hH _ hj]
  · have htj : min b t ≤ τ j := (min_le_left _ _).trans (le_of_not_ge hj)
    rw [min_eq_right htj,min_eq_right (htj.trans (hτ (Nat.le_succ j))),sub_self,mul_zero,mul_zero]

/-- The actual constructed Stieltjes integrals agree when both integrator
and integrand agree on the finite prefix. No measure equality is postulated. -/
theorem stieltjes_integral_congr_on_prefix
    (b : ℝ) (hb : 0 ≤ b) (Q R H K : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc 0 b)) (hR : MonotoneOn R (Icc 0 b))
    (hrQ : ∀ x, x ∈ Icc 0 b → ContinuousWithinAt Q (Icc 0 b ∩ Ici x) x)
    (hrR : ∀ x, x ∈ Icc 0 b → ContinuousWithinAt R (Icc 0 b ∩ Ici x) x)
    (heQ : ∀ x ∈ Icc 0 b, Q x = R x) (heH : ∀ x ∈ Icc 0 b, H x = K x)
    (t : ℝ) :
    (∫ x in Iic t, H x ∂(intervalStieltjes 0 b hb Q hQ hrQ).measure) =
    (∫ x in Iic t, K x ∂(intervalStieltjes 0 b hb R hR hrR).measure) := by
  have hμ := interval_stieltjes_measure_congr_add_const 0 b hb R Q hR hQ hrR hrQ 0
    (fun x hx => by simpa only [add_zero] using heQ x hx)
  rw [hμ]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (interval_stieltjes_ae_mem_Ioc 0 b hb R hR hrR)] with x hx
  exact heH x ⟨hx.1.le,hx.2⟩

/-- A countable collection of local assertions transfers to a common
probability-one event, and on each finite prefix any sufficiently late
localizer may be used. -/
theorem ae_local_assertion_transfer
    {Ω ι : Type*} [MeasurableSpace Ω] [LinearOrder ι] [OrderTop ι]
    (P : Measure Ω) (σ : ℕ → Ω → ι)
    (hco : ∀ ω b, b < ⊤ → ∃ n, b ≤ σ n ω)
    (A : ℕ → Ω → Prop) (B : Ω → ι → Prop)
    (hA : ∀ n, ∀ᵐ ω ∂P, A n ω)
    (hAB : ∀ n ω b, b ≤ σ n ω → A n ω → B ω b) :
    ∀ᵐ ω ∂P, ∀ b, b < ⊤ → B ω b := by
  filter_upwards [ae_all_iff.mpr hA] with ω hω
  intro b hb
  obtain ⟨n,hn⟩ := hco ω b hb
  exact hAB n ω b hn (hω n)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.quadratic_sum_congr_on_prefix
#print axioms Asakura.Chapter3Complete.linear_sum_congr_on_prefix
#print axioms Asakura.Chapter3Complete.stieltjes_integral_congr_on_prefix
#print axioms Asakura.Chapter3Complete.ae_local_assertion_transfer
