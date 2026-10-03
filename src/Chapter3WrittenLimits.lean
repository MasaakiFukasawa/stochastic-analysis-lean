import Chapter2WrittenCorrections
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Written

/-- Polarization used in the first proposition, including its normalization. -/
theorem polarization (x y : ℝ) : x*y = ((x+y)/2)^2 - ((x-y)/2)^2 := by ring

/-- A partition controlling two paths also controls their half-sum. -/
theorem half_sum_oscillation {x y δ : ℝ} (hx : |x| ≤ δ) (hy : |y| ≤ δ) :
    |(x+y)/2| ≤ δ := by
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := abs_add_le x y
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  linarith

/-- Weighted finite-variation error. The partition sum is bounded BY variation. -/
theorem weighted_variation_error {ι : Type*} (s : Finset ι) (h a : ι → ℝ)
    {δ K V : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hh : ∀ j ∈ s, |h j| ≤ K) (ha : ∀ j ∈ s, |a j| ≤ δ)
    (hv : ∑ j ∈ s, |a j| ≤ V) :
    ∑ j ∈ s, |h j| * (a j)^2 ≤ K * (δ * V) := by
  calc
    _ ≤ ∑ j ∈ s, K * (a j)^2 := Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (hh j hj) (sq_nonneg _)
    _ = K * ∑ j ∈ s, (a j)^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (δ * V) := mul_le_mul_of_nonneg_left
      (Asakura.Chapter2Written.variation_square_sum s a hδ ha hv) hK

/-- The mixed finite-variation/martingale term vanishes once the quadratic
martingale sum converges. The Cauchy--Schwarz estimate is an explicit input. -/
theorem mixed_term_vanishes {a b c : ℕ → ℝ} {B : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 B))
    (hcs : ∀ n, (c n)^2 ≤ a n * b n) :
    Tendsto c atTop (𝓝 0) := by
  have hs : Tendsto (fun n => (c n)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) hcs
    simpa using ha.mul hb
  have ht := hs.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

/-- This is the actual Tonelli argument in both discrete approximation proofs:
finite expected sum of errors implies pathwise convergence, with no subsequence. -/
theorem summable_expected_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (e : ℕ → Ω → ℝ)
    (he : ∀ n, AEStronglyMeasurable (e n) μ)
    (hi : ∑' n, ∫⁻ ω, ‖e n ω‖ₑ ∂μ ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => e n ω) atTop (𝓝 0) := by
  have hm n : AEMeasurable (fun ω => ‖e n ω‖ₑ) μ := (he n).enorm
  have hsum : (∫⁻ ω, ∑' n, ‖e n ω‖ₑ ∂μ) ≠ ∞ := by
    rwa [lintegral_tsum hm]
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hsum] with ω hω
  have hs : Summable (fun n => (‖e n ω‖₊ : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hω.ne
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hs.tendsto_atTop_zero

/-- Summing the Taylor remainder estimates as printed in the Ito proof. -/
theorem sum_remainder_bound {ι : Type*} (s : Finset ι) (r dx : ι → ℝ)
    (ε : ℝ) (hr : ∀ j ∈ s, |r j| ≤ ε * (dx j)^2) :
    |∑ j ∈ s, r j| ≤ ε * ∑ j ∈ s, (dx j)^2 := by
  calc
    _ ≤ ∑ j ∈ s, |r j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, ε * (dx j)^2 := Finset.sum_le_sum hr
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Final limiting step of the Ito proof, including a possibly random (fixed
path) finite quadratic variation q. Identification of the stochastic sums is
NOT assumed to have been formalized by this lemma. -/
theorem ito_limit_identification {u v Q ε : ℕ → ℝ} {F I J q : ℝ}
    (hu : Tendsto u atTop (𝓝 I)) (hv : Tendsto v atTop (𝓝 J))
    (hQ : Tendsto Q atTop (𝓝 q)) (hε : Tendsto ε atTop (𝓝 0))
    (hr : ∀ n, |F-u n-v n/2| ≤ ε n * Q n) : F = I+J/2 := by
  have hz : Tendsto (fun n => |F-u n-v n/2|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) hr
    simpa using hε.mul hQ
  have hl : Tendsto (fun n => |F-u n-v n/2|) atTop (𝓝 |F-I-J/2|) :=
    ((tendsto_const_nhds.sub hu).sub (hv.div_const 2)).abs
  have he := tendsto_nhds_unique hl hz
  have := abs_eq_zero.mp he
  linarith

/-- Continuous paths cannot have increments bounded away from zero at an
INTERIOR accumulation time. No continuity at the excluded endpoint T is used. -/
theorem no_interior_oscillation_accumulation {x : ℝ → ℝ} {t : ℝ}
    (hx : ContinuousAt x t) {u v : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 t)) (hv : Tendsto v atTop (𝓝 t))
    {δ : ℝ} (hδ : 0 < δ) (hinc : ∀ᶠ n in atTop, δ ≤ |x (u n)-x (v n)|) : False := by
  have ht : Tendsto (fun n => |x (u n)-x (v n)|) atTop (𝓝 0) := by
    simpa using ((hx.tendsto.comp hu).sub (hx.tendsto.comp hv)).abs
  have : δ ≤ 0 := ge_of_tendsto ht hinc
  linarith

/-- Final stopped-martingale argument: pass equality of the localized test
integrals to the limit using the integrable running maximum as dominator.
The stopping-time identities and the BDG bound are explicit inputs. -/
theorem localized_test_integrals_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : ℕ → Ω → ℝ) (F G B : Ω → ℝ)
    (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n))
    (hF : Measurable F) (hG : Measurable G) (hB : Measurable B)
    (hiB : Integrable B μ)
    (hbF : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ B ω)
    (hbG : ∀ n, ∀ᵐ ω ∂μ, ‖g n ω‖ ≤ B ω)
    (hcF : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (hcG : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (G ω)))
    (he : ∀ n, (∫ ω, f n ω ∂μ) = ∫ ω, g n ω ∂μ) :
    (∫ ω, F ω ∂μ) = ∫ ω, G ω ∂μ := by
  have h1 := Asakura.manuscript_dominated_convergence μ f F B hf hF hB hiB hbF hcF
  have h2 := Asakura.manuscript_dominated_convergence μ g G B hg hG hB hiB hbG hcG
  have heq : (fun n => ∫ ω, f n ω ∂μ) = (fun n => ∫ ω, g n ω ∂μ) := funext he
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Asakura.Chapter3Written
