import Chapter2CovarianceContinuity
import Chapter2ProbabilityErrorSum
import Chapter2LocalCovarianceCongruence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Expansion of the actual quadratic variation of X around Y, obtained
from proved bilinearity and uniqueness, rather than assumed as algebra. -/
theorem quadratic_variation_difference_expansion
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X Y A B R C : ClosedTime T → Ω → ℝ}
    (hA : LocalCovarianceWitness P F X X A)
    (hB : LocalCovarianceWitness P F Y Y B)
    (hR : LocalCovarianceWitness P F (fun t ω => X t ω-Y t ω) (fun t ω => X t ω-Y t ω) R)
    (hC : LocalCovarianceWitness P F (fun t ω => X t ω-Y t ω) Y C) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → A t ω-B t ω = R t ω+2*C t ω := by
  have h1 := (hR.bilinear P F hF hle (hC.symm P F) 1).symm P F
  have h2 := (hC.bilinear P F hF hle hB 1).symm P F
  have h := h1.bilinear P F hF hle h2 1
  have he : LocalCovarianceWitness P F X X (fun t ω => R t ω+2*C t ω+B t ω) := by
    convert h using 1 <;> (funext t ω; ring)
  filter_upwards [hA.unique P F hF hle he] with ω hω
  intro t ht
  have hh := hω t ht
  linarith

/-- Quadratic variation is continuous in local uniform probability for
actual continuous local martingales. All auxiliary covariations are
constructed using the previously proved existence theorem. -/
theorem quadratic_variation_probability_continuity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ℕ → ClosedTime T → Ω → ℝ) (Y B : ClosedTime T → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P F (X n)) (hY : LocalMProcessWitness P F Y)
    (hA : ∀ n, LocalCovarianceWitness P F (X n) (X n) (A n))
    (hB : LocalCovarianceWitness P F Y Y B)
    (t : ClosedTime T) (ht : t < ⊤)
    (hprob : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ⨆ s, |X n (min t s) ω-Y (min t s) ω|}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |A n t ω-B t ω|}) atTop (𝓝 0) := by
  classical
  let D := fun n t ω => X n t ω-Y t ω
  have hD n : LocalMProcessWitness P F (D n) := by
    have h := (hX n).add P F hF hle (hY.smul P F (-1))
    convert h using 1
    funext s ω
    dsimp [D]
    ring
  choose R hR using fun n => local_covariance_witness_exists P F hF hle hnull (D n) (D n) (hD n) (hD n)
  choose C hC using fun n => local_covariance_witness_exists P F hF hle hnull (D n) Y (hD n) hY
  have hstop : ∀ s, MeasurableSet[F s] {ω : Ω | t ≤ s} := by
    intro s
    by_cases hs : t ≤ s <;> simp [hs]
  have hRp := quadratic_variation_probability_of_local_martingale P F hF hle hnull
    D R hD hR (fun _ => t) hstop (fun _ => ht) hprob
  have hCp := local_covariance_probability_of_local_martingale P F hF hle hnull
    D R C Y B hD hY hR hB hC t ht hprob
  apply probability_error_sum_limit P (fun n ω => |A n t ω-B t ω|)
    (fun n ω => R n t ω) (fun n ω => |C n t ω|) 2 (by norm_num) _ hRp hCp ε hε
  intro n
  have he := quadratic_variation_difference_expansion P F hF hle (hA n) hB (hR n) (hC n)
  have hm := local_quadratic_variation_monotone P F hF hle hnull (D n) (R n) (hD n) (hR n)
  have h0 := local_quadratic_variation_initial P F (D n) (R n) (hD n) (hR n)
  filter_upwards [he,hm,h0] with ω heω hmω h0ω
  have hr0 : 0 ≤ R n t ω := by
    have h := hmω (show (⊥ : ClosedTime T) ∈ Iio ⊤ from (bot_le : (⊥ : ClosedTime T) ≤ t).trans_lt ht) ht bot_le
    simpa only [h0ω,Pi.zero_apply] using h
  rw [heω t ht]
  have h := abs_add_le (R n t ω) (2*C n t ω)
  rw [abs_of_nonneg hr0,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.quadratic_variation_difference_expansion
#print axioms Asakura.Chapter2Complete.quadratic_variation_probability_continuity
