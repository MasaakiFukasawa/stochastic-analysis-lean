import Chapter2ElementaryIntegral
import FullAuditCovarianceBilinear

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The product-minus-covariation calculation left as an exercise in 2.7.
It is decomposed into three elementary integrals, with coefficients known
at a or b. The identity is verified in all three time regions. -/
theorem elementary_product_covariance_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F) (a b : ClosedTime T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P) :
    ContinuousM2Witness P F (fun t ω =>
      G ω * (X.val (min b t) ω-X.val (min a t) ω) * Y.val t ω -
      G ω * (boundedCov P F hF hle hnull X Y (min b t) ω -
        boundedCov P F hF hle hnull X Y (min a t) ω)) := by
  let C := boundedCov P F hF hle hnull X Y
  let M := fun t ω => X.val t ω * Y.val t ω-C t ω
  have hM := bounded_cov_product_witness P F hF hle hnull X Y
  have h1 := elementary_integral_m2 P F hF hle M hM a b hab G hGm hG
  have h2 := elementary_integral_m2 P F hF hle Y.val Y.property.1 a b hab
    (fun ω => -G ω * X.val a ω) (hGm.neg.mul (X.property.1.adapted a))
    (hG.neg.mul (X.property.2 a))
  have h3 := elementary_integral_m2 P F hF hle Y.val Y.property.1 b ⊤ le_top
    (fun ω => G ω * (X.val b ω-X.val a ω))
    ((hGm.mono (hF hab) le_rfl).mul
      ((X.property.1.adapted b).sub ((X.property.1.adapted a).mono (hF hab) le_rfl)))
    (hG.mul ((X.property.2 b).sub (X.property.2 a)))
  have h := (h1.add P F h2).add P F h3
  convert h using 1
  funext t ω
  simp only [Pi.add_apply,M,min_top_left]
  by_cases hta : t ≤ a
  · simp only [min_eq_right hta,min_eq_right (hta.trans hab)]
    ring
  · have hat : a ≤ t := le_of_not_ge hta
    by_cases htb : t ≤ b
    · simp only [min_eq_left hat,min_eq_right htb]
      ring
    · simp only [min_eq_left hat,min_eq_left (le_of_not_ge htb)]
      ring

/-- Covariation identity for the elementary integral, using the actual
constructed bounded covariation and its verified uniqueness theorem. -/
theorem elementary_integral_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : boundedMProcess P F) (a b : ClosedTime T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P) :
    ∀ᵐ ω ∂P, ∀ t,
      boundedCov P F hF hle hnull
        ⟨_,elementary_integral_bounded_martingale P F hF hle X a b hab G hGm hG⟩ Y t ω =
      G ω * (boundedCov P F hF hle hnull X Y (min b t) ω -
        boundedCov P F hF hle hnull X Y (min a t) ω) := by
  let C := boundedCov P F hF hle hnull X Y
  have hA (ω) : ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, G ω * (C (min b t) ω-C (min a t) ω) = U t-V t := by
    obtain ⟨U,V,hU,hV,he⟩ := bounded_cov_in_A P F hF hle hnull X Y ω
    apply monotone_difference_smul
    refine ⟨(fun t => U (min b t)+V (min a t)),(fun t => V (min b t)+U (min a t)),
      (hU.comp (monotone_const.min monotone_id)).add (hV.comp (monotone_const.min monotone_id)),
      (hV.comp (monotone_const.min monotone_id)).add (hU.comp (monotone_const.min monotone_id)),?_⟩
    intro t
    dsimp only [C]
    rw [he,he]
    ring
  have h := bounded_cov_unique P F hF hle hnull
    ⟨_,elementary_integral_bounded_martingale P F hF hle X a b hab G hGm hG⟩ Y _ hA
    (elementary_product_covariance_martingale P F hF hle hnull X Y a b hab G hGm hG)
  exact h.mono fun ω hω t => (hω t).symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_product_covariance_martingale
#print axioms Asakura.Chapter2Complete.elementary_integral_covariance
