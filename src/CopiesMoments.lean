import GaussianCopies
import BrownianCube

open MeasureTheory ProbabilityTheory
namespace Asakura
variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
  {P : Measure Ω} {Q : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

lemma copies_mean (Y : UnitCube 1 → Ω₀ → ℝ) (hYm : ∀ t, Measurable (Y t))
    (hm : ∀ t, (∫ ω, Y t ω ∂Q) = 0)
    (ξ : ℕ → Ω → Ω₀) (hξ : ∀ k, HasLaw (ξ k) Q P) (k : ℕ) (t : UnitCube 1) :
    (∫ ω, Y t (ξ k ω) ∂P) = 0 :=
  ((hξ k).integral_comp (hYm t).aestronglyMeasurable).trans (hm t)

lemma copies_covariance (Y : UnitCube 1 → Ω₀ → ℝ) (hYm : ∀ t, Measurable (Y t))
    (hG : IsGaussianProcess Y Q) (hm : ∀ t, (∫ ω, Y t ω ∂Q) = 0)
    (hc : ∀ s t, (∫ ω, Y s ω * Y t ω ∂Q) = min (s.val 0) (t.val 0))
    (ξ : ℕ → Ω → Ω₀) (hξ : ∀ k, HasLaw (ξ k) Q P) (hI : iIndepFun ξ P)
    (k l : ℕ) (s t : UnitCube 1) :
    cov[Y s ∘ ξ k, Y t ∘ ξ l; P] = if k = l then min (s.val 0) (t.val 0) else 0 := by
  have hL (u : UnitCube 1) := (hG.hasGaussianLaw_eval u).memLp_two
  split_ifs with h
  · subst l
    rw [(hξ k).covariance_comp (hYm s).aemeasurable (hYm t).aemeasurable,
      covariance_eq_sub (hL s) (hL t), hm, hm, zero_mul, sub_zero]
    exact hc s t
  · exact ((hI.indepFun h).comp (hYm s) (hYm t)).covariance_eq_zero
      ((hξ k).memLp_comp (hL s)) ((hξ l).memLp_comp (hL t))
end Asakura
