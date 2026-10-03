import GaussianCopies
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.EndToEnd

/-- Independence of two entire Gaussian processes implies joint Gaussianity
of all their coordinates, including mixed finite samples. -/
theorem independent_gaussian_pair {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hI : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P) :
    IsGaussianProcess (Sum.elim X Y) P := by
  classical
  constructor
  intro S
  let a (q : S) := Sum.elim id (fun _ => (0 : ℝ≥0)) q.val
  let b (q : S) := Sum.elim (fun _ => (0 : ℝ≥0)) id q.val
  have hA := Asakura.gaussian_finite_samples hX a
  have hB := Asakura.gaussian_finite_samples hY b
  have hAB : IndepFun (fun ω q => X (a q) ω) (fun ω q => Y (b q) ω) P :=
    hI.comp (Measurable.of_eval fun q => measurable_pi_apply (a q))
      (Measurable.of_eval fun q => measurable_pi_apply (b q))
  let L : ((S → ℝ) × (S → ℝ)) →L[ℝ] (S → ℝ) :=
    ContinuousLinearMap.pi fun q => match q.val with
      | Sum.inl _ => (ContinuousLinearMap.proj q).comp (ContinuousLinearMap.fst ℝ _ _)
      | Sum.inr _ => (ContinuousLinearMap.proj q).comp (ContinuousLinearMap.snd ℝ _ _)
  convert (hAB.hasGaussianLaw hA hB).map L using 1
  ext ω q
  change Sum.elim X Y q.val ω = L ((fun q => X (a q) ω), (fun q => Y (b q) ω)) q
  cases hq : q.val <;> simp [L, a, b, hq]

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.independent_gaussian_pair
