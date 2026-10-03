import GaussianSeries
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

open MeasureTheory ProbabilityTheory
namespace Asakura

lemma gaussian_finite_samples {Ω T ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : T → Ω → ℝ} (hG : IsGaussianProcess X P) [Fintype ι] (t : ι → T) :
    HasGaussianLaw (fun ω i => X (t i) ω) P := by
  classical
  let I := Finset.univ.image t
  let L : (I → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi
    (fun i => ContinuousLinearMap.proj ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  exact (hG.hasGaussianLaw I).map L

lemma gaussian_law_transfer {Ω Ω₀ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {Q : Measure Ω₀} {ξ : Ω → Ω₀} (hξ : HasLaw ξ Q P)
    {Y : Ω₀ → E} (hY : HasGaussianLaw Y Q) : HasGaussianLaw (Y ∘ ξ) P := by
  letI := hY.isGaussian_map
  exact (HasLaw.comp (show HasLaw Y (Q.map Y) Q from ⟨hY.aemeasurable,rfl⟩) hξ).hasGaussianLaw

/-- Independent copies of a Gaussian process are jointly Gaussian across all copies. -/
theorem independent_copies_gaussian {Ω Ω₀ T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {Q : Measure Ω₀} (Y : T → Ω₀ → ℝ)
    (hYm : ∀ t, Measurable (Y t)) (hG : IsGaussianProcess Y Q)
    (ξ : ℕ → Ω → Ω₀) (hξ : ∀ k, HasLaw (ξ k) Q P) (hI : iIndepFun ξ P) :
    IsGaussianProcess (fun p : ℕ × T => Y p.2 ∘ ξ p.1) P := by
  classical
  constructor
  intro I
  let K := I.image Prod.fst
  let A (k : K) : Ω₀ → I → ℝ := fun ω i => if i.val.1 = k.val then Y i.val.2 ω else 0
  have hA (k : K) : Measurable (A k) := by
    apply measurable_pi_lambda
    intro i
    by_cases h : i.val.1 = k.val <;> simp [A, h, hYm]
  have hAg (k : K) : HasGaussianLaw (A k) Q := by
    let L : (I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
      (fun i => if i.val.1 = k.val then ContinuousLinearMap.proj i else 0)
    have hg := (gaussian_finite_samples hG (fun i : I => i.val.2)).map L
    convert hg using 1
    ext ω i
    by_cases h : i.val.1 = k.val <;> simp [A, L, h]
  have hJ := (hI.precomp (g := fun k : K => k.val) Subtype.val_injective).comp A hA
  have hsum := hJ.hasGaussianLaw_fun_sum (fun k : K => gaussian_law_transfer (hξ k) (hAg k))
  convert hsum using 1
  ext ω i
  simp only [Function.comp_apply, Finset.sum_apply, A]
  have hi : i.val.1 ∈ K := Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩
  rw [Finset.sum_eq_single (⟨i.val.1,hi⟩ : K)]
  · simp
  · intro b hb hbi
    have hne : i.val.1 ≠ b.val := by
      intro he
      apply hbi
      exact Subtype.ext he.symm
    simp [hne]
  · simp
end Asakura
