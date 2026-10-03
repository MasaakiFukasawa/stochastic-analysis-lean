import GaussianLimit
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem gaussian_L2_series (v : ℕ → Lp E 2 P)
    (hv : ∀ n, HasGaussianLaw (v n) P) (hI : iIndepFun (fun n => (v n : Ω → E)) P)
    (hs : Summable v) : HasGaussianLaw (∑' n, v n : Lp E 2 P) P := by
  apply gaussian_L2_limit_normed (f := fun N => ∑ n ∈ Finset.range N, v n) _
    hs.hasSum.tendsto_sum_nat
  intro N
  have hJ := hI.precomp (g := fun n : Finset.range N => (n : ℕ)) Subtype.val_injective
  have hG := hJ.hasGaussianLaw_fun_sum (fun n : Finset.range N => hv n)
  have hG' : HasGaussianLaw (fun ω => ∑ n ∈ Finset.range N, v n ω) P := by
    have he : (fun ω => ∑ n : Finset.range N, v n ω) =
        (fun ω => ∑ n ∈ Finset.range N, v n ω) := by
      funext ω
      exact Finset.sum_coe_sort (Finset.range N) (fun n => v n ω)
    rw [he] at hG
    exact hG
  apply hG'.congr
  simpa only [Finset.sum_fn] using (Lp.coeFn_finsetSum (Finset.range N) v).symm

/-- Independent Gaussian inputs mapped by deterministic linear maps have Gaussian L2 sums. -/
theorem gaussian_linear_series {X : ℕ → Ω → ℝ}
    (hX : ∀ n, HasGaussianLaw (X n) P) (hI : iIndepFun X P)
    (L : ℕ → ℝ →L[ℝ] E)
    (hs : Summable (fun n => (L n).compLp ((hX n).memLp_two.toLp (X n)))) :
    HasGaussianLaw (∑' n, (L n).compLp ((hX n).memLp_two.toLp (X n)) : Lp E 2 P) P := by
  let v (n : ℕ) := (L n).compLp ((hX n).memLp_two.toLp (X n))
  have he (n : ℕ) : (v n : Ω → E) =ᵐ[P] (L n) ∘ X n := by
    exact ((L n).coeFn_compLp' _).trans
      ((hX n).memLp_two.coeFn_toLp.fun_comp (L n))
  apply gaussian_L2_series v _ _ hs
  · intro n
    exact ((hX n).map (L n)).congr (he n).symm
  · exact (hI.comp (fun n => (L n)) (fun n => (L n).continuous.measurable)).congr
      (fun n => (he n).symm)
end Asakura
