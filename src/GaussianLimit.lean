import L2Moments
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Gaussian random vectors are closed under L2 limits. -/
theorem gaussian_L2_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : ℕ → Lp E 2 P} {g : Lp E 2 P}
    (hf : ∀ n, HasGaussianLaw (f n) P) (h : Tendsto f atTop (𝓝 g)) :
    HasGaussianLaw g P := by
  apply (hasGaussianLaw_iff_charFun_map_eq (Lp.aestronglyMeasurable g).aemeasurable).mpr
  intro t
  have hd := (tendstoInMeasure_of_tendsto_Lp h).tendstoInDistribution
    (fun n => (Lp.aestronglyMeasurable (f n)).aemeasurable)
  have hc := hd.tendsto_charFun t
  have hm := L2_projected_moments_tendsto h t
  have he : Tendsto (fun n => Complex.exp
      ((((∫ ω, inner ℝ t (f n ω) ∂P) : ℝ) : ℂ) * Complex.I -
        (Var[fun ω => inner ℝ t (f n ω); P] : ℂ) / 2)) atTop
      (𝓝 (Complex.exp ((((∫ ω, inner ℝ t (g ω) ∂P) : ℝ) : ℂ) * Complex.I -
        (Var[fun ω => inner ℝ t (g ω); P] : ℂ) / 2))) := by
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hm.1).mul_const Complex.I |>.sub
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp hm.2).div_const 2))
  simp_rw [HasGaussianLaw.charFun_map_eq t (hf _)] at hc
  exact tendsto_nhds_unique hc he

/-- The same closure result for normed targets, by all real linear projections. -/
theorem gaussian_L2_limit_normed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : ℕ → Lp E 2 P} {g : Lp E 2 P}
    (hf : ∀ n, HasGaussianLaw (f n) P) (h : Tendsto f atTop (𝓝 g)) :
    HasGaussianLaw g P := by
  refine ⟨(Lp.aestronglyMeasurable g).aemeasurable, ?_⟩
  apply isGaussian_of_isGaussian_map
  intro L
  have hn (n : ℕ) : HasGaussianLaw (L.compLp (f n)) P :=
    ((hf n).map L).congr (L.coeFn_compLp' (f n)).symm
  have hg : HasGaussianLaw (L.compLp g) P := gaussian_L2_limit hn
    (((L.compLpL (p := 2) (μ := P)).continuous.tendsto g).comp h)
  have hg' := hg.congr (L.coeFn_compLp g)
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable
    (Lp.aestronglyMeasurable g).aemeasurable]
  exact hg'.isGaussian_map
end Asakura
