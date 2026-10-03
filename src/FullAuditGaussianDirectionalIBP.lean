import FullAuditGaussianProductIBP
import FullAuditGaussianGrowth
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- The finite-dimensional Gaussian identity with the manuscript's polynomial
 growth assumptions, including all integrability and coordinate Fubini steps. -/
theorem gaussian_coordinate_ibp_polynomial {n : ℕ} (i : Fin (n+1))
    {f g df dg : (Fin (n+1) → ℝ) → ℝ}
    (hf : ∀ z y, HasDerivAt (fun x => f (i.insertNth x z)) (df (i.insertNth y z)) y)
    (hg : ∀ z y, HasDerivAt (fun x => g (i.insertNth x z)) (dg (i.insertNth y z)) y)
    (hmf : Measurable f) (hmg : Measurable g) (hmdf : Measurable df) (hmdg : Measurable dg)
    (hpf : PolyGrowth f) (hpg : PolyGrowth g) (hpdf : PolyGrowth df) (hpdg : PolyGrowth dg) :
    (∫ z, g z*df z ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, f z*(z i*g z-dg z) ∂Measure.pi fun _ => gaussianReal 0 1 := by
  apply gaussian_finite_coordinate_ibp i hf hg
  · exact polynomial_growth_gaussian_integrable (hmf.mul hmg) (hpf.mul hpg)
  · exact polynomial_growth_gaussian_integrable (hmg.mul hmdf) (hpg.mul hpdf)
  · exact polynomial_growth_gaussian_integrable (hmf.mul hmdg) (hpf.mul hpdg)
  · exact polynomial_growth_gaussian_integrable (((measurable_pi_apply i).mul hmf).mul hmg)
      (((polynomial_growth_coordinate i).mul hpf).mul hpg)

/-- Sum the coordinate formulas in a deterministic direction. -/
theorem gaussian_directional_ibp_polynomial {n : ℕ}
    {f g : (Fin (n+1) → ℝ) → ℝ}
    {df dg : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    (hf : ∀ i z y, HasDerivAt (fun x => f (i.insertNth x z)) (df i (i.insertNth y z)) y)
    (hg : ∀ i z y, HasDerivAt (fun x => g (i.insertNth x z)) (dg i (i.insertNth y z)) y)
    (hmf : Measurable f) (hmg : Measurable g)
    (hmdf : ∀ i, Measurable (df i)) (hmdg : ∀ i, Measurable (dg i))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ i, PolyGrowth (df i)) (hpdg : ∀ i, PolyGrowth (dg i)) (a : Fin (n+1) → ℝ) :
    (∫ z, g z*(∑ i, a i*df i z) ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, f z*((∑ i, a i*z i)*g z-∑ i, a i*dg i z)
        ∂Measure.pi fun _ => gaussianReal 0 1 := by
  have hleft i : Integrable (fun z => a i*(g z*df i z)) (Measure.pi fun _ => gaussianReal 0 1) :=
    (polynomial_growth_gaussian_integrable (hmg.mul (hmdf i)) (hpg.mul (hpdf i))).const_mul _
  have hright i : Integrable (fun z => a i*(f z*(z i*g z-dg i z)))
      (Measure.pi fun _ => gaussianReal 0 1) := by
    have h1 := polynomial_growth_gaussian_integrable
      (((measurable_pi_apply i).mul hmf).mul hmg) (((polynomial_growth_coordinate i).mul hpf).mul hpg)
    have h2 := polynomial_growth_gaussian_integrable (hmf.mul (hmdg i)) (hpf.mul (hpdg i))
    have h3 : Integrable (fun z => f z*(z i*g z-dg i z)) (Measure.pi fun _ => gaussianReal 0 1) := by
      convert h1.sub h2 using 1
      ext z; simp only [Pi.sub_apply,Pi.mul_apply]; ring
    exact h3.const_mul _
  have hl (z : Fin (n+1) → ℝ) : g z*(∑ i, a i*df i z) = ∑ i, a i*(g z*df i z) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hr (z : Fin (n+1) → ℝ) :
      f z*((∑ i, a i*z i)*g z-∑ i, a i*dg i z) = ∑ i, a i*(f z*(z i*g z-dg i z)) := by
    simp only [Finset.sum_mul,mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  simp_rw [hl,hr]
  rw [integral_finset_sum _ (fun i _ => hleft i),integral_finset_sum _ (fun i _ => hright i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,integral_const_mul,
    gaussian_coordinate_ibp_polynomial i (hf i) (hg i) hmf hmg (hmdf i) (hmdg i) hpf hpg (hpdf i) (hpdg i)]

end Asakura.FullAudit
