import Chapter12DivergenceTrace

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Summing the actual coordinate Gaussian IBP identities gives the
finite-dimensional divergence formula, with integrability proved from
polynomial growth. -/
theorem finite_gaussian_divergence_duality {n : ℕ}
    (f : (Fin (n+1) → ℝ) → ℝ)
    (df u du : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i z y, HasDerivAt (fun x => f (i.insertNth x z))
      (df i (i.insertNth y z)) y)
    (hu : ∀ i z y, HasDerivAt (fun x => u i (i.insertNth x z))
      (du i (i.insertNth y z)) y)
    (hmf : Measurable f) (hpf : PolyGrowth f)
    (hmdf : ∀ i, Measurable (df i)) (hpdf : ∀ i, PolyGrowth (df i))
    (hmu : ∀ i, Measurable (u i)) (hpu : ∀ i, PolyGrowth (u i))
    (hmdu : ∀ i, Measurable (du i)) (hpdu : ∀ i, PolyGrowth (du i)) :
    (∫ z, ∑ i, u i z * df i z ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, f z * (∑ i : Fin (n+1), (z i * u i z - du i z))
        ∂Measure.pi fun _ => gaussianReal 0 1 := by
  have hl i : Integrable (fun z => u i z*df i z)
      (Measure.pi fun _ => gaussianReal 0 1) :=
    polynomial_growth_gaussian_integrable ((hmu i).mul (hmdf i)) ((hpu i).mul (hpdf i))
  have hr i : Integrable (fun z => f z*(z i*u i z-du i z))
      (Measure.pi fun _ => gaussianReal 0 1) := by
    have h1 := polynomial_growth_gaussian_integrable
      (hmf.mul ((measurable_pi_apply i).mul (hmu i)))
      (hpf.mul ((polynomial_growth_coordinate i).mul (hpu i)))
    have h2 := polynomial_growth_gaussian_integrable (hmf.mul (hmdu i)) (hpf.mul (hpdu i))
    convert h1.sub h2 using 1
    ext z
    simp only [Pi.mul_apply,Pi.sub_apply,mul_sub]
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => hl i),
    integral_finset_sum _ (fun i _ => hr i)]
  apply Finset.sum_congr rfl
  intro i _
  exact gaussian_coordinate_ibp_polynomial i (hf i) (hu i) hmf (hmu i)
    (hmdf i) (hmdu i) hpf (hpu i) (hpdf i) (hpdu i)

/-- The product correction term is exactly the coordinate product rule;
this also fixes the sign of the anticipating-integral correction. -/
theorem finite_divergence_product {ι : Type*} [Fintype ι]
    (G : ℝ) (DG u du z : ι → ℝ) :
    (∑ i : ι, (z i*(G*u i)-(DG i*u i+G*du i))) =
      G*(∑ i : ι, (z i*u i-du i))-∑ i,DG i*u i := by
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Asakura.Chapter12
