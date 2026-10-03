import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory Set Finset ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem finite_product_real_density {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i,IsFiniteMeasure (μ i)] (g : ι → ℝ → ℝ)
    (hm : ∀ i,Measurable (g i)) (hi : ∀ i,Integrable (g i) volume)
    (hp : ∀ i x,0≤g i x) (he : ∀ i,μ i=volume.withDensity (fun x => ENNReal.ofReal (g i x))) :
    Measure.pi μ=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i,g i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),volume_pi,Measure.restrict_pi_pi]
  rw [←ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod (fun i => (hi i).restrict))
    (ae_of_all _ (fun x => prod_nonneg (fun i _ => hp i (x i)))),integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hp i))]
  apply prod_congr rfl
  intro i _
  rw [he i,withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi i).restrict (ae_of_all _ (hp i))

theorem independent_gaussian_density {d : ℕ} (t : ℝ≥0) (ht : t≠0) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 t)=
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i,gaussianPDFReal 0 t (x i))) := by
  apply finite_product_real_density _ _ (fun _ => measurable_gaussianPDFReal _ _)
    (fun _ => integrable_gaussianPDFReal _ _) (fun _ => gaussianPDFReal_nonneg _ _)
  intro i
  exact gaussianReal_of_var_ne_zero _ ht

end Asakura.Chapter6
