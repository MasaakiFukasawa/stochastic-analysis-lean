import Chapter12LognormalVarianceMoments
import Chapter12FiniteGreekExponents
import Chapter6ProductDensity
import Chapter6GaussianDensityFormula

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.Chapter6
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem gaussian_integrable_to_lebesgue {d : ℕ} (v : ℝ≥0) (hv : 0<v)
    (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g (Measure.pi (fun _ : Fin d => gaussianReal 0 v))) :
    Integrable (fun z => g z*Real.exp (-(∑ i,(z i)^2)/(2*(v:ℝ)))) volume := by
  rw [independent_gaussian_density v (ne_of_gt hv)] at hg
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at hg
  let c := (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹^d
  have hc : c≠0 := by dsimp [c]; positivity
  have hh := hg.const_mul c⁻¹
  convert hh using 1
  funext z
  simp only [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)),smul_eq_mul]
  rw [gaussian_product_formula]
  change g z*_=c⁻¹*(c*_ *g z)
  field_simp

theorem gaussian_quadratic_payoff_envelope {d : ℕ} (s : ℝ) (hs : 0<s)
    (f : (Fin d → ℝ) → ℝ)
    (hf : MemLp f 2 (Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨8*s^2,by positivity⟩))) :
    Integrable (fun z => |f z| *((1+∑ i,(z i)^2)*Real.exp (-(∑ i,(z i)^2)/(16*s^2)))) volume := by
  let v : ℝ≥0 := ⟨8*s^2,by positivity⟩
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 v)
  have hi (i : Fin d) : MemLp (fun z : Fin d → ℝ => (z i)^2) 2 μ := by
    have hh : MemLp (fun z : Fin d → ℝ => z i) 4 μ := by
      simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 4).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 v) i)
    convert hh.mul (r := 2) hh using 1
    funext z
    simp only [Pi.mul_apply,pow_two]
  have hsum : MemLp (fun z : Fin d → ℝ => ∑ i,(z i)^2) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hi i)
  have hq : MemLp (fun z : Fin d → ℝ => 1+∑ i,(z i)^2) 2 μ := by
    exact (memLp_const (μ := μ) (p := 2) (1:ℝ)).add hsum
  have hg := hf.norm.integrable_mul hq
  have hh := gaussian_integrable_to_lebesgue v (by change (0:ℝ)<8*s^2; positivity) _ hg
  convert hh using 1
  funext z
  change |f z| *((1+∑ i,(z i)^2)*Real.exp (-(∑ i,(z i)^2)/(16*s^2)))=
    (|f z| *(1+∑ i,(z i)^2))*Real.exp (-(∑ i,(z i)^2)/(2*(8*s^2)))
  have he : 2*(8*s^2)=16*s^2 := by ring
  rw [he]
  ring

end Asakura.Chapter12
