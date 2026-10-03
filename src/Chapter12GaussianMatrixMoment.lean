import Chapter12GaussianMomentPositive
import Chapter12FiniteMomentMinkowski
import Chapter12GaussianJetAlgebra

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The even moments of a Gaussian projection of a finite tensor are
bounded by its Hilbert--Schmidt norm, uniformly in both dimensions. -/
theorem gaussian_matrix_even_moment {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℝ) (p : ℕ) (hp : 0<p) :
    (∫ z : Fin n → ℝ,(Real.sqrt (∑ i,(∑ j,a i j*z j)^2))^(2*p)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
    gaussianEvenMoment p * (Real.sqrt (∑ i,∑ j,(a i j)^2))^(2*p) := by
  classical
  letI : Fact (1≤(p:ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let c := (gaussianEvenMoment p)^((p:ℝ)⁻¹)
  have hc : 0≤c := Real.rpow_nonneg (gaussian_even_moment_pos p).le _
  have hcp : c^p=gaussianEvenMoment p :=
    Real.rpow_inv_natCast_pow (gaussian_even_moment_pos p).le hp.ne'
  let f := fun i (z : Fin n → ℝ) => (∑ j,a i j*z j)^2
  let A := fun i => ∑ j,(a i j)^2
  have hA i : 0≤A i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hf i : MemLp (f i) (p:ℝ≥0∞) μ := by
    let g := GaussianJet.finsetSum Finset.univ (fun j => (GaussianJet.coordinate j).smul (a i j))
    have hh := (g.mul g).all_moments (p:ℝ≥0∞) (ENNReal.natCast_ne_top _)
    simpa only [GaussianJet.mul,g,GaussianJet.finsetSum,GaussianJet.smul,
      GaussianJet.coordinate,pow_two,f] using hh
  have hb i : (∫ z,(f i z)^p ∂μ)≤(c*A i)^p := by
    have hh := gaussian_projection_even_moment (a i) p
    simp only [pow_mul] at hh
    rw [Real.sq_sqrt (hA i)] at hh
    change (∫ z,((∑ j,a i j*z j)^2)^p ∂μ)≤(c*A i)^p
    rw [hh,mul_pow,hcp]
  have hbound := finite_moment_minkowski_bound μ p hp f hf
    (fun _ _ => sq_nonneg _) A hA c hc hb
  have hl (z : Fin n → ℝ) :
      (Real.sqrt (∑ i,(∑ j,a i j*z j)^2))^(2*p)=(∑ i,f i z)^p := by
    rw [pow_mul,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [show (Real.sqrt (∑ i,∑ j,(a i j)^2))^(2*p)=(∑ i,A i)^p by
    rw [pow_mul,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => hA i))]]
  simp only [hl]
  simpa only [mul_pow,hcp] using hbound

end Asakura.Chapter12
