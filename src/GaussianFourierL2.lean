import FourierL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma standard_gaussian_memLp {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) :
    MemLp X 2 P := hX.memLp (memLp_id_gaussianReal' 2 (by norm_num))

lemma independent_standard_gaussians_orthonormal (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (hI : iIndepFun X P) :
    Orthonormal ℝ (fun n => (standard_gaussian_memLp (hX n)).toLp (X n)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_def]
  have he : (∫ ω, inner ℝ ((standard_gaussian_memLp (hX i)).toLp (X i) ω)
        ((standard_gaussian_memLp (hX j)).toLp (X j) ω) ∂P) =
      ∫ ω, X i ω * X j ω ∂P := by
    apply integral_congr_ae
    filter_upwards [(standard_gaussian_memLp (hX i)).coeFn_toLp,
      (standard_gaussian_memLp (hX j)).coeFn_toLp] with ω hi hj
    simp [hi, hj, mul_comm]
  rw [he]
  have hm : ∀ n, (∫ ω, X n ω ∂P) = 0 := by
    intro n
    rw [(hX n).integral_eq, integral_id_gaussianReal]
  split_ifs with hij
  · subst j
    have hv := (hX i).variance_eq
    rw [variance_id_gaussianReal, variance_eq_sub (standard_gaussian_memLp (hX i)), hm] at hv
    simpa [pow_two] using hv
  · rw [(hI.indepFun hij).integral_fun_mul_eq_mul_integral
      (standard_gaussian_memLp (hX i)).aestronglyMeasurable
      (standard_gaussian_memLp (hX j)).aestronglyMeasurable, hm, zero_mul]

/-- Fourier random series converges in L2 for independent standard normal variables. -/
theorem gaussian_fourier_L2_convergence (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (hI : iIndepFun X P) (t : ℝ) :
    Summable (fun n => fourierCoefficient t n •
      (standard_gaussian_memLp (hX n)).toLp (X n)) :=
  orthonormal_fourier_series_converges _ (independent_standard_gaussians_orthonormal X hX hI) t
end Asakura
