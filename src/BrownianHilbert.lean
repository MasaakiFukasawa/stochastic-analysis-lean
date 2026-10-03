import ManuscriptSineSeries
import FourierL2

open Set Filter
open scoped Topology
namespace Asakura

noncomputable def brownianCoefficient (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then t else fourierCoefficient t n

lemma brownian_coefficients_square_summable (t : ℝ) :
    Summable (fun n => ‖brownianCoefficient t n‖ ^ 2) := by
  apply (fourier_coefficients_square_summable t).congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℕ)] with n hn
  simp [brownianCoefficient, hn]

lemma brownian_coefficient_product (s t : ℝ) (n : ℕ) :
    fourierCoefficient s n * fourierCoefficient t n =
      2 * Real.sin (Real.pi * n * s) * Real.sin (Real.pi * n * t) /
        (Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  unfold fourierCoefficient
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = (Real.sqrt 2 * Real.sqrt 2) * Real.sin (Real.pi * n * s) *
        Real.sin (Real.pi * n * t) / (Real.pi ^ 2 * (n : ℝ) ^ 2) := by ring
    _ = _ := by rw [h]

lemma brownian_coefficient_covariance (s t : ℝ) (hs : s ∈ Icc 0 1)
    (ht : t ∈ Icc 0 1) :
    HasSum (fun n => brownianCoefficient s n * brownianCoefficient t n) (min s t) := by
  have h : HasSum (fun n => fourierCoefficient s n * fourierCoefficient t n)
      (min s t - s * t) := by
    simpa only [brownian_coefficient_product] using manuscript_sine_covariance s t hs ht
  have hh := h.update 0 (s * t)
  have he : Function.update (fun n => fourierCoefficient s n * fourierCoefficient t n)
      0 (s * t) = (fun n => brownianCoefficient s n * brownianCoefficient t n) := by
    funext n
    by_cases hn : n = 0 <;> simp [brownianCoefficient, hn]
  rw [he] at hh
  simpa [fourierCoefficient] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma brownian_hilbert_summable (v : ℕ → E) (hv : Orthonormal ℝ v) (t : ℝ) :
    Summable (fun n => brownianCoefficient t n • v n) := by
  simpa using (hv.orthogonalFamily.summable_iff_norm_sq_summable
    (brownianCoefficient t)).mpr (brownian_coefficients_square_summable t)

noncomputable def brownianHilbert (v : ℕ → E) (t : ℝ) : E :=
  ∑' n, brownianCoefficient t n • v n

/-- Covariance calculation for the full Fourier construction, including t ξ₀. -/
theorem brownian_hilbert_inner (v : ℕ → E) (hv : Orthonormal ℝ v)
    (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    inner ℝ (brownianHilbert v s) (brownianHilbert v t) = min s t := by
  have h₁ := (brownian_hilbert_summable v hv s).hasSum
  have h₂ := (brownian_hilbert_summable v hv t).hasSum
  have hh := h₁.inner h₂ (𝕜 := ℝ)
  have he (F : Finset ℕ) := hv.inner_sum (brownianCoefficient s) (brownianCoefficient t) F
  simp only [RCLike.conj_to_real] at he
  simp only [he] at hh
  exact tendsto_nhds_unique hh (brownian_coefficient_covariance s t hs ht)
end Asakura
