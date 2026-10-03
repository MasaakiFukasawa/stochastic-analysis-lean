import BrownianHilbert
import GaussianFourierL2
import GaussianSeries
import L2Vector
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def normalLp (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (n : ℕ) : Lp ℝ 2 P :=
  (standard_gaussian_memLp (hX n)).toLp (X n)

noncomputable def fourierProcess (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (t : ℝ) : Ω → ℝ :=
  ⇑(brownianHilbert (normalLp X hX) t : Lp ℝ 2 P)

lemma fourier_process_gaussian (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (hI : iIndepFun X P) :
    IsGaussianProcess (fourierProcess X hX) P := by
  classical
  constructor
  intro I
  let v := normalLp X hX
  have hv : Orthonormal ℝ v := independent_standard_gaussians_orthonormal X hX hI
  let w (n : ℕ) : Lp (I → ℝ) 2 P := L2vector (fun t : I => brownianCoefficient t n • v n)
  let L (n : ℕ) : ℝ →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun t : I => brownianCoefficient t n • ContinuousLinearMap.id ℝ ℝ)
  have he (n : ℕ) : (w n : Ω → I → ℝ) =ᵐ[P] (L n) ∘ X n := by
    have ha : ∀ᵐ ω ∂P, ∀ t : I,
        (brownianCoefficient t n • v n : Lp ℝ 2 P) ω = brownianCoefficient t n * X n ω := by
      apply ae_all_iff.mpr
      intro t
      filter_upwards [Lp.coeFn_smul (brownianCoefficient t n) (v n),
        (standard_gaussian_memLp (hX n)).coeFn_toLp] with ω h₁ h₂
      simpa [v, normalLp, h₂] using h₁
    filter_upwards [L2vector_coe (fun t : I => brownianCoefficient t n • v n), ha] with ω h₁ h₂
    rw [h₁]
    ext t
    exact h₂ t
  have hG (n : ℕ) : HasGaussianLaw (w n) P :=
    ((hX n).hasGaussianLaw.map (L n)).congr (he n).symm
  have hJ : iIndepFun (fun n => (w n : Ω → I → ℝ)) P :=
    (hI.comp (fun n => (L n)) (fun n => (L n).continuous.measurable)).congr
      (fun n => (he n).symm)
  have hs : HasSum w (L2vector (fun t : I => brownianHilbert v t)) :=
    L2vector_hasSum _ _ (fun t => (brownian_hilbert_summable v hv t).hasSum)
  have hg := gaussian_L2_series w hG hJ hs.summable
  rw [hs.tsum_eq] at hg
  exact hg.congr (L2vector_coe (fun t : I => brownianHilbert v t))

lemma fourier_process_mean (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (hI : iIndepFun X P) (t : ℝ) :
    (∫ ω, fourierProcess X hX t ω ∂P) = 0 := by
  let v := normalLp X hX
  have hv : Orthonormal ℝ v := independent_standard_gaussians_orthonormal X hX hI
  have hm (n : ℕ) : (∫ ω, v n ω ∂P) = 0 := by
    change (∫ ω, (standard_gaussian_memLp (hX n)).toLp (X n) ω ∂P) = 0
    rw [integral_congr_ae (standard_gaussian_memLp (hX n)).coeFn_toLp,
      (hX n).integral_eq, integral_id_gaussianReal]
  let M : Lp ℝ 2 P →L[ℝ] ℝ := innerSL ℝ
    ((memLp_const (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ)))
  have h := M.hasSum (brownian_hilbert_summable v hv t).hasSum
  have hz : ∀ n, M (brownianCoefficient t n • v n) = 0 := by
    intro n
    rw [map_smul]
    change brownianCoefficient t n * inner ℝ _ (v n) = 0
    rw [← L2_mean_inner, hm, mul_zero]
  simp_rw [hz] at h
  have he := h.unique (hasSum_zero (β := ℕ) (α := ℝ))
  change inner ℝ _ (brownianHilbert v t) = 0 at he
  rw [← L2_mean_inner] at he
  exact he

lemma fourier_process_covariance (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) (gaussianReal 0 1) P) (hI : iIndepFun X P)
    (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    (∫ ω, fourierProcess X hX s ω * fourierProcess X hX t ω ∂P) = min s t := by
  have h := brownian_hilbert_inner (normalLp X hX)
    (independent_standard_gaussians_orthonormal X hX hI) s t hs ht
  simpa [L2.inner_def, fourierProcess, mul_comm] using h
end Asakura
