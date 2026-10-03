import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

open Matrix
open scoped Matrix BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 800000

/-- The log likelihood of the linear drift model, as a quadratic in theta. -/
noncomputable def quadraticLogLikelihood {n : Type*} [Fintype n]
    (I : Matrix n n ℝ) (b θ : n → ℝ) : ℝ := θ ⬝ᵥ b - (θ ⬝ᵥ (I *ᵥ θ))/2

lemma quadratic_likelihood_difference {n : Type*} [Fintype n]
    (I : Matrix n n ℝ) (hs : Iᵀ = I) (b v θ : n → ℝ) (hv : I *ᵥ v = b) :
    quadraticLogLikelihood I b θ - quadraticLogLikelihood I b v =
      -((θ-v) ⬝ᵥ (I *ᵥ (θ-v)))/2 := by
  have hsym : v ⬝ᵥ (I *ᵥ θ) = θ ⬝ᵥ (I *ᵥ v) := by
    simpa only [hs] using dotProduct_transpose_mulVec I v θ
  simp only [quadraticLogLikelihood,Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub]
  rw [hsym,hv]
  ring

/-- Positive definiteness, restricted to the event where it holds in the
manuscript, gives a unique maximizer rather than merely a stationary point. -/
theorem quadratic_likelihood_unique_maximum {n : Type*} [Fintype n] [DecidableEq n]
    (I : Matrix n n ℝ) (hI : I.PosDef) (b : n → ℝ) :
    (∀ θ,quadraticLogLikelihood I b θ ≤ quadraticLogLikelihood I b (I⁻¹ *ᵥ b)) ∧
    (∀ θ,quadraticLogLikelihood I b θ = quadraticLogLikelihood I b (I⁻¹ *ᵥ b) ↔
      θ = I⁻¹ *ᵥ b) := by
  have hs : Iᵀ = I := by simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hI.isHermitian
  have hi : IsUnit I.det := I.isUnit_iff_isUnit_det.mp hI.isUnit
  have hv : I *ᵥ (I⁻¹ *ᵥ b) = b := by rw [Matrix.mulVec_mulVec,I.mul_nonsing_inv hi,Matrix.one_mulVec]
  have hd θ := quadratic_likelihood_difference I hs b (I⁻¹ *ᵥ b) θ hv
  have hp (θ : n → ℝ) (hθ : θ ≠ I⁻¹ *ᵥ b) :
      0 < (θ-I⁻¹ *ᵥ b) ⬝ᵥ (I *ᵥ (θ-I⁻¹ *ᵥ b)) := by
    simpa only [star_trivial] using hI.dotProduct_mulVec_pos (sub_ne_zero.mpr hθ)
  constructor
  · intro θ
    by_cases hθ : θ = I⁻¹ *ᵥ b
    · rw [hθ]
    · have h := hp θ hθ
      linarith [hd θ]
  · intro θ
    constructor
    · intro he
      by_contra hn
      have h := hp θ hn
      linarith [hd θ]
    · rintro rfl
      rfl

/-- Substituting the true drift into the score gives the displayed estimation error. -/
theorem likelihood_estimator_error {n : Type*} [Fintype n] [DecidableEq n]
    (I : Matrix n n ℝ) (hI : I.PosDef) (θ noise : n → ℝ) :
    I⁻¹ *ᵥ (I *ᵥ θ + noise) - θ = I⁻¹ *ᵥ noise := by
  have hi : IsUnit I.det := I.isUnit_iff_isUnit_det.mp hI.isUnit
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,I.nonsing_inv_mul hi,Matrix.one_mulVec]
  abel

end Asakura.Chapter6
