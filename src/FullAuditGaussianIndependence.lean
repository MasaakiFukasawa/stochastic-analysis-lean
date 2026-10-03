/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion

The characteristic-function proof of chap1 thm:gaussind, expanded locally.
Adapted from Mathlib's proof of the same factorization argument. The independence
conclusion is not obtained by calling its Gaussian independence theorem.
-/
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory ProbabilityTheory WithLp Complex Finset ContinuousLinearMap InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.FullAudit
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [MeasurableSpace F] [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]

theorem gaussian_independence_charFun_written [NormedSpace ℝ E] [NormedSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := hXY.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod hXY.fst.aemeasurable hXY.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
    ext; simp [-comp_apply, ← comp_inl_add_comp_inr]
  rw [hXY.charFunDual_map_eq, hXY.fst.charFunDual_map_eq, hXY.snd.charFunDual_map_eq, ← exp_add,
    sub_add_sub_comm, ← add_mul, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add, this,
    variance_add, h, mul_zero, add_zero]
  · simp
  · exact (hXY.fst.map _).memLp_two
  · exact (hXY.snd.map _).memLp_two
  · exact (hXY.fst.map _).integrable
  · exact (hXY.snd.map _).integrable

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
theorem gaussian_independence_inner_written [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  gaussian_independence_charFun_written hXY fun L₁ L₂ ↦ by
    simpa using! h ((toDual ℝ E).symm L₁) ((toDual ℝ F).symm L₂)

/-- If $((X_i)_{i \in \iota}, (Y_j)_{j \in \kappa})$ is Gaussian, then $(X_i)_{i \in \iota}$ and
$(Y_j)_{j \in \kappa}$ are independent if for all $i \in \iota, j \in \kappa$,
$\mathrm{Cov}(X_i, Y_j) = 0$. -/
theorem gaussian_independence_coordinates_written {ι κ : Type*} [Finite ι] [Finite κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  have := hXY.isProbabilityMeasure
  have hX : (fun ω i ↦ X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i ↦ X i ω)) := by ext; simp
  have hY : (fun ω j ↦ Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j ↦ Y j ω)) := by ext; simp
  rw [hX, hY]
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine IndepFun.comp (gaussian_independence_inner_written ?_ fun x y ↦ ?_)
    (by fun_prop) (by fun_prop)
  · exact hXY.map_equiv (.prodCongr (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm)
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i ↦ (hXY.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j ↦ (hXY.snd.eval j).memLp_two.const_mul _


/-- The printed zero-mean, zero-cross-moment assumptions imply the coordinate
covariance assumptions used in the displayed characteristic function. -/
theorem gaussian_independence_printed {d e : ℕ} {X : Fin d → Ω → ℝ} {Y : Fin e → Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (fun i => X i ω, fun j => Y j ω)) P)
    (hX : ∀ i, ∫ ω, X i ω ∂P = 0) (hY : ∀ j, ∫ ω, Y j ω ∂P = 0)
    (hcross : ∀ i j, ∫ ω, X i ω * Y j ω ∂P = 0) :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P := by
  have := hXY.isProbabilityMeasure
  apply gaussian_independence_coordinates_written hXY
  intro i j
  rw [covariance_eq_sub (hXY.fst.eval i).memLp_two (hXY.snd.eval j).memLp_two]
  simp [hX, hY, hcross]

end Asakura.FullAudit
