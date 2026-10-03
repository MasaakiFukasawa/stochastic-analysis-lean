import FullAuditRegressionConditional
import FullAuditRegressionAlgebra
import Mathlib.Analysis.Matrix.PosDef

open MeasureTheory ProbabilityTheory Matrix
namespace Asakura.FullAudit

/-- Covariance of two actual linear combinations, expanded as the matrix product. -/
theorem gaussian_linear_covariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} {X : Ω → Fin d → ℝ} (hX : HasGaussianLaw X P) (a b : Fin d → ℝ) :
    cov[(fun ω => linearPredictor a (X ω)),(fun ω => linearPredictor b (X ω)); P] =
      dotProduct a ((Matrix.of fun i j => cov[(fun ω => X ω i),(fun ω => X ω j); P]) *ᵥ b) := by
  have := hX.isProbabilityMeasure
  have hb : MemLp (fun ω => ∑ i, b i * X ω i) 2 P := by
    simpa only [Function.comp_def,linearPredictor_apply] using (hX.map (linearPredictor b)).memLp_two
  simp_rw [linearPredictor_apply]
  rw [covariance_fun_sum_left (fun i => (hX.eval i).memLp_two.const_mul (a i))
    hb]
  simp_rw [covariance_const_mul_left,
    covariance_fun_sum_right (fun j => (hX.eval j).memLp_two.const_mul (b j)) (hX.eval _).memLp_two,
    covariance_const_mul_right]
  simp only [dotProduct,mulVec,Matrix.of_apply,Finset.mul_sum]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The covariance matrix used in the regression theorem is positive semidefinite. -/
theorem gaussian_covariance_posSemidef {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} {X : Ω → Fin d → ℝ} (hX : HasGaussianLaw X P) :
    Matrix.PosSemidef (Matrix.of fun i j => cov[(fun ω => X ω i),(fun ω => X ω j); P]) := by
  have := hX.isProbabilityMeasure
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    exact covariance_comm _ _
  · intro a
    simp only [star_trivial]
    have hm : AEMeasurable (fun ω => linearPredictor a (X ω)) P := (hX.map (linearPredictor a)).aemeasurable
    rw [← gaussian_linear_covariance P hX a a,covariance_self hm]
    exact variance_nonneg _ _

/-- The square-root factorization invoked in the printed kernel argument,
constructed from the spectral theorem and nonnegative eigenvalues. -/
theorem real_posSemidef_gram_factor {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.PosSemidef) :
    ∃ S : Matrix n n ℝ, C = S.transpose * S := by
  let U : Matrix n n ℝ := hC.isHermitian.eigenvectorUnitary
  let e := hC.isHermitian.eigenvalues
  have hs : C = U * diagonal e * U.transpose := by
    simpa only [U,e,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id, id_eq] using hC.isHermitian.spectral_theorem
  refine ⟨diagonal (fun i => Real.sqrt (e i)) * U.transpose,?_⟩
  rw [transpose_mul,transpose_transpose,diagonal_transpose,Matrix.mul_assoc,
    ← Matrix.mul_assoc (diagonal _) (diagonal _),diagonal_mul_diagonal]
  have he : (fun i => Real.sqrt (e i) * Real.sqrt (e i)) = e := by
    funext i
    exact Real.mul_self_sqrt (hC.eigenvalues_nonneg i)
  rw [he]
  simpa only [Matrix.mul_assoc] using hs

/-- Existence of precisely the nonnegative spectral data used to define M^-.
The matrix U is orthogonal even when some eigenvalues vanish. -/
theorem real_posSemidef_spectral {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    ∃ (U : Matrix n n ℝ) (e : n → ℝ),
      U.transpose * U = 1 ∧ (∀ i, 0 ≤ e i) ∧ M = U * diagonal e * U.transpose := by
  refine ⟨hM.isHermitian.eigenvectorUnitary,hM.isHermitian.eigenvalues,?_,hM.eigenvalues_nonneg,?_⟩
  · simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary
  · simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using hM.isHermitian.spectral_theorem

end Asakura.FullAudit
