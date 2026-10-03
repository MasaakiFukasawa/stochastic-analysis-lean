import Chapter7OriginalEstimatorScalarCLT
import Chapter7SymmetricContraction
import Chapter7CramerWold

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedEstimatorMatrix {Ω : Type*} {d : ℕ}
    (X : Fin d → ℝ → Ω → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) (n : ℕ) (w : Ω) :
    EuclideanSpace ℝ (Fin d × Fin d) := WithLp.toLp 2 (fun p => Real.sqrt (n:ℝ)*
      (realizedProcessEntry (X p.1) (X p.2) T n w-(S*S.transpose) p.1 p.2))

lemma realized_entry_symmetric {Ω : Type*} (X Y : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (w : Ω) :
    realizedProcessEntry X Y T n w=realizedProcessEntry Y X T n w := by
  dsimp [realizedProcessEntry]
  congr 1
  apply sum_congr rfl
  intro k _
  ring

lemma normalized_estimator_symmetric {Ω : Type*} {d : ℕ}
    (X : Fin d → ℝ → Ω → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) (n : ℕ) (w : Ω) (i j : Fin d) :
    normalizedEstimatorMatrix X S T n w (i,j)=normalizedEstimatorMatrix X S T n w (j,i) := by
  have hs : (S*S.transpose).transpose=S*S.transpose := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  change Real.sqrt (n:ℝ)*(_-_)=Real.sqrt (n:ℝ)*(_-_)
  rw [realized_entry_symmetric (X i) (X j),← congrFun (congrFun hs i) j]
  rfl

/-- The actual matrix estimator, including singular Gaussian limits. -/
theorem original_estimator_matrix_clt {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (Baux : BrownianSystem Q 1)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b : Fin d → ℝ → Ω → ℝ) (x : Fin d → Ω → ℝ)
    (hbc : ∀ i w,Continuous (fun r => b i r w))
    (hba : ∀ i r,r∈Icc 0 T → Measurable[B.F (realTimeClamp r)] (b i r))
    (hbb : ∀ i r,r∈Icc 0 T → ∀ w,|b i r w|≤K) (hx : ∀ i,Measurable (x i)) :
    TendstoInDistribution (fun n => normalizedEstimatorMatrix
      (fun i => driftedProjectionProcess B (S i) (b i) (x i)) S T (n+1)) atTop
      id (fun _ => P) (estimatorGaussianLaw S) := by
  let X := fun i => driftedProjectionProcess B (S i) (b i) (x i)
  have hXm i t (ht : t∈Icc 0 T) : Measurable (X i t) :=
    drifted_projection_measurable B (S i) (b i) (x i) T hT.le
      (fun w => (hbc i w).continuousOn) (fun r hr => (hba i r hr).mono (B.le _) le_rfl) (hx i) t ht
  have hmeas n : Measurable (normalizedEstimatorMatrix X S T (n+1)) := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro p
    exact measurable_const.mul ((realized_process_entry_measurable (X p.1) (X p.2) T hT
      (hXm p.1) (hXm p.2) n).sub_const _)
  apply cramer_wold_euclidean P (estimatorGaussianLaw S) _ id
    (fun n => (hmeas n).aemeasurable) measurable_id.aemeasurable
  intro v
  let V : Matrix (Fin d) (Fin d) ℝ := fun i j => v (i,j)
  let H := symmetrizedMatrix V
  have hd := original_estimator_scalar_clt P Q B Baux H S (symmetrized_matrix_symmetric V)
    T K hT hK b x hbc hba hbb hx
  apply hd.congr
  · intro n
    apply ae_of_all
    intro w
    have he := symmetrized_contraction V (fun i j => normalizedEstimatorMatrix X S T (n+1) w (i,j))
      (normalized_estimator_symmetric X S T (n+1) w)
    have hi : inner ℝ (normalizedEstimatorMatrix X S T (n+1) w) v=
        ∑ i,∑ j,V i j*normalizedEstimatorMatrix X S T (n+1) w (i,j) := by
      simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_prod_type,V]
    change Real.sqrt ((n+1:ℕ):ℝ)*(∑ i,∑ j,H i j*(realizedProcessEntry (X i) (X j) T (n+1) w-(S*S.transpose) i j)) = inner ℝ (normalizedEstimatorMatrix X S T (n+1) w) v
    rw [hi,← he]
    dsimp only [H,normalizedEstimatorMatrix]
    simp only [mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  · filter_upwards [(estimator_gaussian_matrix P B S).2.2] with g hg
    have he := symmetrized_contraction V (fun i j => g (i,j)) hg
    change (∑ i,∑ j,H i j*g (i,j))=inner ℝ g v
    rw [he]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_prod_type,V]

end Asakura.Chapter7
