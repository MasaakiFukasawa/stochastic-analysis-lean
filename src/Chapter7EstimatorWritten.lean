import Chapter7EstimatorFiniteDrift
import Chapter7FiniteVectorProbability
import Chapter7BrownianExists

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def realizedEstimatorMatrix {Ω : Type*} {d : ℕ}
    (X : Fin d → ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (w : Ω) : EuclideanSpace ℝ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p => realizedProcessEntry (X p.1) (X p.2) T n w)

/-- The manuscript's covariance estimator: norm consistency, matrix CLT,
mean, covariance and symmetry of the limit, with only finite-interval drift regularity. -/
theorem covariance_estimator_written {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (B : BrownianSystem P d)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b : Fin d → ℝ → Ω → ℝ) (x : Fin d → Ω → ℝ)
    (hbc : ∀ i w,ContinuousOn (fun r => b i r w) (Icc 0 T))
    (hba : ∀ i r,r∈Icc 0 T → Measurable[B.F (realTimeClamp r)] (b i r))
    (hbb : ∀ i r,r∈Icc 0 T → ∀ w,|b i r w|≤K) (hx : ∀ i,Measurable (x i)) :
    let X := fun i => driftedProjectionProcess B (S i) (b i) (x i)
    let a : EuclideanSpace ℝ (Fin d × Fin d) := WithLp.toLp 2 (fun p => (S*S.transpose) p.1 p.2)
    TendstoInMeasure P (fun n => realizedEstimatorMatrix X T (n+1)) atTop (fun _ => a) ∧
    TendstoInDistribution (fun n => normalizedEstimatorMatrix X S T (n+1)) atTop
      id (fun _ => P) (estimatorGaussianLaw S) ∧
    (∀ p,(∫ g,g p ∂estimatorGaussianLaw S)=0) ∧
    (∀ p q,cov[(fun g => g p),(fun g => g q);estimatorGaussianLaw S]=estimatorLimitCovariance S p q) ∧
    (∀ᵐ g ∂estimatorGaussianLaw S,∀ i j,g (i,j)=g (j,i)) := by
  obtain ⟨Γ,q,Q,hQ,⟨Baux⟩⟩ := brownian_system_exists
  letI := q
  letI := hQ
  dsimp only
  refine ⟨?_,finite_interval_estimator_matrix_clt P Q B Baux S T K hT hK b x hbc hba hbb hx,
    estimator_gaussian_matrix P B S⟩
  apply probability_euclidean_of_coordinates
  intro p
  exact finite_interval_estimator_entry_consistency P B (S p.1) (S p.2) T K hT hK
    (b p.1) (b p.2) (x p.1) (x p.2) (hbc p.1) (hbc p.2) (hba p.1) (hba p.2) (hbb p.1) (hbb p.2)

end Asakura.Chapter7
