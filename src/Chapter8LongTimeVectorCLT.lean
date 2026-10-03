import Chapter8LongTimeGaussianCLT
import Chapter8GaussianProjection
import Chapter4FiniteCovarianceSum
import Chapter7CramerWold

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
  Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Cramer-Wold applied to the actual scalar projections and their
constructed quadratic variations. The projection of the information
limit is positive by positive definiteness. -/
theorem long_time_vector_clt {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M : Fin d → HalfClosedTime → Ω → ℝ)
    (C : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hM : ∀ i, LocalMProcessWitness P F (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (havg : ∀ v : EuclideanSpace ℝ (Fin d),
      TendstoInMeasure P (fun T ω => (∑ j,v j*(∑ i,v i*C i j (realTimeClamp T) ω))/T)
        atTop (fun _ => v ⬝ᵥ S *ᵥ v))
    (T : ℕ → ℝ) (hT : ∀ n,0 < T n) (hTlim : Tendsto T atTop atTop) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (fun i => M i (realTimeClamp (T n)) ω/Real.sqrt (T n))) atTop
      id (fun _ => P) (multivariateGaussian 0 S) := by
  let V := fun n ω => WithLp.toLp 2 (fun i => M i (realTimeClamp (T n)) ω/Real.sqrt (T n))
  have hm (n : ℕ) : Measurable (V n) := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    exact (((hM i).adapted P F _ (real_time_below _ (hT n).le (EReal.coe_lt_top _))).mono
      (hle _) le_rfl).div_const _
  apply cramer_wold_euclidean P (multivariateGaussian 0 S) V id
    (fun n => (hm n).aemeasurable) measurable_id.aemeasurable
  intro v
  by_cases hv : v=0
  · subst v
    simp only [inner_zero_right]
    have hd := tendstoInDistribution_const (μ' := P) (l := (atTop : Filter ℕ))
      (show AEMeasurable (fun _ : Ω => (0:ℝ)) P from measurable_const.aemeasurable)
    have hl : HasLaw (fun _ : Ω => (0:ℝ)) (gaussianReal 0 0) P := by
      refine ⟨measurable_const.aemeasurable,?_⟩
      simp [Measure.map_const,gaussianReal_zero_var]
    have hr : HasLaw (fun _ : EuclideanSpace ℝ (Fin d) => (0:ℝ))
        (gaussianReal 0 0) (multivariateGaussian 0 S) := by
      refine ⟨measurable_const.aemeasurable,?_⟩
      simp [Measure.map_const,gaussianReal_zero_var]
    exact distribution_limit_same_law P P (multivariateGaussian 0 S) hd hl hr
  let N := fun t ω => ∑ i,v i*M i t ω
  let A := fun t ω => ∑ j,v j*(∑ i,v i*C i j t ω)
  have hN : LocalMProcessWitness P F N :=
    local_martingale_finset_sum P (by simp : (0:EReal)<⊤) F hF hle Finset.univ
      (fun i t ω => v i*M i t ω) (fun i _ => (hM i).smul P F (v i))
  have hA : LocalCovarianceWitness P F N N A :=
    weighted_covariance_sum P (by simp : (0:EReal)<⊤) F hF hle M C v v hC
  have hv' : (v : Fin d → ℝ) ≠ 0 := by
    intro he
    apply hv
    ext i
    exact congrFun he i
  have hc : 0 < v ⬝ᵥ S *ᵥ v := by
    simpa only [star_trivial] using hS.dotProduct_mulVec_pos hv'
  have hd := long_time_scalar_gaussian_clt P F hF hle N A hN hA
    (v ⬝ᵥ S *ᵥ v) hc (havg v) T hT hTlim
  have hl : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (v ⬝ᵥ S *ᵥ v).toNNReal)
      (gaussianReal 0 ⟨v ⬝ᵥ S *ᵥ v,hc.le⟩) := by
    refine ⟨measurable_id.aemeasurable,?_⟩
    rw [Measure.map_id]
    congr 1
    exact (Real.toNNReal_of_nonneg hc.le).symm
  have hlim := distribution_limit_same_law P (gaussianReal 0 ⟨v ⬝ᵥ S *ᵥ v,hc.le⟩)
    (multivariateGaussian 0 S) hd hl (multivariate_gaussian_projection_law S hS.posSemidef v)
  apply hlim.congr _ (.rfl)
  intro n
  apply ae_of_all _
  intro ω
  dsimp only [N,V]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,WithLp.ofLp_toLp,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Asakura.Chapter8
