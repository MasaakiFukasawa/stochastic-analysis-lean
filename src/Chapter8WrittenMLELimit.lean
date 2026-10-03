import Chapter8LikelihoodCLTAssemblyAE
import Chapter8RescaledLikelihoodError
import Chapter8SelfNormalisation
import Chapter8CLTConsistency

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology BigOperators Matrix.Norms.Elementwise MatrixOrder
namespace Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Apply the score and information limits to the actual maximizer of
the quadratic likelihood, set equal to zero on singular information. -/
theorem written_mle_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : ℕ}
    (I : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ) (hI : ∀ n,Measurable (I n))
    (hIp : ∀ n w,(I n w).PosSemidef)
    (score noise : ℕ → Ω → Fin p → ℝ) (hscore : ∀ n,Measurable (score n))
    (θ : Fin p → ℝ) (he : ∀ n,∀ᵐ w ∂P,score n w=I n w *ᵥ θ+noise n w)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n) (hTlim : Tendsto T atTop atTop)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef)
    (hIl : ∀ k l,TendstoInMeasure P (fun n w => I n w k l/T n) atTop (fun _ => S k l))
    (hNl : TendstoInDistribution (fun n w => WithLp.toLp 2 (fun k => noise n w k/Real.sqrt (T n)))
      atTop id (fun _ => P) (multivariateGaussian 0 S)) :
    let est := fun n w => if (I n w).det≠0 then (I n w)⁻¹ *ᵥ score n w else 0
    let V := fun n w => WithLp.toLp 2 (fun k => Real.sqrt (T n)*(est n w k-θ k))
    TendstoInDistribution V atTop id (fun _ => P) (multivariateGaussian 0 S⁻¹) ∧
      TendstoInMeasure P (fun n w => WithLp.toLp 2 (fun k => est n w k-θ k)) atTop (fun _ => 0) ∧
      TendstoInDistribution (fun n w => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt ((T n)⁻¹ • I n w)) (V n w))
        atTop id (fun _ => P) (multivariateGaussian 0 1) := by
  classical
  dsimp only
  let est := fun n w => if (I n w).det≠0 then (I n w)⁻¹ *ᵥ score n w else 0
  let V := fun n w => WithLp.toLp 2 (fun k => Real.sqrt (T n)*(est n w k-θ k))
  let J := fun n w => (T n)⁻¹ • I n w
  have hJm n : Measurable (J n) := by
    change Measurable (fun w => (T n)⁻¹ • I n w)
    exact (measurable_const : Measurable (fun _ : Ω => (T n)⁻¹)).smul (hI n)
  have hJpos n w : (J n w).PosSemidef := (hIp n w).smul (inv_nonneg.mpr (hT n).le)
  have hJl k l : TendstoInMeasure P (fun n w => J n w k l) atTop (fun _ => S k l) := by
    simpa only [J,Matrix.smul_apply,smul_eq_mul,div_eq_inv_mul] using hIl k l
  have hest n : Measurable (est n) := by
    apply Measurable.ite
    · exact ((continuous_id.matrix_det.measurable.comp (hI n)) (measurableSet_singleton 0)).compl
    · apply measurable_pi_lambda
      intro k
      simpa only [Matrix.mulVec,dotProduct,Function.comp_def,Pi.mul_apply] using Finset.measurable_sum Finset.univ (fun j _ =>
        ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp (matrix_inverse_measurable.comp (hI n)))).mul
          ((measurable_pi_apply j).comp (hscore n)))
    · exact measurable_const
  have hVm n : Measurable (V n) := by
    apply (WithLp.measurable_toLp 2 (Fin p → ℝ)).comp
    apply measurable_pi_lambda
    intro k
    exact (((measurable_pi_apply k).comp (hest n)).sub measurable_const).const_mul _
  have hVe n : ∀ᵐ w ∂P,(J n w).det≠0 → V n w=Matrix.toEuclideanCLM (𝕜 := ℝ) (J n w)⁻¹
      (WithLp.toLp 2 (fun k => noise n w k/Real.sqrt (T n))) := by
    filter_upwards [he n] with w hw
    intro hn
    have hdet : (I n w).det≠0 := by
      intro hz
      apply hn
      simp [J,Matrix.det_smul,hz]
    have hp := (information_posDef_iff_det_ne_zero (I n w) (hIp n w)).mpr hdet
    simpa only [V,est,if_pos hdet,J] using rescaled_likelihood_error (I n w) hp θ (score n w) (noise n w) hw (T n) (hT n)
  have hv := likelihood_clt_assembly_ae P _ V J S hS hNl hJm (fun n => (hVm n).aemeasurable) hJl hVe
  refine ⟨hv,?_,self_normalised_likelihood_clt P V J S hS hv hJm hJpos hJl⟩
  have hc := consistency_from_scaled_clt P (multivariateGaussian 0 S⁻¹) V id hv
    (fun n => (Real.sqrt (T n))⁻¹) (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hTlim))
  convert hc using 1
  funext n w
  ext k
  simp only [V,PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_toLp]
  rw [←mul_assoc,inv_mul_cancel₀ (Real.sqrt_pos.mpr (hT n)).ne',one_mul]
end Asakura.Chapter8
