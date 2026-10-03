import Chapter8ScalarOUScoreCLT
import Chapter8WrittenMLELimit

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology BigOperators RealInnerProductSpace MatrixOrder
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Scalar specialization of the inverse-information Gaussian law. -/
theorem scalar_inverse_information_law (θ : ℝ) (hθ : 0 < θ) :
    HasLaw (fun v : EuclideanSpace ℝ (Fin 1) => v 0)
      (gaussianReal 0 (2*θ).toNNReal)
      (multivariateGaussian 0 (fun _ _ : Fin 1 => 1/(2*θ))⁻¹) := by
  let S : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1/(2*θ)
  have hS : S.PosDef := by
    convert (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef).smul (show 0<1/(2*θ) by positivity) using 1
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    simp [S,hi,hj]
  have he : S⁻¹ = fun _ _ => 2*θ := by
    apply Matrix.inv_eq_right_inv
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply,Fin.sum_univ_one,S,hi,hj,Matrix.one_apply_eq]
    field_simp
    simp [Matrix.one_apply,hi,hj,Pi.one_apply]
  have hh := multivariate_gaussian_projection_law S⁻¹ hS.inv.posSemidef (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))
  change HasLaw _ _ (multivariateGaussian 0 S⁻¹)
  rw [he]
  simpa only [he,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,WithLp.ofLp_toLp,
    Fin.sum_univ_one,mul_one,one_mul,Matrix.mulVec,dotProduct] using hh

/-- The actual OU score and time average give the displayed scalar estimator CLT,
including the convention on vanishing information. -/
theorem scalar_ou_written_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ σ x : ℝ) (hθ : 0<θ) (hσ : 0<σ)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n) (hTlim : Tendsto T atTop atTop) :
    ∃ (Z : (Fin 1 → ℝ) → HalfClosedTime → Ω → Fin 1 → ℝ)
      (N : HalfClosedTime → Ω → ℝ),
      (∀ y,VectorSDESolution P B.F B.W (fun _ z => -θ*z 0) (fun _ _ _ => σ) (fun _ => y) (Z y)) ∧
      LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => -(Z (fun _ => x) (realTimeClamp z.2) z.1 0)/σ) N ∧
      let I := fun q w => ∫ r in 0..T q,(Z (fun _ => x) (realTimeClamp r) w 0)^2/σ^2
      let est := fun q w => if I q w≠0 then θ+N (realTimeClamp (T q)) w/I q w else 0
      TendstoInDistribution (fun q w => Real.sqrt (T q)*(est q w-θ)) atTop id (fun _ => P)
        (gaussianReal 0 (2*θ).toNNReal) := by
  classical
  obtain ⟨Z,N,hZ,hN,hNI,havg,hNl⟩ := scalar_ou_score_clt P B θ σ x hθ hσ T hT hTlim
  refine ⟨Z,N 0 0,hZ,hN 0 0,hNI 0 0,?_⟩
  dsimp only
  let J := fun q w => ∫ r in 0..T q,(Z (fun _ => x) (realTimeClamp r) w 0)^2/σ^2
  let I : ℕ → Ω → Matrix (Fin 1) (Fin 1) ℝ := fun q w _ _ => J q w
  have hc w : Continuous (fun t : ℝ => Z (fun _ => x) (realTimeClamp t) w 0) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuous_apply 0).continuousAt.comp (((hZ _).path w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt)
  have hm : Measurable (fun z : Ω × ℝ => Z (fun _ => x) (realTimeClamp z.2) z.1 0) :=
    (measurable_uncurry_of_continuous_of_measurable hc (fun t => (measurable_pi_apply 0).comp
      (((hZ _).adapted _ (half_real_time_finite t)).mono (B.le _) le_rfl))).comp measurable_swap
  have hJm q : Measurable (J q) := by
    dsimp only [J]
    simp_rw [intervalIntegral.integral_of_le (hT q).le]
    exact (show StronglyMeasurable (Function.uncurry (fun w r => (Z (fun _ => x) (realTimeClamp r) w 0)^2/σ^2)) from
      ((hm.pow_const 2).div_const _).stronglyMeasurable).integral_prod_right.measurable
  have hIm q : Measurable (I q) := by
    apply measurable_pi_lambda
    intro k
    apply measurable_pi_lambda
    intro l
    exact hJm q
  have hIp q w : (I q w).PosSemidef := by
    have hp : 0≤J q w := intervalIntegral.integral_nonneg (hT q).le (fun r _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    convert (Matrix.PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef).smul hp using 1
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    simp [I,hi,hj]
  let noise := fun q w (_ : Fin 1) => N 0 0 (realTimeClamp (T q)) w
  let score := fun q w => I q w *ᵥ (fun _ => θ)+noise q w
  have hsm q : Measurable (score q) := by
    apply measurable_pi_lambda
    intro k
    have hh : Measurable (fun w => J q w*θ+N 0 0 (realTimeClamp (T q)) w) := ((hJm q).mul_const θ).add
      (((hN 0 0).adapted P B.F (realTimeClamp (T q)) (half_real_time_finite (T q))).mono (B.le _) le_rfl)
    simpa only [score,noise,I,Matrix.mulVec,dotProduct,Fin.sum_univ_one,Pi.add_apply] using hh
  let S : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1/(2*θ)
  have hS : S.PosDef := by
    convert (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef).smul (show 0<1/(2*θ) by positivity) using 1
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    simp [S,hi,hj]
  have hNl' : TendstoInDistribution (fun q w => WithLp.toLp 2 (fun k => noise q w k/Real.sqrt (T q)))
      atTop id (fun _ => P) (multivariateGaussian 0 S) := by
    convert hNl using 1
    funext q w
    ext k
    have hk : k=0 := Subsingleton.elim _ _
    simp [noise,hk]
  have hh := (written_mle_limit P I hIm hIp score noise hsm (fun _ => θ)
    (fun _ => ae_of_all _ (fun _ => rfl)) T hT hTlim S hS (fun _ _ => havg.comp hTlim) hNl').1
  have hp := hh.continuous_comp (show Continuous (fun v : EuclideanSpace ℝ (Fin 1) => v 0) from (EuclideanSpace.proj 0).continuous)
  have hl := scalar_inverse_information_law θ hθ
  have hz : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (2*θ).toNNReal) (gaussianReal 0 (2*θ).toNNReal) := ⟨measurable_id.aemeasurable,Measure.map_id⟩
  have hh' := Asakura.Chapter7.distribution_limit_same_law P (multivariateGaussian 0 S⁻¹) (gaussianReal 0 (2*θ).toNNReal) hp hl hz
  apply hh'.congr _ Filter.EventuallyEq.rfl
  intro q
  apply ae_of_all
  intro w
  dsimp only [Function.comp_def,WithLp.ofLp_toLp]
  have he : (I q w).det=J q w := by simp [I,Matrix.det_fin_one]
  change Real.sqrt (T q)*((if (I q w).det≠0 then (I q w)⁻¹ *ᵥ score q w else 0) 0-θ)=
    Real.sqrt (T q)*((if J q w≠0 then θ+N 0 0 (realTimeClamp (T q)) w/J q w else 0)-θ)
  rw [he]
  by_cases hj : J q w=0
  · simp only [hj,ne_eq,not_true_eq_false,ite_false,Pi.zero_apply]
  · have hi : (I q w)⁻¹ = fun _ _ => (J q w)⁻¹ := by
      apply Matrix.inv_eq_right_inv
      ext i j
      have hij : i=j := Subsingleton.elim _ _
      simp [Matrix.mul_apply,I,hij,hj,Matrix.one_apply,Pi.one_apply]
    simp only [if_pos hj,hi,Matrix.mulVec,dotProduct,Fin.sum_univ_one,Pi.add_apply,score,noise,I]
    field_simp
    <;> ring
end Asakura.Chapter8
