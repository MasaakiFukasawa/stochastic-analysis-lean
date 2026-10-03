import Chapter9OUConditionalTransition
import Chapter9GaussianObservation

open MeasureTheory ProbabilityTheory Matrix Set
open scoped NNReal ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Actual joint density at two times, derived from the independent Gaussian
stochastic-convolution increment and the adapted state at the earlier time. -/
theorem standard_ou_two_time_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (s t : ℝ) (hs : 0≤s) (hst : s<t)
 :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    P.map (fun w => (X s w,X t w))=((P.map (X s)).prod volume).withDensity
      (fun z => ENNReal.ofReal (gaussianKernel (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) z.1 z.2)) := by
  dsimp only
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  let raw := fun w i => Finset.sum Finset.univ (fun j : Fin d =>
    N i j (realTimeClamp t) w-N i j (realTimeClamp s) w)
  let φ := fun z : Fin d → ℝ => (WithLp.toLp 2 (fun i => Real.exp (-t)*z i) : EuclideanSpace ℝ (Fin d))
  let Z := φ ∘ raw
  let a := Real.exp (-(t-s))
  let v : ℝ≥0 := ⟨1-Real.exp (-2*(t-s)),(ou_variance_positive (t-s) (sub_pos.mpr hst)).le⟩
  let ν := multivariateGaussian 0 ((v:ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hraw : Measurable raw := by
    apply Measurable.of_eval
    intro i
    exact Finset.measurable_sum _ (fun j _ =>
      (((hN i j).adapted P B.F _ (half_real_time_finite t)).mono (B.le _) le_rfl).sub
        (((hN i j).adapted P B.F _ (half_real_time_finite s)).mono (B.le _) le_rfl))
  have hZ : Measurable Z := hφ.comp hraw
  have hindraw := vector_ito_increment_independent P B
    (fun i j r => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp r)
    (fun i j => by fun_prop) N hN hNI t s (hs.trans hst.le) ⟨hs,hst.le⟩
  have hind : Indep (MeasurableSpace.comap Z inferInstance) (B.F (realTimeClamp s)) P :=
    indep_of_indep_of_le_left hindraw (MeasurableSpace.comap_le_comap_of_eq_comp φ hφ rfl)
  have hlaw : HasLaw Z ν P := by
    have hh := vector_ou_innovation_law P B
      ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) N hN hNI t s (hs.trans hst.le) ⟨hs,hst.le⟩
    rw [standard_ou_covariance] at hh
    exact hh
  have hXs : Measurable[B.F (realTimeClamp s)] (X s) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp s)
    change Measurable[B.F (realTimeClamp s)] (fun w i => Real.exp (-s)*(ξ w i+∑ j,N i j (realTimeClamp s) w))
    apply measurable_pi_lambda
    intro i
    exact measurable_const.mul (((measurable_pi_apply i).comp (hξ.mono (B.mono bot_le) le_rfl)).add
      (Finset.measurable_sum _ (fun j _ => (hN i j).adapted P B.F _ (half_real_time_finite s))))
  let F := fun z : (Fin d → ℝ) × EuclideanSpace ℝ (Fin d) => fun i => a*z.1 i+z.2 i
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hexp : a*Real.exp (-s)=Real.exp (-t) := by
    dsimp [a]
    rw [←Real.exp_add]
    congr 1
    ring
  have hpath w : F (X s w,Z w)=X t w := by
    funext i
    change a*(Real.exp (-s)*(ξ w i+∑ j,N i j (realTimeClamp s) w))+
      Real.exp (-t)*(Finset.sum Finset.univ (fun j : Fin d =>
        N i j (realTimeClamp t) w-N i j (realTimeClamp s) w))=_
    rw [←mul_assoc,hexp,Finset.sum_sub_distrib]
    dsimp [X]
    ring
  have hv : v≠0 := by
    intro he
    have hh := congrArg (fun z : ℝ≥0 => (z:ℝ)) he
    exact (ou_variance_positive (t-s) (sub_pos.mpr hst)).ne' hh
  have hXa : Measurable (X s) := hXs.mono (B.le _) le_rfl
  have hi : IndepFun (X s) Z P := (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le_left hind.symm hXs.comap_le)
  have hjoint := hi.map_prod_eq_prod_map_map hXa.aemeasurable hZ.aemeasurable
  rw [hlaw.map_eq] at hjoint
  let μ := P.map (X s)
  haveI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hXa.aemeasurable).mpr inferInstance
  change P.map (fun w => (X s w,X t w))=(μ.prod volume).withDensity
    (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
  calc
    _ = (P.map (fun w => (X s w,Z w))).map (fun z => (z.1,F z)) := by
      rw [Measure.map_map (measurable_fst.prodMk hF.measurable) (hXa.prodMk hZ)]
      congr 1
      funext w
      simp only [Function.comp_def,hpath]
    _ = (μ.prod ν).map (fun z => (z.1,F z)) := by rw [hjoint]
    _ = _ := by
      apply joint_map_of_fiber_density μ ν volume F hF.measurable
        (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
        (by unfold gaussianKernel; fun_prop)
      intro y
      exact isotropic_gaussian_affine_density a v hv y
end Asakura.Chapter9
