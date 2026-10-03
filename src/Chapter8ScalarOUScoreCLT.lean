import Chapter8ScalarOUInvariantTests
import Chapter8ConstructedLangevinScoreCLT
import Chapter8OUInformation
import Chapter4DeterministicSDEFamily

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The information and score limits of the OU example follow from the
actual Langevin time-average and martingale CLT, with its Gaussian invariant law. -/
theorem scalar_ou_score_clt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ σ x : ℝ) (hθ : 0<θ) (hσ : 0<σ)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n) (hTlim : Tendsto T atTop atTop) :
    ∃ (Z : (Fin 1 → ℝ) → HalfClosedTime → Ω → Fin 1 → ℝ)
      (N : Fin 1 → Fin 1 → HalfClosedTime → Ω → ℝ),
      (∀ y,VectorSDESolution P B.F B.W (fun _ z => -θ*z 0) (fun _ _ _ => σ) (fun _ => y) (Z y)) ∧
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => -(Z (fun _ => x) (realTimeClamp z.2) z.1 0)/σ) (N k j)) ∧
      TendstoInMeasure P (fun t w => (∫ r in 0..t,(Z (fun _ => x) (realTimeClamp r) w 0)^2/σ^2)/t)
        atTop (fun _ => 1/(2*θ)) ∧
      TendstoInDistribution (fun q w => WithLp.toLp 2 (fun k => N k 0 (realTimeClamp (T q)) w/Real.sqrt (T q)))
        atTop id (fun _ => P) (multivariateGaussian 0 (fun _ _ : Fin 1 => 1/(2*θ))) := by
  obtain ⟨Z,hZ⟩ := deterministic_sde_family_exists P B (θ^2) (sq_nonneg _) _ _ (scalar_ou_lipschitz_square θ σ)
  let π := gaussianReal 0 (ouStationaryVariance θ σ hθ)
  let ν := π.map scalarCoordinate.symm
  haveI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff scalarCoordinate.symm.continuous.measurable.aemeasurable).mpr inferInstance
  have hν : MemLp (fun z => z) 2 ν := by
    apply scalarCoordinate.symm.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact scalarCoordinate.symm.toContinuousLinearMap.comp_memLp' (memLp_id_gaussianReal (p := 2))
  have he : ν.map scalarCoordinate=π := by
    rw [Measure.map_map scalarCoordinate.continuous.measurable scalarCoordinate.symm.continuous.measurable]
    simp only [Function.comp_def,scalarCoordinate.apply_symm_apply,Measure.map_id']
  let g := fun y : Fin 1 → ℝ => fun _ : Fin 1 => θ*y 0
  let Kg := ‖scalarCoordinate.symm.toContinuousLinearMap‖₊*(‖θ‖₊*‖scalarCoordinate.toContinuousLinearMap‖₊)
  have hg : LipschitzWith Kg g := by
    exact scalarCoordinate.symm.toContinuousLinearMap.lipschitz.comp
      ((lipschitzWith_smul θ).comp scalarCoordinate.toContinuousLinearMap.lipschitz)
  have hmono y z : θ*‖scalarCoordinate y-scalarCoordinate z‖^2≤
      ⟪scalarCoordinate y-scalarCoordinate z,scalarCoordinate (g y)-scalarCoordinate (g z)⟫ := by
    simp only [scalarCoordinate_apply,g,Real.norm_eq_abs,sq_abs,real_inner_self_eq_norm_sq]
    rw [Real.inner_apply]
    nlinarith
  let H := fun (_ _ : Fin 1) (z : ℝ) => -z/σ
  let K := fun (_ _ : Fin 1) => ‖-σ⁻¹‖₊
  have hH k j : LipschitzWith (K k j) (H k j) := by
    convert (lipschitzWith_smul (-σ⁻¹) : LipschitzWith ‖-σ⁻¹‖₊ (fun z : ℝ => (-σ⁻¹) • z)) using 1
    funext z
    simp only [H,smul_eq_mul]
    ring
  have hHc k j : ContDiff ℝ 1 (H k j) := by dsimp [H]; fun_prop
  let S : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1/(2*θ)
  have hS : S.PosDef := by
    have hp : 0<1/(2*θ) := by positivity
    convert (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef).smul hp using 1
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    simp [S,hi,hj]
  have hSe k l : S k l=∫ z,∑ j,H k j z*H l j z ∂ν.map scalarCoordinate := by
    rw [he]
    have hh := (ou_information θ σ hθ hσ).2.1
    have heq (z : ℝ) : (∑ j : Fin 1,H k j z*H l j z)=(σ^2)⁻¹*z^2 := by simp [H]; ring
    simp_rw [heq]
    rw [integral_const_mul]
    exact hh.symm
  have hZ' y : VectorSDESolution P B.F B.W (fun i z => -(g z i)) (fun _ _ _ => σ) (fun _ => y) (Z y) := by
    simpa only [g,neg_mul] using hZ y
  have hLip : ∀ y z,(∑ i,(-(g y i)- -(g z i))^2)+(∑ i : Fin 1,∑ j : Fin 1,(σ-σ)^2)≤θ^2*∑ i,(y i-z i)^2 := by
    simpa only [g,neg_mul] using scalar_ou_lipschitz_square θ σ
  obtain ⟨havg,N,hN,hNI,hNl⟩ := constructed_langevin_score_clt P B scalarCoordinate g Kg hg
    (fun _ _ => σ) (θ^2) (sq_nonneg _) hLip θ hθ hmono ν hν Z hZ'
    (scalar_ou_invariant_tests P B θ σ hθ Z hZ) (fun _ => x) H K hH hHc S hS hSe T hT hTlim
  refine ⟨Z,N,hZ,hN,hNI,?_,?_⟩
  · have hh := havg 0 0
    convert hh using 1
    funext t w
    congr 1
    apply intervalIntegral.integral_congr
    intro r _
    simp [H]
    ring
  · simpa only [Fin.sum_univ_one] using hNl
end Asakura.Chapter8
