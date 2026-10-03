import Chapter12Representation
import FullAuditGaussianIndependence

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Passing from the constructed L2 linear map to representatives gives the
finite almost-everywhere linearity required in the cylindrical proofs. -/
theorem wiener_finite_linearity {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (P : Measure Ω)
    (W : H →ₗ[ℝ] Lp ℝ 2 P) {n : ℕ} (v : Fin n → H) (c : Fin n → ℝ) :
    (W (∑ i,c i • v i) : Ω → ℝ) =ᵐ[P] fun ω => ∑ i,c i*W (v i) ω := by
  rw [map_sum]
  simp_rw [map_smul]
  have he := Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • W (v i))
  filter_upwards [he,ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (W (v i)))] with ω hω hs
  rw [hω]
  apply Finset.sum_congr rfl
  intro i _
  exact hs i

/-- One-dimensional normality of every deterministic integral implies joint
Gaussianity; it is not a separate assumption about independent coordinates. -/
theorem wiener_joint_gaussian {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n : ℕ} (v : Fin n → H) :
    HasGaussianLaw (fun ω i => W (v i) ω) P := by
  have hm : AEMeasurable (fun ω i => W (v i) ω) P :=
    AEMeasurable.of_eval (fun i => (Lp.memLp (W (v i))).aestronglyMeasurable.aemeasurable)
  refine ⟨hm, ?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  let c := fun i => L (Pi.single i 1)
  let h := ∑ i,c i • v i
  have he := wiener_finite_linearity P W.toLinearMap v c
  have hre : (fun ω => L (fun i => W (v i) ω)) =ᵐ[P] (W h : Ω → ℝ) := by
    filter_upwards [he] with ω hω
    rw [finite_differential_coordinates]
    change (W h : Ω → ℝ) ω = ∑ i,c i*(W (v i) : Ω → ℝ) ω at hω
    rw [hω]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  refine ⟨0,⟨‖h‖^2,sq_nonneg _⟩,?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hm]
  exact (hlaw h).congr hre |>.map_eq

/-- Orthogonal deterministic directions yield independent standard Gaussian
coordinates. The independence and the product law are derived. -/
theorem wiener_orthonormal_law {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    {n : ℕ} (e : Fin n → H) (he : Orthonormal ℝ e) :
    HasLaw (fun ω i => W (e i) ω) (Measure.pi fun _ => gaussianReal 0 1) P := by
  have hm (h : H) : (∫ ω, W h ω ∂P) = 0 := by
    simpa only [integral_id_gaussianReal] using (hlaw h).integral_eq
  have hc i j : cov[(W (e i) : Ω → ℝ),(W (e j) : Ω → ℝ); P] = ⟪e i,e j⟫ := by
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),hm,hm,mul_zero,sub_zero]
    have hi := W.inner_map_map (e i) (e j)
    rw [L2.inner_def] at hi
    simpa only [real_inner_comm,Real.inner_apply,Pi.mul_apply] using hi
  have hind := (wiener_joint_gaussian P W hlaw e).iIndepFun_of_covariance_eq_zero
    (fun i j hij => by rw [hc]; exact he.inner_eq_zero hij)
  apply hind.hasLaw_pi
  intro i
  convert hlaw (e i) using 1
  congr 1
  apply NNReal.eq
  change (1:ℝ) = ‖e i‖^2
  rw [he.norm_eq_one i,one_pow]

end Asakura.Chapter12
