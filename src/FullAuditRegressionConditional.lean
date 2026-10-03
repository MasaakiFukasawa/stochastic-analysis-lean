import FullAuditGaussianIndependence
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set ContinuousLinearMap
namespace Asakura.FullAudit

noncomputable def linearPredictor {n : ℕ} (a : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

theorem linearPredictor_apply {n : ℕ} (a : Fin n → ℝ) (y : Fin n → ℝ) :
    linearPredictor a y = ∑ i, a i * y i := by
  simp [linearPredictor, ContinuousLinearMap.sum_apply]

/-- Probabilistic part of the printed regression proof: form the residual,
check its covariance, use the characteristic-function independence argument,
and remove the zero-mean residual under conditional expectation. -/
theorem gaussian_regression_residual_written {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} {X : Ω → ℝ} {Y : Ω → Fin n → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hmX : Measurable X) (hmY : Measurable Y) (a : Fin n → ℝ)
    (hmean : ∫ ω, X ω ∂P = 0) (hYmean : ∀ j, ∫ ω, Y ω j ∂P = 0)
    (hcov : ∀ j, cov[X, (fun ω => Y ω j); P] =
      ∑ i, a i * cov[(fun ω => Y ω i), (fun ω => Y ω j); P]) :
    P[X | MeasurableSpace.comap Y inferInstance] =ᵐ[P]
      (fun ω => ∑ i, a i * Y ω i) := by
  have := hXY.isProbabilityMeasure
  let Z : Ω → ℝ := fun ω => linearPredictor a (Y ω)
  let R : Ω → ℝ := fun ω => X ω - Z ω
  let L : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ _ - (linearPredictor a).comp (ContinuousLinearMap.snd ℝ ℝ _)
  have hR : HasGaussianLaw R P := hXY.map L
  have hZ : HasGaussianLaw Z P := hXY.snd.map (linearPredictor a)
  have hRmean : ∫ ω, R ω ∂P = 0 := by
    rw [show R = X - Z from rfl]
    simp only [Pi.sub_apply]
    rw [integral_sub hXY.fst.integrable hZ.integrable, hmean]
    dsimp [Z]
    simp_rw [linearPredictor_apply]
    rw [integral_finsetSum _ (fun i _ => (hXY.snd.eval i).integrable.const_mul (a i))]
    simp [integral_const_mul, hYmean]
  have hcross (j : Fin n) : cov[R, (fun ω => Y ω j); P] = 0 := by
    rw [show R = X - Z from rfl,
      covariance_sub_left hXY.fst.memLp_two hZ.memLp_two (hXY.snd.eval j).memLp_two]
    dsimp [Z]
    simp_rw [linearPredictor_apply]
    rw [covariance_fun_sum_left (fun i => (hXY.snd.eval i).memLp_two.const_mul (a i))
      (hXY.snd.eval j).memLp_two]
    simp only [covariance_const_mul_left, hcov, sub_self]
  have hjoint : HasGaussianLaw (fun ω => ((fun _ : Fin 1 => R ω), Y ω)) P :=
    hXY.map ((ContinuousLinearMap.pi fun _ : Fin 1 => L).prod (ContinuousLinearMap.snd ℝ ℝ _))
  have hind0 := gaussian_independence_coordinates_written hjoint (fun _ j => hcross j)
  have hind : IndepFun R Y P := by
    exact hind0.comp (measurable_pi_apply (0 : Fin 1)) measurable_id
  have hmR : Measurable R := hmX.sub ((linearPredictor a).continuous.measurable.comp hmY)
  let G := MeasurableSpace.comap Y inferInstance
  have hG : G ≤ m := hmY.comap_le
  have hzero : P[R | G] =ᵐ[P] (fun _ => (0:ℝ)) := by
    have h := condExp_indep_eq hmR.comap_le hG
      (show StronglyMeasurable[MeasurableSpace.comap R inferInstance] R from
        (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind
    simpa only [hRmean] using h
  have hmZ : StronglyMeasurable[G] Z :=
    ((linearPredictor a).continuous.measurable.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hself : P[Z | G] = Z := condExp_of_stronglyMeasurable hG hmZ hZ.integrable
  have hsub := condExp_sub (m := G) hXY.fst.integrable hZ.integrable
  rw [hself] at hsub
  filter_upwards [hsub,hzero] with ω hs hz
  change P[R | G] ω = P[X | G] ω - Z ω at hs
  change P[X | G] ω = ∑ i, a i * Y ω i
  have : Z ω = ∑ i, a i * Y ω i := linearPredictor_apply a (Y ω)
  linarith

end Asakura.FullAudit
