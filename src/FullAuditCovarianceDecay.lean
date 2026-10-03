import FullAuditIndependentCopyVariance
import FullAuditQuadraticCS
import FullAuditConditionalExercises

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem covariance_cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |cov[X,Y;P]| ≤ Real.sqrt (Var[X;P])*Real.sqrt (Var[Y;P]) := by
  apply quadratic_interval_cs _ _ _ (variance_nonneg _ _) (variance_nonneg _ _)
  intro q
  have h := variance_nonneg (fun ω => (q:ℝ)*X ω+Y ω) P
  rw [variance_fun_add (hX.const_mul _) hY,variance_const_mul,covariance_const_mul_left] at h
  convert h using 1 <;> ring

/-- C2/C3 move conditioning onto the future factor in the covariance. -/
theorem covariance_conditional_future {Ω : Type*} {G m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (X Y Z : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (hmX : AEStronglyMeasurable[G] X P) (hCE : P[Y|G] =ᵐ[P] Z) :
    cov[X,Y;P] = cov[X,Z;P] := by
  letI : MeasurableSpace Ω := m
  have hp := exercise_ce_holder_pullout P hY hX hmX
  have hprod : (∫ ω, X ω*Y ω ∂P) = ∫ ω, X ω*Z ω ∂P := by
    have h := integral_congr_ae hp
    rw [integral_condExp (μ := P) hG] at h
    have hz : (fun ω => P[Y|G] ω*X ω) =ᵐ[P] (fun ω => Z ω*X ω) := hCE.mul (EventuallyEq.refl _ _)
    simp only [Pi.mul_apply] at h
    rw [integral_congr_ae hz] at h
    simpa only [Pi.mul_apply,mul_comm] using h
  have hmean : (∫ ω, Y ω ∂P) = ∫ ω, Z ω ∂P := by
    rw [← integral_condExp (μ := P) hG (f := Y)]
    exact integral_congr_ae hCE
  rw [covariance_eq_sub hX hY,covariance_eq_sub hX hZ,hmean]
  change (∫ ω, X ω*Y ω ∂P)-_ = (∫ ω, X ω*Z ω ∂P)-_
  rw [hprod]

/-- Combine the two independent-copy variance bounds with Cauchy-Schwarz.
 The function g represents P_t f, whose Lipschitz constant has already been
 bounded by the synchronous coupling. -/
theorem lipschitz_covariance_decay {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (hP : MemLp (fun x : E => x) 2 P) (f g : E → ℝ) (L : ℝ≥0) (κ t : ℝ)
    (hfL : LipschitzWith L f)
    (hgL : LipschitzWith (L*⟨Real.exp (-κ*t),(Real.exp_pos _).le⟩) g)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |cov[f,g;P]| ≤ (L:ℝ)^2*(∫ x, ‖x-(∫ y, y ∂P)‖^2 ∂P)*Real.exp (-κ*t) := by
  let m2 := ∫ x, ‖x-(∫ y, y ∂P)‖^2 ∂P
  have hm2 : 0 ≤ m2 := integral_nonneg (fun _ => sq_nonneg _)
  have hfvar := lipschitz_variance_bound P hP f L hfL hf
  have hgvar := lipschitz_variance_bound P hP g _ hgL hg
  change Var[g;P] ≤ ((L:ℝ)*Real.exp (-κ*t))^2*(∫ x, ‖x-(∫ y,y ∂P)‖^2 ∂P) at hgvar
  have hcs := covariance_cauchy_schwarz P f g hf hg
  have hc2 := pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [sq_abs,mul_pow,Real.sq_sqrt (variance_nonneg f P),Real.sq_sqrt (variance_nonneg g P)] at hc2
  have hv := mul_le_mul hfvar hgvar (variance_nonneg g P) (by positivity)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  apply hc2.trans
  convert hv using 1 <;> ring

end Asakura.FullAudit
