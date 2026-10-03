import FullAuditMertonIntegrability

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def mertonGenerator (r μ σ γ T t x z : ℝ) :=
    deriv (fun s => mertonValue r μ σ γ T s x) t+
      x*(r+z*(μ-r))*deriv (mertonValue r μ σ γ T t) x+
      σ^2*z^2*x^2/2*deriv (fun y => deriv (mertonValue r μ σ γ T t) y) x

/-- Verification from the preceding Ito formula and stochastic-integral
 isometry/mean-zero theorem. The Ito input uses the actual derivatives of J,
 before the generator is simplified. Moment integrability, simplification,
 utility integrability, and the expectation inequality are proved below. -/
theorem merton_expected_utility {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V π : Ω × ℝ → ℝ) (M : Ω → ℝ)
    (r μ σ γ T x K : ℝ) (hσ : σ ≠ 0) (hγ : 0 < γ) (hγ1 : γ ≠ 1)
    (hV : Measurable V) (hπ : Measurable π) (hpos : ∀ z, 0 < V z)
    (hbound : ∀ z, ‖π z‖ ≤ K)
    (hmom : Integrable (fun z => (V z)^(2*(1-γ))) (P.prod (volume.restrict (Icc 0 T))))
    (hIto : ∀ᵐ ω ∂P, mertonValue r μ σ γ T T (V (ω,T)) = mertonValue r μ σ γ T 0 x+
      (∫ t in Icc 0 T, mertonGenerator r μ σ γ T t (V (ω,t)) (π (ω,t)))+M ω)
    (hMean : MemLp (fun z : Ω × ℝ => σ*π z*V z*deriv (mertonValue r μ σ γ T z.2) (V z)) 2
      (P.prod (volume.restrict (Icc 0 T))) → Integrable M P ∧ (∫ ω, M ω ∂P) = 0) :
    Integrable (fun ω => (V (ω,T))^(1-γ)/(1-γ)) P ∧
    (∫ ω, (V (ω,T))^(1-γ)/(1-γ) ∂P) = mertonValue r μ σ γ T 0 x-
      γ*σ^2/2*(∫ ω, (∫ t in Icc 0 T,
        Real.exp (mertonRate r μ σ γ*(T-t))*(V (ω,t))^(1-γ)*(π (ω,t)-(μ-r)/(γ*σ^2))^2) ∂P) ∧
    (∫ ω, (V (ω,T))^(1-γ)/(1-γ) ∂P) ≤ mertonValue r μ σ γ T 0 x := by
  let ν := volume.restrict (Icc 0 T)
  let a := (μ-r)/(γ*σ^2)
  let L : Ω → ℝ := fun ω => ∫ t, Real.exp (mertonRate r μ σ γ*(T-t))*(V (ω,t))^(1-γ)*(π (ω,t)-a)^2 ∂ν
  have hcoef := merton_coefficients_integrable P V π (mertonRate r μ σ γ) γ σ a T K hV hπ hpos hbound hmom
  have hM := hMean (by simpa only [merton_noise_coefficient r μ σ γ T _ _ _ (hpos _) hγ1] using hcoef.1)
  have hL : Integrable L P := hcoef.2.integral_prod_left
  have heq : (fun ω => (V (ω,T))^(1-γ)/(1-γ)) =ᵐ[P]
      (fun ω => mertonValue r μ σ γ T 0 x-γ*σ^2/2*L ω+M ω) := by
    filter_upwards [hIto] with ω hω
    rw [merton_terminal_utility] at hω
    convert hω using 1
    dsimp only [mertonGenerator]
    simp_rw [merton_generator_square r μ σ γ T _ _ _ (hpos _) hγ1 (ne_of_gt hγ) hσ]
    have he : (fun t => -(γ*σ^2/2)*Real.exp (mertonRate r μ σ γ*(T-t))*(V (ω,t))^(1-γ)*(π (ω,t)-a)^2) =
        fun t => -(γ*σ^2/2)*(Real.exp (mertonRate r μ σ γ*(T-t))*(V (ω,t))^(1-γ)*(π (ω,t)-a)^2) := by
      funext t
      ring
    change _ = mertonValue r μ σ γ T 0 x+(∫ t, -(γ*σ^2/2)*Real.exp (mertonRate r μ σ γ*(T-t))*(V (ω,t))^(1-γ)*(π (ω,t)-a)^2 ∂ν)+M ω
    rw [he,integral_const_mul]
    change _ = mertonValue r μ σ γ T 0 x+ -(γ*σ^2/2)*L ω+M ω
    ring
  have hbase : Integrable (fun ω => mertonValue r μ σ γ T 0 x-γ*σ^2/2*L ω) P :=
    (integrable_const _).sub (hL.const_mul _)
  have hi := (hbase.add hM.1).congr heq.symm
  have hE : (∫ ω, (V (ω,T))^(1-γ)/(1-γ) ∂P) =
      mertonValue r μ σ γ T 0 x-γ*σ^2/2*(∫ ω, L ω ∂P) := by
    rw [integral_congr_ae heq,integral_add hbase hM.1,hM.2,add_zero,
      integral_sub (integrable_const _) (hL.const_mul _),integral_const,probReal_univ,one_smul,
      integral_const_mul]
  refine ⟨hi,hE,?_⟩
  rw [hE]
  have hn : 0 ≤ ∫ ω, L ω ∂P := integral_nonneg fun ω => integral_nonneg fun t => by
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_pos_of_pos (hpos (ω,t)) _).le) (sq_nonneg _)
  have : 0 ≤ γ*σ^2/2*(∫ ω, L ω ∂P) := by positivity
  linarith

/-- The loss vanishes for the constant admissible strategy. -/
theorem merton_optimal_attainment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω × ℝ → ℝ) (M : Ω → ℝ)
    (r μ σ γ T x : ℝ) (hσ : σ ≠ 0) (hγ : 0 < γ) (hγ1 : γ ≠ 1)
    (hV : Measurable V) (hpos : ∀ z, 0 < V z)
    (hmom : Integrable (fun z => (V z)^(2*(1-γ))) (P.prod (volume.restrict (Icc 0 T))))
    (hIto : ∀ᵐ ω ∂P, mertonValue r μ σ γ T T (V (ω,T)) = mertonValue r μ σ γ T 0 x+
      (∫ t in Icc 0 T, mertonGenerator r μ σ γ T t (V (ω,t)) ((μ-r)/(γ*σ^2)))+M ω)
    (hMean : MemLp (fun z : Ω × ℝ => σ*((μ-r)/(γ*σ^2))*V z*deriv (mertonValue r μ σ γ T z.2) (V z)) 2
      (P.prod (volume.restrict (Icc 0 T))) → Integrable M P ∧ (∫ ω, M ω ∂P) = 0) :
    (∫ ω, (V (ω,T))^(1-γ)/(1-γ) ∂P) = mertonValue r μ σ γ T 0 x := by
  have h := merton_expected_utility P V (fun _ => (μ-r)/(γ*σ^2)) M r μ σ γ T x
    ‖(μ-r)/(γ*σ^2)‖ hσ hγ hγ1 hV measurable_const hpos (fun _ => le_rfl) hmom hIto hMean
  simpa using h.2.1

theorem merton_time_shift (r μ σ γ T t x : ℝ) :
    mertonValue r μ σ γ T t x = mertonValue r μ σ γ (T-t) 0 x := by
  simp [mertonValue]

end Asakura.FullAudit
