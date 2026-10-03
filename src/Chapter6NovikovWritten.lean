import Chapter6NovikovStoppedMoment
import Chapter6LocalMaximalMoment
import Chapter5DominatedLocalMean
import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's strict Novikov condition, from its original local
martingale and quadratic variation. The proof constructs the exponential,
uses Holder and Doob, proves an integrable maximum and then takes the
localization limit. No martingale or uniform-integrability conclusion is
assumed in its hypotheses. -/
theorem novikov_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (γ : ℝ) (hγ : 1/2 < γ)
    (hEi : Integrable (fun w => Real.exp (γ*C (τ w) w)) P) :
    let M := fun t w => Real.exp (Z (min (τ w) t) w-C (min (τ w) t) w/2)
    (∀ t,Integrable (M t) P) ∧
    (∀ s t,s ≤ t → P[M t|F s] =ᵐ[P] M s) ∧
    ((∫ w,M ⊤ w ∂P) = 1) ∧
    (∃ B : Ω → ℝ,Integrable B P ∧ ∀ w t,|M t w| ≤ B w) := by
  let Z' := fun t w => Z (min (τ w) t) w
  let C' := fun t w => C (min (τ w) t) w
  let M := fun t w => Real.exp (Z' t w-C' t w/2)
  have hZ' := hZ.stopped P F hF hle τ hτ
  have hC' := hC.stopped P F hF hle τ hτ
  have hZr := open_process_stopped_regular F hF Z (hZ.adapted P F) (hZ.path P F) τ hτ hτt
  have hCr := hC.stopped_regular P F hF hle hZ hZ τ hτ hτt
  have hMa t : Measurable[F t] (M t) :=
    Real.continuous_exp.measurable.comp ((hZr.1 t).sub ((hCr.1 t).div_const 2))
  have hMc w : Continuous (fun t => M t w) :=
    Real.continuous_exp.comp ((hZr.2 w).sub ((hCr.2 w).div_const 2))
  have hMp t w : 0 ≤ M t w := (Real.exp_pos _).le
  have hL := stochastic_exponential_local P hT F hF hle hnull Z' C' hZ' hC'
  obtain ⟨α,p,ha,hag,hp,hg⟩ := novikov_exponents γ hγ
  have hp0 : 0 < p := by linarith
  have ha0 : 0 < α := by linarith
  let K := (∫⁻ w,ENNReal.ofReal (Real.exp (γ*C (τ w) w)) ∂P)^((α-1)/α)
  have hmono := local_quadratic_variation_monotone P F hF hle hnull Z C hZ hC
  have hmom (σ : Ω → ClosedTime T) (hs : ∀ t,MeasurableSet[F t] {w | σ w ≤ t}) (hst : ∀ w,σ w < ⊤) :
      (∫⁻ w,ENNReal.ofReal (M (σ w) w)^p ∂P) ≤ K := by
    have hh := novikov_stopped_moment P hT F hF hle hnull Z' C' hZ' hC' σ hs hst
      (fun w => C (τ w) w) (hmono.mono fun w hw =>
        hw ((min_le_left _ _).trans_lt (hτt w)) (hτt w) (min_le_left _ _))
      α p γ ha (by linarith) hg
    dsimp only [M]
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp0.le,← Real.exp_mul]
    simpa only [K,mul_comm] using hh
  have hnorm := positive_local_path_moment P F hF hle M hMa hMc hMp hL τ hτt
    (fun w t => by dsimp [M,Z',C']; rw [← min_assoc, min_self]) p hp K hmom
  have hfinite : (∫⁻ w,ENNReal.ofReal (Real.exp (γ*C (τ w) w)) ∂P) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hEi (.of_forall (fun _ => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_ne_top
  have hK : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hfinite
  have hpath : MemLp (continuousPath M hMc) (ENNReal.ofReal p) P :=
    hnorm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK))
  have hpathi := hpath.integrable (by simpa using ENNReal.ofReal_le_ofReal hp.le : (1:ℝ≥0∞) ≤ ENNReal.ofReal p)
  have hMtopi : Integrable (M ⊤) P := hpathi.norm.mono'
    ((hMa ⊤).mono (hle ⊤) le_rfl).aestronglyMeasurable
    (.of_forall fun w => ContinuousMap.norm_coe_le_norm (continuousPath M hMc w) ⊤)
  have hmean0 := Asakura.Chapter5.dominated_local_terminal_mean P F hle _ hL
    (fun w => (hMc w).sub continuous_const)
    (fun w => ‖continuousPath M hMc w‖+1) (hpathi.norm.add (integrable_const (1:ℝ)))
    (.of_forall fun w t => (norm_sub_le (M t w) 1).trans (by
      have hh : ‖M t w‖ ≤ ‖continuousPath M hMc w‖ := ContinuousMap.norm_coe_le_norm (continuousPath M hMc w) t
      simpa only [norm_one] using add_le_add_left hh 1))
  have hmean : (∫ w,M ⊤ w ∂P) = 1 := by
    rw [integral_sub hMtopi (integrable_const (1:ℝ))] at hmean0
    have hone : (∫ _w,(1:ℝ) ∂P) = 1 := by simp
    rw [hone] at hmean0
    linarith
  have hmeanτ : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1 := by
    simpa only [M,Z',C',min_top_right] using hmean
  obtain ⟨_,hi,_,hm,_⟩ := stochastic_exponential_closed_martingale P hT F hF hle hnull
    Z C hZ hC τ hτ hτt hmeanτ
  exact ⟨hi,hm,hmean,⟨fun w => ‖continuousPath M hMc w‖,hpathi.norm,
    fun w t => by
      change |M t w| ≤ ‖continuousPath M hMc w‖
      rw [← Real.norm_eq_abs]
      exact ContinuousMap.norm_coe_le_norm (continuousPath M hMc w) t⟩⟩

end Asakura.Chapter6
