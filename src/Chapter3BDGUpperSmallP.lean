import Chapter3RegularizedBDGUpperMoment
import Chapter3WrittenRegularization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's entire 0<p<2 upper BDG argument for bounded quadratic variation.
The stochastic integral, Holder and Doob estimates, and epsilon limit are all derived. -/
theorem bdg_upper_small_p_bounded_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 0 < p) (hp2 : p < 2)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ ω, A b ω ≤ K) :
    ∃ hx : ∀ ω, Continuous (fun t => X (min b t) ω),
      Integrable (fun ω => ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p) P ∧
      (∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P) ≤
        2^(2*p)*(2/p)^(p/2)*(∫ ω, A b ω^(p/2) ∂P) := by
  have hAp ω : 0 ≤ A b ω := by
    rw [← hA0 ω]
    exact hAm ω hT hb bot_le
  have hAm' : Measurable (A b) := (hA.adapted P F hX hX b hb).mono (hle b) le_rfl
  let ε := fun n : ℕ => (1/2:ℝ)^n
  have hεp n : 0 < ε n := pow_pos (by norm_num) n
  have hεb n : 0 ≤ ε n ∧ ε n ≤ 1 :=
    ⟨(hεp n).le,pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h n := regularized_bdg_upper_moment P hT F hF hle hnull X A hX hA hAm hAc hA0
    (ε n) p (hεp n) hp hp2 b hb K hK (Filter.Eventually.of_forall hbound)
  obtain ⟨hx,hi,hfirst⟩ := h 0
  refine ⟨hx,hi,?_⟩
  let U := fun n => ∫ ω, (ε n+A b ω)^(p/2)-(ε n)^(p/2) ∂P
  let V := fun n => ∫ ω, (ε n+A b ω)^(p/2) ∂P
  have hUp n : 0 ≤ U n := by
    apply integral_nonneg
    intro ω
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow (hεp n).le (by linarith [hAp ω]) (by positivity)
  have hu := Asakura.Chapter3Written.regularized_energy_expectation_limit P (A b) hAm' hp
    (fun ω => ⟨hAp ω,hbound ω⟩) ε hεlim hεb
  have hv := Asakura.Chapter3Written.shifted_bracket_moment_limit P (A b) hAm' hp
    (fun ω => ⟨hAp ω,hbound ω⟩) ε hεlim hεb
  have hineq n : (∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P) ≤
      (2^p*(4*(2/p))^(p/2))*(U n)^(p/2)*(V n)^((2-p)/2) := by
    obtain ⟨hx',_,hn⟩ := h n
    change (∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P) ≤
      2^p*(4*(2/p)*U n)^(p/2)*(V n)^(1-p/2) at hn
    rw [Real.mul_rpow (by positivity : 0 ≤ 4*(2/p)) (hUp n)] at hn
    have he : 1-p/2 = (2-p)/2 := by ring
    simpa only [he,mul_assoc] using hn
  have hlim := Asakura.Chapter3Written.bdg_regularized_bound_limit hp hp2 hu hv hineq
    (integral_nonneg (fun ω => Real.rpow_nonneg (hAp ω) _))
  have hc : 2^p*(4*(2/p))^(p/2) = 2^(2*p)*(2/p)^(p/2) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have h4 : (4:ℝ)^(p/2) = 2^p := by
      rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [h4,← mul_assoc,← Real.rpow_add (by norm_num)]
    congr 2
    ring
  simpa only [hc] using hlim

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_upper_small_p_bounded_variation
