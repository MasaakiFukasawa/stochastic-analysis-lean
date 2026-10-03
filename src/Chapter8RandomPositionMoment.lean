import Chapter8RandomVolterraBound
import Chapter4PathEvaluationMoment

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- A finite-path L2 bound supplies continuity of the endpoint second moment.
This is used before each application of Gronwall, not assumed of the SDE. -/
theorem path_square_moment_continuous {Ω D E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace D] [CompactSpace D] [FirstCountableTopology D]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (X : Ω → C(D,E)) (hm : Measurable X) (h2 : MemLp X 2 P) :
    Continuous (fun t : D => ∫ w,‖X w t‖^2 ∂P) := by
  apply continuous_of_dominated (bound := fun w => ‖X w‖^2)
  · intro t
    exact (((continuous_eval_const t).measurable.comp hm).norm.pow_const 2).aestronglyMeasurable
  · intro t
    exact .of_forall (fun w => by
      simpa only [Real.norm_eq_abs,abs_sq] using pow_le_pow_left₀ (norm_nonneg _) ((X w).norm_coe_le_norm t) 2)
  · exact h2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  · exact .of_forall (fun w => (X w).continuous.norm.pow 2)

/-- The sum estimate is applied to actual square-integrable random vectors. -/
theorem random_three_sum_square {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (A B C : Ω → E) (hA : MemLp A 2 P) (hB : MemLp B 2 P) (hC : MemLp C 2 P) :
    (∫ w,‖A w+B w+C w‖^2 ∂P)≤3*((∫ w,‖A w‖^2 ∂P)+(∫ w,‖B w‖^2 ∂P)+(∫ w,‖C w‖^2 ∂P)) := by
  have ha := hA.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hb := hB.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := hC.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  calc
    _ ≤ ∫ w,3*(‖A w‖^2+‖B w‖^2+‖C w‖^2) ∂P :=
      integral_mono (((hA.add hB).add hC).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
        (((ha.add hb).add hc).const_mul 3) (fun w => norm_three_sum_square _ _ _)
    _ = _ := by
      rw [integral_const_mul]
      have hab : Integrable (fun w => ‖A w‖^2+‖B w‖^2) P := ha.add hb
      rw [integral_add hab hc,integral_add ha hb]

/-- The position representation gives the precise integral inequality
needed for a mass-independent second-moment estimate. -/
theorem random_position_moment_inequality {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (t : ℝ) (ht : 0≤t)
    (K : ℝ → E →L[ℝ] E) (hK : Continuous K)
    (H : Ω × ℝ → E) (hH : Measurable H)
    (hH2 : MemLp H 2 (P.prod (volume.restrict (Ioc 0 t))))
    (L : ℝ) (hL : 0≤L) (hKb : ∀ s∈Icc 0 t,‖K s‖≤L)
    (A N Q : Ω → E) (hA : MemLp A 2 P) (hN : MemLp N 2 P)
    (he : ∀ᵐ w ∂P,Q w=A w+(∫ s in 0..t,K s (H (w,s)))+N w)
    (u : ℝ → ℝ) (hu : ContinuousOn u (Icc 0 t))
    (CA CN G : ℝ) (hG : 0≤G)
    (ha : (∫ w,‖A w‖^2 ∂P)≤CA) (hn : (∫ w,‖N w‖^2 ∂P)≤CN)
    (hg : ∀ s∈Icc 0 t,(∫ w,‖H (w,s)‖^2 ∂P)≤G*(1+u s)) :
    (∫ w,‖Q w‖^2 ∂P)≤3*(CA+CN)+3*t*L^2*G*(t+∫ s in 0..t,u s) := by
  obtain ⟨hD,hDb⟩ := random_volterra_bound P t ht K hK H hH hH2 L hL hKb
  have hHi := hH2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi : IntervalIntegrable (fun s => ∫ w,‖H (w,s)‖^2 ∂P) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact hHi.integral_prod_right
  have hui := hu.intervalIntegrable_of_Icc (μ := volume) ht
  have hgi : IntervalIntegrable (fun s => G*(1+u s)) volume 0 t := (intervalIntegrable_const.add hui).const_mul G
  have hhb := intervalIntegral.integral_mono_on ht hi hgi hg
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const hui] at hhb
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hhb
  have hdb := hDb.trans (mul_le_mul_of_nonneg_left hhb (mul_nonneg ht (sq_nonneg _)))
  rw [integral_congr_ae (he.mono (fun w hw => by rw [hw]))]
  have hh := random_three_sum_square P A (fun w => ∫ s in 0..t,K s (H (w,s))) N hA hD hN
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hdb) hn) (by norm_num : (0:ℝ)≤3)
  exact hh.trans (by nlinarith [hsum])
end Asakura.Chapter8
