import FullAuditCLTTaylor
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.FullAudit

noncomputable def cltBump (a b x : ℝ) : ℝ := expNegInvGlue ((x-a)*(b-x))

/-- The exact exponential bump specified in the exercise, including endpoints. -/
theorem cltBump_formula (a b x : ℝ) (hab : a < b) :
    cltBump a b x = if x ∈ Ioo a b then Real.exp ((x-a)⁻¹*(x-b)⁻¹) else 0 := by
  by_cases hx : x ∈ Ioo a b
  · have hp : 0 < (x-a)*(b-x) := mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
    simp only [cltBump,expNegInvGlue,not_le.mpr hp,ite_false,ite_true,hx]
    congr 1
    rw [show b-x = -(x-b) by ring]
    simp only [mul_inv_rev,inv_neg]
    ring
  · have hp : (x-a)*(b-x) ≤ 0 := by
      by_cases hxa : x ≤ a
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxa) (sub_nonneg.mpr (hxa.trans hab.le))
      · have hbx : b ≤ x := le_of_not_gt (fun h => hx ⟨lt_of_not_ge hxa,h⟩)
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hab.le.trans hbx)) (sub_nonpos.mpr hbx)
    simp [cltBump,expNegInvGlue.zero_of_nonpos hp,hx]

theorem cltBump_smooth (a b : ℝ) : ContDiff ℝ ∞ (cltBump a b) :=
  expNegInvGlue.contDiff.comp ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id))

theorem cltBump_compact (a b : ℝ) (hab : a < b) : HasCompactSupport (cltBump a b) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := b))
  intro x hx
  rw [cltBump_formula a b x hab,if_neg (fun h => hx ⟨h.1.le,h.2.le⟩)]

theorem cltBump_integrable (a b : ℝ) (hab : a < b) : Integrable (cltBump a b) volume :=
  (cltBump_smooth a b).continuous.integrable_of_hasCompactSupport (cltBump_compact a b hab)

noncomputable def cltPrimitive (a b x : ℝ) : ℝ := ∫ y in Iic x, cltBump a b y

/-- The improper primitive equals an ordinary variable-endpoint integral. -/
theorem cltPrimitive_eq_interval (a b x : ℝ) (hab : a < b) :
    cltPrimitive a b x = ∫ y in a..x, cltBump a b y := by
  have hi := cltBump_integrable a b hab
  have hz : ∫ y in Iic a, cltBump a b y = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [cltBump_formula a b y hab,if_neg (fun h => not_lt_of_ge hy h.1)]
  have h := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := x) hi.integrableOn hi.integrableOn
  simpa only [hz,sub_zero,cltPrimitive] using h

/-- Fundamental theorem of calculus for the actual G in the exercise. -/
theorem cltPrimitive_hasDerivAt (a b x : ℝ) (hab : a < b) :
    HasDerivAt (cltPrimitive a b) (cltBump a b x) x := by
  have he : cltPrimitive a b = fun x => ∫ y in a..x, cltBump a b y :=
    funext fun x => cltPrimitive_eq_interval a b x hab
  rw [he]
  have hc := (cltBump_smooth a b).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem cltPrimitive_smooth (a b : ℝ) (hab : a < b) : ContDiff ℝ ∞ (cltPrimitive a b) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (cltPrimitive_hasDerivAt a b x hab).differentiableAt,?_⟩
  have he : deriv (cltPrimitive a b) = cltBump a b := funext fun x => (cltPrimitive_hasDerivAt a b x hab).deriv
  rw [he]
  exact cltBump_smooth a b

theorem cltPrimitive_end_pos (a b : ℝ) (hab : a < b) : 0 < cltPrimitive a b b := by
  rw [cltPrimitive_eq_interval a b b hab]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on ((cltBump_smooth a b).continuous.intervalIntegrable _ _)
    (fun x hx => expNegInvGlue.pos_of_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))) hab

/-- Exact values outside the transition interval and monotonicity inside. -/
theorem cltPrimitive_bounds (a b : ℝ) (hab : a < b) :
    (∀ x, 0 ≤ cltPrimitive a b x ∧ cltPrimitive a b x ≤ cltPrimitive a b b) ∧
    (∀ x ≤ a, cltPrimitive a b x = 0) ∧
    (∀ x ≥ b, cltPrimitive a b x = cltPrimitive a b b) := by
  have hi := cltBump_integrable a b hab
  have hpos : ∀ x, 0 ≤ cltBump a b x := fun x => expNegInvGlue.nonneg _
  have hzero : ∀ x ≤ a, cltPrimitive a b x = 0 := by
    intro x hx
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [cltBump_formula a b y hab,if_neg (fun h => not_lt_of_ge (hy.trans hx) h.1)]
  have htop : ∀ x ≥ b, cltPrimitive a b x = cltPrimitive a b b := by
    intro x hx
    have he : ∫ y in b..x, cltBump a b y = 0 := by
      calc
        _ = ∫ y in b..x, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le hx] at hy
          rw [cltBump_formula a b y hab,if_neg (fun h => not_lt_of_ge hy.1 h.2)]
        _ = 0 := by simp
    have h := intervalIntegral.integral_Iic_sub_Iic (a := b) (b := x) hi.integrableOn hi.integrableOn
    rw [he] at h
    exact sub_eq_zero.mp h
  refine ⟨fun x => ⟨integral_nonneg (fun y => hpos y),?_⟩,hzero,htop⟩
  by_cases hx : x ≤ b
  · exact setIntegral_mono_set hi.integrableOn (Eventually.of_forall hpos) (Eventually.of_forall (Iic_subset_Iic.mpr hx))
  · exact (htop x (le_of_not_ge hx)).le

noncomputable def cltCutoff (a b x : ℝ) : ℝ := 1 - (cltPrimitive a b b)⁻¹*cltPrimitive a b x

theorem cltCutoff_smooth (a b : ℝ) (hab : a < b) : ContDiff ℝ ∞ (cltCutoff a b) :=
  contDiff_const.sub (contDiff_const.mul (cltPrimitive_smooth a b hab))

/-- The lower and upper indicator bounds required in the exercise. -/
theorem cltCutoff_indicator_bounds (a b x : ℝ) (hab : a < b) :
    (Iic a).indicator (fun _ => (1:ℝ)) x ≤ cltCutoff a b x ∧
      cltCutoff a b x ≤ (Iio b).indicator (fun _ => (1:ℝ)) x := by
  have hp := cltPrimitive_end_pos a b hab
  have hb := cltPrimitive_bounds a b hab
  have h0 : 0 ≤ cltCutoff a b x := by
    dsimp [cltCutoff]
    have h := mul_le_mul_of_nonneg_left (hb.1 x).2 (inv_nonneg.mpr hp.le)
    rw [inv_mul_cancel₀ hp.ne'] at h
    linarith
  have h1 : cltCutoff a b x ≤ 1 := by
    dsimp [cltCutoff]
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hp.le) (hb.1 x).1)
  constructor
  · by_cases hx : x ≤ a
    · simp [Set.indicator,hx,cltCutoff,hb.2.1 x hx]
    · simpa [Set.indicator,hx] using h0
  · by_cases hx : x < b
    · simpa [Set.indicator,hx] using h1
    · simp [Set.indicator,hx,cltCutoff,hb.2.2 x (le_of_not_gt hx),hp.ne']

/-- All derivatives in the exercise really are bounded on the entire line,
including the function itself (order zero). -/
theorem cltCutoff_all_derivatives_bounded (a b : ℝ) (hab : a < b) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n (cltCutoff a b) x| ≤ C := by
  have hd : deriv (cltCutoff a b) = fun x => -(cltPrimitive a b b)⁻¹*cltBump a b x := by
    funext x
    have h := ((cltPrimitive_hasDerivAt a b x hab).const_mul (cltPrimitive a b b)⁻¹).const_sub 1
    change deriv (fun x => 1 - (cltPrimitive a b b)⁻¹*cltPrimitive a b x) x = _
    simpa only [neg_mul] using h.deriv
  have hc : HasCompactSupport (deriv (cltCutoff a b)) := by
    rw [hd]
    apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := b))
    intro x hx
    rw [cltBump_formula a b x hab,if_neg (fun h => hx ⟨h.1.le,h.2.le⟩),mul_zero]
  have hcs : ∀ n : ℕ, HasCompactSupport (iteratedDeriv (n+1) (cltCutoff a b)) := by
    intro n
    induction n with
    | zero => simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hc
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  intro n
  cases n with
  | zero =>
    refine ⟨1,zero_le_one,fun x => ?_⟩
    rw [iteratedDeriv_zero]
    have h := cltCutoff_indicator_bounds a b x hab
    have hl : (0:ℝ) ≤ (Iic a).indicator (fun _ => (1:ℝ)) x := by
      by_cases hx : x ∈ Iic a <;> simp [Set.indicator,hx]
    have hu : (Iio b).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
      by_cases hx : x ∈ Iio b <;> simp [Set.indicator,hx]
    rw [abs_of_nonneg (hl.trans h.1)]
    exact h.2.trans hu
  | succ n =>
    have ht := (cltCutoff_smooth a b hab).continuous_iteratedDeriv (n+1) (by simp)
    obtain ⟨C,hC⟩ := ht.bounded_above_of_compact_support (hcs n)
    refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
    have hh : |iteratedDeriv (n+1) (cltCutoff a b) x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x
    exact hh.trans (le_max_left _ _)

end Asakura.FullAudit
