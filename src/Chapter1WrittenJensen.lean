import Chapter1WrittenSteps
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/- The proof of Jensen printed in chap1.tex: secant slopes, finite one-sided
 derivatives, rational supporting lines, continuity of their supremum,
 and a common full-measure set. No existing Jensen theorem is invoked. -/
open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter1Written

noncomputable def rightSlope (φ : ℝ → ℝ) (q : ℝ) : ℝ :=
  sInf (slope φ q '' {y : ℝ | q < y})

/-- The infimum used by the manuscript is the finite right derivative. -/
theorem rightSlope_eq_deriv {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (q : ℝ) :
    rightSlope φ q = derivWithin φ (Ioi q) q := by
  simpa [rightSlope] using
    (hφ.rightDeriv_eq_sInf_slope_of_mem_interior (x := q) (by simp)).symm

/-- Continuity is obtained from the two finite one-sided derivatives. -/
theorem convex_continuous_from_one_sided {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    Continuous φ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_iff_continuous_left'_right'.mpr
  exact ⟨(hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (x := x) (by simp)).continuousWithinAt,
    (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (x := x) (by simp)).continuousWithinAt⟩

/-- Equation jensenlb, with the right derivative defined by the manuscript's infimum. -/
theorem right_supporting_line {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (q x : ℝ) :
    φ q + rightSlope φ q * (x-q) ≤ φ x := by
  rw [rightSlope_eq_deriv hφ]
  rcases lt_trichotomy q x with h | h | h
  · have hs := hφ.rightDeriv_le_slope_of_mem_interior (x := q) (y := x) (by simp) (by simp) h
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · subst x
    simp
  · have hs := hφ.slope_le_leftDeriv_of_mem_interior (x := x) (y := q) (by simp) (by simp) h
    have hd := hφ.leftDeriv_le_rightDeriv_of_mem_interior (x := q) (by simp)
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp (hs.trans hd)
    nlinarith

noncomputable def rationalSupport (φ : ℝ → ℝ) (q : ℚ) (x : ℝ) : ℝ :=
  φ q + rightSlope φ q * (x-q)

noncomputable def rationalEnvelope (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨆ q : ℚ, rationalSupport φ q x

/-- Finiteness: every rational supporting line is bounded by φ at the given x. -/
theorem rational_support_bdd {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (x : ℝ) :
    BddAbove (range (fun q : ℚ => rationalSupport φ q x)) := by
  refine ⟨φ x, ?_⟩
  rintro y ⟨q, rfl⟩
  exact right_supporting_line hφ q x

/-- The envelope is convex by taking the supremum of its affine constituents. -/
theorem rational_envelope_convex {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    ConvexOn ℝ univ (rationalEnvelope φ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change (⨆ q : ℚ, rationalSupport φ q (a*x+b*y)) ≤
    a*rationalEnvelope φ x+b*rationalEnvelope φ y
  apply ciSup_le
  intro q
  have hx := le_ciSup (rational_support_bdd hφ x) q
  have hy := le_ciSup (rational_support_bdd hφ y) q
  calc
    rationalSupport φ q (a*x+b*y) = a*rationalSupport φ q x + b*rationalSupport φ q y := by
      dsimp [rationalSupport]
      linear_combination (rightSlope φ (q : ℝ) * (q : ℝ) - φ (q : ℝ)) * hab
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- Agreement on Q, followed by continuity and density, gives the exact representation. -/
theorem rational_envelope_eq {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    rationalEnvelope φ = φ := by
  have hQ : ∀ q : ℚ, rationalEnvelope φ (q : ℝ) = φ q := by
    intro q
    apply le_antisymm
    · exact ciSup_le (fun r => right_supporting_line hφ r q)
    · have h := le_ciSup (rational_support_bdd hφ (q : ℝ)) q
      simpa [rationalSupport, rationalEnvelope] using h
  exact Rat.denseRange_cast.equalizer
    (convex_continuous_from_one_sided (rational_envelope_convex hφ))
    (convex_continuous_from_one_sided hφ) (funext hQ)

/-- The full conditional Jensen conclusion, proved by the manuscript's rational lines.
The only expectation facts used are linearity, constants and monotonicity. -/
theorem conditional_jensen_written {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {G : MeasurableSpace Ω}
    (hG : G ≤ m) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    {X : Ω → ℝ} (hX : Integrable X P) (hφX : Integrable (φ ∘ X) P) :
    ∀ᵐ ω ∂P, φ (P[X | G] ω) ≤ P[φ ∘ X | G] ω := by
  have hline : ∀ q : ℚ, ∀ᵐ ω ∂P,
      rationalSupport φ q (P[X | G] ω) ≤ P[φ ∘ X | G] ω := by
    intro q
    let d := rightSlope φ (q : ℝ)
    let c := φ (q : ℝ) - d * (q : ℝ)
    have hlin : Integrable (fun ω => d * X ω + c) P :=
      (hX.const_mul d).add (integrable_const c)
    have hmono := condExp_mono hlin hφX (Eventually.of_forall (fun ω => by
      have h := right_supporting_line hφ (q : ℝ) (X ω)
      change d * X ω + c ≤ φ (X ω)
      dsimp [c, d] at *
      nlinarith)) (m := G)
    have hadd := condExp_add (hX.const_mul d) (integrable_const c) G
    have hmul := condExp_smul (μ := P) d X G
    filter_upwards [hmono, hadd, hmul] with ω hm ha hmul
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hG] at ha hmul
    have he : rationalSupport φ q (P[X | G] ω) = P[fun ω => d * X ω + c | G] ω := by
      change φ (q : ℝ) + d * (P[X | G] ω - (q : ℝ)) = _
      change P[fun ω => d * X ω + c | G] ω = P[fun ω => d * X ω | G] ω + c at ha
      rw [ha]
      change P[fun ω => d * X ω | G] ω = d * P[X | G] ω at hmul
      rw [hmul]
      dsimp [c]
      ring
    exact he.trans_le hm
  filter_upwards [ae_all_iff.mpr hline] with ω hω
  calc
    φ (P[X | G] ω) = rationalEnvelope φ (P[X | G] ω) :=
      (congrFun (rational_envelope_eq hφ) _).symm
    _ ≤ _ := ciSup_le hω

end Asakura.Chapter1Written
