import FullAuditL1Extension

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit

/-- C2 on the two sign sets gives the L1 bound for the L2 projection itself.
Only the Hilbert space projection is used in this construction. -/
theorem l2_projection_l1_bound {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0) (X : Lp ℝ 2 P) :
    ∫ ω, |(condExpL2 ℝ ℝ hm X : Lp ℝ 2 P) ω| ∂P ≤ ∫ ω, |X ω| ∂P := by
  let Y := (condExpL2 ℝ ℝ hm X : Lp ℝ 2 P)
  have hYa := aestronglyMeasurable_condExpL2 (𝕜 := ℝ) hm X
  let Y' := hYa.mk Y
  have hYm : Measurable[m] Y' := hYa.stronglyMeasurable_mk.measurable
  have he : Y' =ᵐ[P] Y := hYa.ae_eq_mk.symm
  have hi : Integrable Y P := (Lp.memLp Y).integrable (by norm_num)
  have hi' : Integrable Y' P := hi.congr he.symm
  have hset (A : Set Ω) (hA : MeasurableSet[m] A) :
      ∫ ω, A.indicator Y' ω ∂P = ∫ ω, A.indicator X ω ∂P := by
    rw [integral_indicator (hm _ hA), integral_indicator (hm _ hA)]
    calc
      _ = ∫ ω in A, Y ω ∂P := integral_congr_ae (ae_restrict_of_ae he)
      _ = _ := integral_condExpL2_eq_of_fin_meas_real (hm := hm) X hA (measure_ne_top _ _)
  have hb := Asakura.Chapter1Written.l1_bound_from_C2
    ((Lp.memLp X).integrable (by norm_num)) hi' (hYm.mono hm le_rfl)
    (hset _ (measurableSet_lt measurable_const hYm))
    (hset _ (measurableSet_lt hYm measurable_const))
  have heabs : (fun ω => |Y' ω|) =ᵐ[P] (fun ω => |Y ω|) := he.fun_comp abs
  rwa [integral_congr_ae heabs] at hb

/-- The contraction applies to differences by linearity of the L2 projection. -/
theorem l2_projection_l1_difference {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0) (X Z : Lp ℝ 2 P) :
    (∫ ω, |(condExpL2 ℝ ℝ hm X : Lp ℝ 2 P) ω-
      (condExpL2 ℝ ℝ hm Z : Lp ℝ 2 P) ω| ∂P) ≤ ∫ ω, |X ω-Z ω| ∂P := by
  have hb := l2_projection_l1_bound P hm (X-Z)
  have hlin : (condExpL2 ℝ ℝ hm (X-Z) : Lp ℝ 2 P) =
      (condExpL2 ℝ ℝ hm X : Lp ℝ 2 P)-(condExpL2 ℝ ℝ hm Z : Lp ℝ 2 P) := by
    simp
  rw [hlin] at hb
  have hY := integral_congr_ae (μ := P) ((Lp.coeFn_sub
    (condExpL2 ℝ ℝ hm X : Lp ℝ 2 P) (condExpL2 ℝ ℝ hm Z : Lp ℝ 2 P)).fun_comp abs)
  have hX := integral_congr_ae (μ := P) ((Lp.coeFn_sub X Z).fun_comp abs)
  simp only [Function.comp_def] at hY hX
  rw [hY, hX] at hb
  exact hb

noncomputable def l2ProjectionOnL1Domain {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    (X : squareIntegrableDomain P) : Lp ℝ 1 P :=
  let Y := (condExpL2 ℝ ℝ hm (X.property.toLp (X.val : Ω → ℝ)) : Lp ℝ 2 P)
  ((Lp.memLp Y).integrable (by norm_num)).toL1 Y

/-- L1 distance is the integral printed in the manuscript. -/
theorem l1_dist_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Lp ℝ 1 P) :
    dist X Y = ∫ ω, |X ω-Y ω| ∂P := by
  rw [dist_eq_norm, L1.norm_sub_eq_lintegral]
  symm
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    integral_norm_eq_lintegral_enorm (L1.integrable_coeFn X |>.sub (L1.integrable_coeFn Y)).aestronglyMeasurable

/-- The contraction on the actual dense domain, with no L1 conditional expectation input. -/
theorem l2ProjectionOnL1Domain_contraction {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    (X Z : squareIntegrableDomain P) :
    dist (l2ProjectionOnL1Domain P hm X) (l2ProjectionOnL1Domain P hm Z) ≤ dist X Z := by
  let X₂ := X.property.toLp (X.val : Ω → ℝ)
  let Z₂ := Z.property.toLp (Z.val : Ω → ℝ)
  let Y := (condExpL2 ℝ ℝ hm X₂ : Lp ℝ 2 P)
  let V := (condExpL2 ℝ ℝ hm Z₂ : Lp ℝ 2 P)
  have heX : X₂ =ᵐ[P] (X.val : Ω → ℝ) := X.property.coeFn_toLp
  have heZ : Z₂ =ᵐ[P] (Z.val : Ω → ℝ) := Z.property.coeFn_toLp
  have heY : l2ProjectionOnL1Domain P hm X =ᵐ[P] Y := ((Lp.memLp Y).integrable (by norm_num)).coeFn_toL1
  have heV : l2ProjectionOnL1Domain P hm Z =ᵐ[P] V := ((Lp.memLp V).integrable (by norm_num)).coeFn_toL1
  change dist (l2ProjectionOnL1Domain P hm X) (l2ProjectionOnL1Domain P hm Z) ≤ dist X.val Z.val
  have hiY := integral_congr_ae (μ := P) ((heY.sub heV).fun_comp abs)
  have hiX := integral_congr_ae (μ := P) ((heX.sub heZ).fun_comp abs)
  simp only [Function.comp_def, Pi.sub_apply] at hiY hiX
  rw [l1_dist_integral_abs, l1_dist_integral_abs, hiY, ← hiX]
  exact l2_projection_l1_difference P hm X₂ Z₂

/-- The manuscript's extension construction now applies to the concrete L2 projection. -/
theorem l1_projection_extension_exists {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0) :
    ∃! G : Lp ℝ 1 P → Lp ℝ 1 P,
      UniformContinuous G ∧ ∀ X : squareIntegrableDomain P,
        G X = l2ProjectionOnL1Domain P hm X := by
  exact l1_operator_extension P _ (l2ProjectionOnL1Domain_contraction P hm)

end Asakura.FullAudit
