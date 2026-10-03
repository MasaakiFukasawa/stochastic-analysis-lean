import FullAuditL2L1Projection

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.FullAudit

/-- Measurability survives the dense extension because the measurable L1 subspace is closed. -/
theorem l1_extension_measurable {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    (G : Lp ℝ 1 P → Lp ℝ 1 P) (hG : Continuous G)
    (he : ∀ X : squareIntegrableDomain P, G X = l2ProjectionOnL1Domain P hm X)
    (X : Lp ℝ 1 P) : AEStronglyMeasurable[m] (G X) P := by
  have hc : IsClosed {X : Lp ℝ 1 P | AEStronglyMeasurable[m] (G X) P} :=
    (isClosed_aestronglyMeasurable (F := ℝ) (p := 1) hm).preimage hG
  apply closure_minimal (s := squareIntegrableDomain P) _ hc (squareIntegrableDomain_dense P X)
  intro Z hZ
  change AEStronglyMeasurable[m] (G Z) P
  rw [he ⟨Z,hZ⟩]
  let Y := (condExpL2 ℝ ℝ hm (hZ.toLp (Z : Ω → ℝ)) : Lp ℝ 2 P)
  have hY : AEStronglyMeasurable[m] Y P := aestronglyMeasurable_condExpL2 (𝕜 := ℝ) hm _
  exact hY.congr ((Lp.memLp Y).integrable (by norm_num)).coeFn_toL1.symm

/-- C2 passes to the extension by continuity of integration on each fixed event. -/
theorem l1_extension_setIntegral {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    (G : Lp ℝ 1 P → Lp ℝ 1 P) (hG : Continuous G)
    (he : ∀ X : squareIntegrableDomain P, G X = l2ProjectionOnL1Domain P hm X)
    (A : Set Ω) (hA : MeasurableSet[m] A) (X : Lp ℝ 1 P) :
    ∫ ω in A, (G X) ω ∂P = ∫ ω in A, X ω ∂P := by
  have hh := Continuous.ext_on (squareIntegrableDomain_dense P)
    ((continuous_setIntegral A).comp hG) (continuous_setIntegral A) (g := fun Z : Lp ℝ 1 P => ∫ ω in A, Z ω ∂P) ?_
  · exact congrFun hh X
  intro Z hZ
  change (∫ ω in A, (G Z) ω ∂P) = ∫ ω in A, Z ω ∂P
  rw [he ⟨Z,hZ⟩]
  let Z₂ := hZ.toLp (Z : Ω → ℝ)
  let Y := (condExpL2 ℝ ℝ hm Z₂ : Lp ℝ 2 P)
  have heY : l2ProjectionOnL1Domain P hm ⟨Z,hZ⟩ =ᵐ[P] Y :=
    ((Lp.memLp Y).integrable (by norm_num)).coeFn_toL1
  calc
    _ = ∫ ω in A, Y ω ∂P := integral_congr_ae (ae_restrict_of_ae heY)
    _ = ∫ ω in A, Z₂ ω ∂P :=
      integral_condExpL2_eq_of_fin_meas_real (hm := hm) Z₂ hA (measure_ne_top _ _)
    _ = _ := integral_congr_ae (ae_restrict_of_ae hZ.coeFn_toLp)

/-- The printed positive-set uniqueness argument also applies to L1 equivalence classes. -/
theorem l1_uniqueness_classes {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) (hm : m ≤ m0) (Y Z : Lp ℝ 1 P)
    (hY : AEStronglyMeasurable[m] Y P) (hZ : AEStronglyMeasurable[m] Z P)
    (heq : ∀ A, MeasurableSet[m] A → ∫ ω in A, Y ω ∂P = ∫ ω in A, Z ω ∂P) : Y=Z := by
  have hy : hY.mk Y =ᵐ[P] Y := hY.ae_eq_mk.symm
  have hz : hZ.mk Z =ᵐ[P] Z := hZ.ae_eq_mk.symm
  have hid := l1_uniqueness_written P hm
    ((L1.integrable_coeFn Y).congr hy.symm) ((L1.integrable_coeFn Z).congr hz.symm)
    hY.stronglyMeasurable_mk.measurable hZ.stronglyMeasurable_mk.measurable
    (fun A hA => (integral_congr_ae (ae_restrict_of_ae hy)).trans
      ((heq A hA).trans (integral_congr_ae (ae_restrict_of_ae hz)).symm))
  exact Lp.ext (hy.symm.trans (hid.trans hz))

/-- Full integral characterization for the operator constructed by the manuscript's extension. -/
theorem l1_extension_characterization {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0) :
    ∃ G : Lp ℝ 1 P → Lp ℝ 1 P, UniformContinuous G ∧
      (∀ X : squareIntegrableDomain P, G X = l2ProjectionOnL1Domain P hm X) ∧
      ∀ X Y : Lp ℝ 1 P, AEStronglyMeasurable[m] Y P →
        (Y=G X ↔ ∀ A, MeasurableSet[m] A → ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P) := by
  obtain ⟨G, ⟨hG,he⟩, _⟩ := l1_projection_extension_exists P hm
  refine ⟨G,hG,he,?_⟩
  intro X Y hY
  constructor
  · rintro rfl A hA
    exact l1_extension_setIntegral P hm G hG.continuous he A hA X
  · intro htests
    apply l1_uniqueness_classes P hm Y (G X) hY (l1_extension_measurable P hm G hG.continuous he X)
    intro A hA
    exact (htests A hA).trans (l1_extension_setIntegral P hm G hG.continuous he A hA X).symm

/-- The linearity step for the dense extension, proved using the integral characterization. -/
theorem l1_extension_linear {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    (G : Lp ℝ 1 P → Lp ℝ 1 P) (hG : Continuous G)
    (he : ∀ X : squareIntegrableDomain P, G X = l2ProjectionOnL1Domain P hm X) :
    (∀ X Y, G (X+Y)=G X+G Y) ∧ (∀ (a : ℝ) X, G (a • X)=a • G X) := by
  have hgm := l1_extension_measurable P hm G hG he
  have hgi := l1_extension_setIntegral P hm G hG he
  have hiadd (A : Set Ω) (X Y : Lp ℝ 1 P) :
      ∫ ω in A, (X+Y) ω ∂P = (∫ ω in A, X ω ∂P)+(∫ ω in A, Y ω ∂P) := by
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add X Y))]
    exact integral_add (L1.integrable_coeFn X).integrableOn (L1.integrable_coeFn Y).integrableOn
  have hismul (A : Set Ω) (a : ℝ) (X : Lp ℝ 1 P) :
      ∫ ω in A, (a • X) ω ∂P = a * ∫ ω in A, X ω ∂P := by
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul a X))]
    exact integral_const_mul _ _
  constructor
  · intro X Y
    apply l1_uniqueness_classes P hm _ _ (hgm _)
      (((hgm X).add (hgm Y)).congr (Lp.coeFn_add (G X) (G Y)).symm)
    intro A hA
    rw [hgi A hA, hiadd, hiadd, hgi A hA, hgi A hA]
  · intro a X
    apply l1_uniqueness_classes P hm _ _ (hgm _)
      (((hgm X).const_smul a).congr (Lp.coeFn_smul a (G X)).symm)
    intro A hA
    rw [hgi A hA, hismul, hismul, hgi A hA]

/-- Proposition 1.1's continuous linear extension, constructed from L2 by the
written cutoff and extension argument and characterized by the written sign-set uniqueness. -/
theorem l1_conditional_operator_written {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0) :
    ∃ L : Lp ℝ 1 P →L[ℝ] Lp ℝ 1 P,
      (∀ X : squareIntegrableDomain P, L X = l2ProjectionOnL1Domain P hm X) ∧
      (∀ X, AEStronglyMeasurable[m] (L X) P) ∧
      ∀ X Y : Lp ℝ 1 P, AEStronglyMeasurable[m] Y P →
        (Y=L X ↔ ∀ A, MeasurableSet[m] A → ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P) := by
  obtain ⟨G, ⟨hG,he⟩, _⟩ := l1_projection_extension_exists P hm
  have hl := l1_extension_linear P hm G hG.continuous he
  let L : Lp ℝ 1 P →L[ℝ] Lp ℝ 1 P :=
    { toFun := G
      map_add' := hl.1
      map_smul' := hl.2
      cont := hG.continuous }
  refine ⟨L,he,l1_extension_measurable P hm G hG.continuous he,?_⟩
  intro X Y hY
  constructor
  · rintro rfl A hA
    exact l1_extension_setIntegral P hm G hG.continuous he A hA X
  · intro htests
    apply l1_uniqueness_classes P hm Y (G X) hY (l1_extension_measurable P hm G hG.continuous he X)
    intro A hA
    exact (htests A hA).trans (l1_extension_setIntegral P hm G hG.continuous he A hA X).symm

end Asakura.FullAudit
