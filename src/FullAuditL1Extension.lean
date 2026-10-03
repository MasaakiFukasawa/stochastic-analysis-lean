import Chapter1WrittenL1
import ManuscriptExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit

/-- The actual dense domain in the manuscript: L2 viewed inside L1. -/
def squareIntegrableDomain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    Set (Lp ℝ 1 P) := {X | MemLp X 2 P}

/-- The printed cutoff, including its L1 convergence, proves density in the L1 topology. -/
theorem squareIntegrableDomain_dense {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] : Dense (squareIntegrableDomain P) := by
  intro X
  let f := (Lp.aestronglyMeasurable X).mk X
  have hfm : Measurable f := (Lp.aestronglyMeasurable X).stronglyMeasurable_mk.measurable
  have hfe : f =ᵐ[P] X := (Lp.aestronglyMeasurable X).ae_eq_mk.symm
  have hfi : Integrable f P := (L1.integrable_coeFn X).congr hfe.symm
  let fN := fun n : ℕ => {ω | |f ω| ≤ (n : ℝ)}.indicator f
  have hN2 : ∀ n, MemLp (fN n) 2 P :=
    fun n => Asakura.Chapter1Written.cutoff_L2 hfm n
  have hN1 : ∀ n, Integrable (fN n) P := fun n => (hN2 n).integrable (by norm_num)
  let XN := fun n => (hN1 n).toL1 (fN n)
  have hXN : ∀ n, XN n ∈ squareIntegrableDomain P := by
    intro n
    change MemLp (XN n) 2 P
    exact (memLp_congr_ae (hN1 n).coeFn_toL1).mpr (hN2 n)
  have ht : Tendsto XN atTop (𝓝 X) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    have h := Asakura.Chapter1Written.written_cutoff_eLpNorm_one hfm hfi
    apply h.congr
    intro n
    rw [eLpNorm_sub_comm]
    exact eLpNorm_congr_ae ((hN1 n).coeFn_toL1.symm.sub hfe)
  exact mem_closure_of_tendsto ht (Eventually.of_forall hXN)

/-- The appendix's sequence construction extends the L2-defined operator once
its printed L1 contraction has been established. This does not invoke an existing
conditional expectation on L1. -/
theorem l1_operator_extension {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : squareIntegrableDomain P → Lp ℝ 1 P)
    (hF : ∀ X Y, dist (F X) (F Y) ≤ dist X Y) :
    ∃! G : Lp ℝ 1 P → Lp ℝ 1 P,
      UniformContinuous G ∧ ∀ X : squareIntegrableDomain P, G X = F X := by
  apply Asakura.manuscript_uniform_extension _ (squareIntegrableDomain_dense P) F
  apply LipschitzWith.uniformContinuous (K := 1)
  exact LipschitzWith.of_dist_le_mul (by simpa only [NNReal.coe_one, one_mul] using hF)

/-- The positive-set argument printed for uniqueness, before swapping Y and Z. -/
theorem l1_order_from_positive_set {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {Y Z : Ω → ℝ} (hY : Integrable Y P) (hZ : Integrable Z P)
    (hYm : Measurable Y) (hZm : Measurable Z)
    (hzero : ∫ ω in {ω | 0 < Y ω-Z ω}, Y ω-Z ω ∂P = 0) :
    Y ≤ᵐ[P] Z := by
  let A := {ω | 0 < Y ω-Z ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hYm.sub hZm)
  have hnonneg : ∀ᵐ ω ∂P.restrict A, 0 ≤ Y ω-Z ω := by
    rw [ae_restrict_iff' hA]
    exact Eventually.of_forall fun _ h => le_of_lt h
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hY.sub hZ).integrableOn).mp hzero
  change (∀ᵐ ω ∂P.restrict A, Y ω-Z ω = 0) at hz
  rw [ae_restrict_iff' hA] at hz
  filter_upwards [hz] with ω hω
  by_contra h
  have hp : 0 < Y ω-Z ω := sub_pos.mpr (lt_of_not_ge h)
  exact (ne_of_gt hp) (hω hp)

/-- The uniqueness half of Proposition 1.1: use the two positive difference sets. -/
theorem l1_uniqueness_written {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) (hm : m ≤ m0) {Y Z : Ω → ℝ}
    (hY : Integrable Y P) (hZ : Integrable Z P)
    (hYm : Measurable[m] Y) (hZm : Measurable[m] Z)
    (heq : ∀ A, MeasurableSet[m] A → ∫ ω in A, Y ω ∂P = ∫ ω in A, Z ω ∂P) :
    Y =ᵐ[P] Z := by
  have hYZ : Y ≤ᵐ[P] Z := by
    apply l1_order_from_positive_set P hY hZ (hYm.mono hm le_rfl) (hZm.mono hm le_rfl)
    rw [integral_sub hY.integrableOn hZ.integrableOn]
    exact sub_eq_zero.mpr (heq _ (measurableSet_lt (measurable_const (a := (0:ℝ))) (hYm.sub hZm)))
  have hZY : Z ≤ᵐ[P] Y := by
    apply l1_order_from_positive_set P hZ hY (hZm.mono hm le_rfl) (hYm.mono hm le_rfl)
    rw [integral_sub hZ.integrableOn hY.integrableOn]
    exact sub_eq_zero.mpr (heq _ (measurableSet_lt (measurable_const (a := (0:ℝ))) (hZm.sub hYm))).symm
  filter_upwards [hYZ, hZY] with ω h₁ h₂
  exact le_antisymm h₁ h₂

end Asakura.FullAudit
