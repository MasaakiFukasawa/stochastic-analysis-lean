import FullAuditBVClamp
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal ProbabilityTheory
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (a b : ℝ) (hab : a ≤ b) (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))

/-- The interval extension is constant below the left endpoint. -/
theorem interval_stieltjes_left_limit (ω : Ω) :
    Tendsto (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)) atBot (𝓝 (A ω a)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot a] with r hr
  change A ω a = A ω (intervalClamp a b hab r)
  simp only [intervalClamp,projIcc_of_le_left hab hr]

/-- The interval extension is constant above the right endpoint. -/
theorem interval_stieltjes_right_limit (ω : Ω) :
    Tendsto (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)) atTop (𝓝 (A ω b)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop b] with r hr
  change A ω b = A ω (intervalClamp a b hab r)
  simp only [intervalClamp,projIcc_of_right_le hab hr]

theorem interval_stieltjes_total_mass (ω : Ω) :
    (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure univ = ENNReal.ofReal (A ω b-A ω a) :=
  StieltjesFunction.measure_univ _
    (interval_stieltjes_left_limit a b hab A hA hr ω)
    (interval_stieltjes_right_limit a b hab A hA hr ω)

include hm

/-- Measurability of the random Stieltjes measure follows from interval
masses and the monotone-class construction, not an assumed kernel. -/
theorem random_stieltjes_measure_measurable :
    Measurable (fun ω => (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) := by
  letI (ω : Ω) : IsFiniteMeasure (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure :=
    intervalStieltjes_finite a b hab (A ω) (hA ω) (hr ω)
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic
  · rintro _ ⟨r,rfl⟩
    have he (ω) := (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure_Iic
      (interval_stieltjes_left_limit a b hab A hA hr ω) r
    simp only [he]
    exact ((hm (intervalClamp a b hab r)).sub (hm a)).ennreal_ofReal
  · simp only [interval_stieltjes_total_mass a b hab A hA hr]
    exact ((hm b).sub (hm a)).ennreal_ofReal

noncomputable def randomStieltjesKernel : Kernel Ω ℝ where
  toFun := fun ω => (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure
  measurable' := random_stieltjes_measure_measurable a b hab A hA hr hm

theorem random_stieltjes_kernel_finite (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K) :
    IsFiniteKernel (randomStieltjesKernel a b hab A hA hr hm) := by
  refine ⟨ENNReal.ofReal K,ENNReal.ofReal_lt_top,?_⟩
  intro ω
  change (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure univ ≤ ENNReal.ofReal K
  rw [interval_stieltjes_total_mass a b hab A hA hr]
  exact ENNReal.ofReal_le_ofReal (hK ω)

/-- The finite measure used for the Hilbert space in the density proof:
its value on B is the expectation of the pathwise Stieltjes mass of B. -/
theorem random_stieltjes_product_measure
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K) :
    ∃ μ : Measure (Ω × ℝ), IsFiniteMeasure μ ∧
      μ univ ≤ ENNReal.ofReal K ∧
      (∀ S, MeasurableSet S → μ S =
        ∫⁻ ω, (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure {t | (ω,t) ∈ S} ∂P) := by
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let μ := P ⊗ₘ κ
  have hmass : μ univ ≤ ENNReal.ofReal K := by
    rw [Measure.compProd_apply MeasurableSet.univ]
    calc
      (∫⁻ ω, κ ω univ ∂P) ≤ ∫⁻ ω, ENNReal.ofReal K ∂P := by
        apply lintegral_mono
        intro ω
        change (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure univ ≤ _
        rw [interval_stieltjes_total_mass a b hab A hA hr]
        exact ENNReal.ofReal_le_ofReal (hK ω)
      _ = ENNReal.ofReal K := by simp
  refine ⟨μ,⟨hmass.trans_lt ENNReal.ofReal_lt_top⟩,hmass,?_⟩
  intro S hS
  exact Measure.compProd_apply hS

omit hm in
/-- Continuity of the increasing path makes its Stieltjes measure atomless. -/
theorem interval_stieltjes_no_atoms (hcont : ∀ ω, Continuous (A ω)) (ω : Ω) :
    NullSingletonClass (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure := by
  constructor
  intro t
  rw [StieltjesFunction.measure_singleton]
  have hc : Continuous (intervalStieltjes a b hab (A ω) (hA ω) (hr ω)) :=
    (hcont ω).comp (intervalClamp_continuous a b hab)
  rw [hc.continuousAt.continuousWithinAt.leftLim_eq,sub_self,ENNReal.ofReal_zero]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.random_stieltjes_measure_measurable
#print axioms Asakura.Chapter2Complete.random_stieltjes_product_measure

#print axioms Asakura.Chapter2Complete.interval_stieltjes_no_atoms
