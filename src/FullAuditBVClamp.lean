import FullAuditBVMeasure
import Mathlib.Topology.Order.ProjIcc

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

noncomputable def intervalClamp (a b : ℝ) (hab : a ≤ b) (x : ℝ) : ℝ := (projIcc a b hab x : ℝ)

theorem intervalClamp_mem (a b : ℝ) (hab : a ≤ b) (x : ℝ) : intervalClamp a b hab x ∈ Icc a b :=
  (projIcc a b hab x).property

theorem intervalClamp_mono (a b : ℝ) (hab : a ≤ b) : Monotone (intervalClamp a b hab) :=
  monotone_projIcc hab

theorem intervalClamp_continuous (a b : ℝ) (hab : a ≤ b) : Continuous (intervalClamp a b hab) :=
  continuous_subtype_val.comp continuous_projIcc

theorem intervalClamp_eq (a b : ℝ) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Icc a b) :
    intervalClamp a b hab x = x := by simp [intervalClamp,projIcc_of_mem hab hx]

/-- Right continuity at the endpoints is preserved by constant extension. -/
theorem intervalClamp_right_continuous (a b : ℝ) (hab : a ≤ b) (C : ℝ → ℝ)
    (hr : ∀ x ∈ Icc a b, ContinuousWithinAt C (Icc a b ∩ Ici x) x) :
    ∀ x, ContinuousWithinAt (C ∘ intervalClamp a b hab) (Ici x) x := by
  intro x
  apply (hr _ (intervalClamp_mem a b hab x)).comp (intervalClamp_continuous a b hab).continuousWithinAt
  intro y hy
  exact ⟨intervalClamp_mem a b hab y,intervalClamp_mono a b hab hy⟩

/-- Constant extension does not increase the total variation. -/
theorem intervalClamp_boundedVariation (a b : ℝ) (hab : a ≤ b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b)) : BoundedVariationOn (C ∘ intervalClamp a b hab) univ := by
  apply ne_of_lt
  exact (eVariationOn.comp_le_of_monotoneOn C _ ((intervalClamp_mono a b hab).monotoneOn univ)
    (fun x _ => intervalClamp_mem a b hab x)).trans_lt hC.lt_top

noncomputable def intervalStieltjes (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x) : StieltjesFunction ℝ where
  toFun := A ∘ intervalClamp a b hab
  mono' := fun x y hxy => hA (intervalClamp_mem a b hab x) (intervalClamp_mem a b hab y) (intervalClamp_mono a b hab hxy)
  right_continuous' := intervalClamp_right_continuous a b hab A hr

theorem intervalStieltjes_finite (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x) :
    IsFiniteMeasure (intervalStieltjes a b hab A hA hr).measure := by
  apply (intervalStieltjes a b hab A hA hr).isFiniteMeasure_of_forall_abs_le (C := |A a|+|A b|)
  intro x
  have hl := hA (left_mem_Icc.mpr hab) (intervalClamp_mem a b hab x) (intervalClamp_mem a b hab x).1
  have hu := hA (intervalClamp_mem a b hab x) (right_mem_Icc.mpr hab) (intervalClamp_mem a b hab x).2
  change |A (intervalClamp a b hab x)| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (A b),neg_abs_le (A a),abs_nonneg (A a),abs_nonneg (A b)]

/-- Interval masses of the extension reproduce the original increments. -/
theorem intervalStieltjes_Ioc_real (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x ∈ Icc a b, ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (s t : ℝ) (hst : s ≤ t) :
    (intervalStieltjes a b hab A hA hr).measure.real (Ioc s t) =
      A (intervalClamp a b hab t)-A (intervalClamp a b hab s) := by
  rw [measureReal_def,StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((intervalStieltjes a b hab A hA hr).mono hst))]
  rfl

end Asakura.FullAudit
