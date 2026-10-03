import Chapter2IncreasingLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000

def cappedPath (a k : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ := min k (A r-A a)

theorem capped_path_monotone (a b k : ℝ) (A : ℝ → ℝ) (hA : MonotoneOn A (Icc a b)) :
    MonotoneOn (cappedPath a k A) (Icc a b) := by
  intro s hs t ht hst
  exact min_le_min_left k (sub_le_sub_right (hA hs ht hst) _)

theorem capped_path_continuous (a b k : ℝ) (A : ℝ → ℝ) (hA : ContinuousOn A (Icc a b)) :
    ContinuousOn (cappedPath a k A) (Icc a b) :=
  (continuous_const.min continuous_id).comp_continuousOn (hA.sub continuousOn_const)

theorem capped_path_mass_bound (a b k : ℝ) (A : ℝ → ℝ) (hk : 0 ≤ k) :
    cappedPath a k A b-cappedPath a k A a ≤ k := by
  simp only [cappedPath,sub_self,min_eq_right hk,sub_zero]
  exact min_le_left _ _

theorem capped_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    (a k : ℝ) (A : Ω → ℝ → ℝ) (hm : ∀ r, Measurable (fun ω => A ω r)) (r : ℝ) :
    Measurable (fun ω => cappedPath a k (A ω) r) :=
  measurable_const.min ((hm r).sub (hm a))

theorem capped_path_adapted {Ω : Type*} (a b k : ℝ) (hab : a ≤ b)
    (F : Icc a b → MeasurableSpace Ω) (hF : Monotone F) (A : Ω → ℝ → ℝ)
    (ha : ∀ t : Icc a b, Measurable[F t] (fun ω => A ω t.val)) (t : Icc a b) :
    Measurable[F t] (fun ω => cappedPath a k (A ω) t.val) := by
  have h0 := (ha ⟨a,left_mem_Icc.2 hab⟩).mono (hF t.property.1) le_rfl
  exact measurable_const.min ((ha t).sub h0)

/-- Outside the event that the terminal mass exceeds k, capping changes
the distribution function only by a constant, hence leaves its whole
Stieltjes measure on the finite interval unchanged. -/
theorem capped_stieltjes_measure_agrees
    (a b k : ℝ) (hab : a ≤ b) (hk : 0 ≤ k) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b)) (hc : ContinuousOn A (Icc a b))
    (hgood : A b-A a ≤ k) :
    let hB := capped_path_monotone a b k A hA
    let hcB := capped_path_continuous a b k A hc
    (intervalStieltjes a b hab (cappedPath a k A) hB
      (fun x hx => (hcB x hx).mono inter_subset_left)).measure =
    (intervalStieltjes a b hab A hA
      (fun x hx => (hc x hx).mono inter_subset_left)).measure := by
  intro hB hcB
  apply interval_stieltjes_measure_congr_add_const a b hab A (cappedPath a k A) hA hB
    (fun x hx => (hc x hx).mono inter_subset_left)
    (fun x hx => (hcB x hx).mono inter_subset_left) (-A a)
  intro x hx
  have hle : A x-A a ≤ k := (sub_le_sub_right (hA hx (right_mem_Icc.2 hab) hx.2) _).trans hgood
  change min k (A x-A a) = A x + -A a
  rw [min_eq_right hle]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.capped_path_monotone
#print axioms Asakura.Chapter2Complete.capped_path_continuous
#print axioms Asakura.Chapter2Complete.capped_path_mass_bound
#print axioms Asakura.Chapter2Complete.capped_path_measurable
#print axioms Asakura.Chapter2Complete.capped_path_adapted
#print axioms Asakura.Chapter2Complete.capped_stieltjes_measure_agrees
