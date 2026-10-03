import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Interval.Set.Basic
import Chapter7InverseClock

open Set
namespace Asakura.Chapter7

/-- The two boundaries of a downward-closed cut coincide in a dense order.
This proves the first two inverse-clock identities, including empty endpoints. -/
theorem lower_cut_boundary {α : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    (S : Set α) (hS : ∀ x ∈ S,∀ y,y ≤ x → y ∈ S) : sSup S = sInf Sᶜ := by
  have hle : sSup S ≤ sInf Sᶜ := by
    apply sSup_le
    intro x hx
    apply le_sInf
    intro y hy
    by_contra h
    exact hy (hS x hx y (le_of_lt (lt_of_not_ge h)))
  apply le_antisymm hle
  by_contra h
  obtain ⟨z,hz1,hz2⟩ := exists_between (lt_of_not_ge h)
  by_cases hz : z ∈ S
  · exact (not_lt_of_ge (le_sSup hz)) hz1
  · exact (not_lt_of_ge (sInf_le hz)) hz2

/-- Strict lower level sets have the same boundary as weak upper level sets. -/
theorem sup_lt_eq_inf_ge {α β : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [LinearOrder β] (F : α → β) (hF : Monotone F) (s : β) :
    sSup {t | F t < s} = sInf {t | s ≤ F t} := by
  have hh := lower_cut_boundary {t | F t < s}
    (fun x hx y hy => (hF hy).trans_lt hx)
  simpa only [compl_setOf,not_lt] using hh

/-- Weak lower level sets have the same boundary as strict upper level sets. -/
theorem sup_le_eq_inf_gt {α β : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [LinearOrder β] (F : α → β) (hF : Monotone F) (s : β) :
    sSup {t | F t ≤ s} = sInf {t | s < F t} := by
  have hh := lower_cut_boundary {t | F t ≤ s}
    (fun x hx y hy => (hF hy).trans hx)
  simpa only [compl_setOf,not_le] using hh

/-- Both generalized inverses are monotone, without continuity of F. -/
theorem generalized_inverse_monotone {α β : Type*} [CompleteLinearOrder α]
    [LinearOrder β] (F : α → β) :
    Monotone (fun s => sInf {t | s ≤ F t}) ∧ Monotone (fun s => sInf {t | s < F t}) := by
  constructor
  · intro s r hsr
    exact sInf_le_sInf (fun t ht => hsr.trans ht)
  · intro s r hsr
    exact sInf_le_sInf (fun t ht => hsr.trans_lt ht)

end Asakura.Chapter7
