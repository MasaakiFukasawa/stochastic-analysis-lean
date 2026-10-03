import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

open Set Filter
open scoped Topology
namespace Asakura.Chapter7

/-- A countable dense family of comparisons suffices to establish constancy
on every flat portion, including random flat intervals. -/
theorem continuous_flat_of_dense
    {α β E : Type*} [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α] [LinearOrder β]
    [TopologicalSpace E] [T2Space E]
    (D : Set α) (hD : Dense D) (A : α → β) (hm : Monotone A)
    (X : α → E) (hc : Continuous X)
    (he : ∀ a ∈ D,∀ b ∈ D,A a = A b → X a = X b) :
    ∀ a b,A a = A b → X a = X b := by
  have hlt (a b : α) (hab : a < b) (heq : A a = A b) : X a = X b := by
    obtain ⟨r,hr,hrD⟩ := hD.inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hab)
    have hlevel (t : α) (ht : t ∈ Ioo a b) : A t = A a :=
      le_antisymm ((hm ht.2.le).trans_eq heq.symm) (hm ht.1.le)
    have hclosed : IsClosed {t | X t = X r} := isClosed_eq hc continuous_const
    have hsub : Ioo a b ∩ D ⊆ {t | X t = X r} := by
      intro t ht
      exact he t ht.2 r hrD ((hlevel t ht.1).trans (hlevel r hr).symm)
    have hI : Ioo a b ⊆ {t | X t = X r} :=
      (hD.open_subset_closure_inter isOpen_Ioo).trans (closure_minimal hsub hclosed)
    have hcc : Icc a b ⊆ {t | X t = X r} := by
      rw [← closure_Ioo hab.ne]
      exact closure_minimal hI hclosed
    exact (hcc ⟨le_rfl,hab.le⟩).trans (hcc ⟨hab.le,le_rfl⟩).symm
  intro a b heq
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hlt a b hab heq
  · exact congrArg X hab
  · exact (hlt b a hab heq.symm).symm

end Asakura.Chapter7
