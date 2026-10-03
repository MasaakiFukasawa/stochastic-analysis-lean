import Chapter7OrderInverse
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Monotone

open Set Filter
open scoped Topology
namespace Asakura.Chapter7

/-- Left continuity of the weak generalized inverse follows from preservation
of suprema. Jumps and flat pieces of the original clock are allowed. -/
theorem weak_inverse_left_order_continuous
    {α β : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [CompleteLinearOrder β] (F : α → β) (hF : Monotone F) :
    LeftOrdContinuous (fun s => sInf {t | s ≤ F t}) := by
  intro S s hS hs
  constructor
  · rintro _ ⟨y,hy,rfl⟩
    exact (generalized_inverse_monotone F).1 (hs.1 hy)
  · intro z hz
    change sInf {t | s ≤ F t} ≤ z
    rw [← sup_lt_eq_inf_ge F hF s]
    apply sSup_le
    intro t ht
    have hex : ∃ y ∈ S,F t < y := by
      by_contra hn
      have hh : s ≤ F t := hs.2 (by
        intro y hy
        exact le_of_not_gt (fun hh => hn ⟨y,hy,hh⟩))
      exact (not_lt_of_ge hh) ht
    obtain ⟨y,hy,hty⟩ := hex
    have hty' : t ≤ sInf {u | y ≤ F u} := by
      rw [← sup_lt_eq_inf_ge F hF y]
      exact le_sSup hty
    exact hty'.trans (hz (mem_image_of_mem _ hy))

/-- Right continuity of the strict generalized inverse follows from
preservation of infima. -/
theorem strict_inverse_right_order_continuous
    {α β : Type*} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (F : α → β) : RightOrdContinuous (fun s => sInf {t | s < F t}) := by
  intro S s hS hs
  constructor
  · rintro _ ⟨y,hy,rfl⟩
    exact (generalized_inverse_monotone F).2 (hs.1 hy)
  · intro z hz
    apply le_sInf
    intro t ht
    have hex : ∃ y ∈ S,y < F t := by
      by_contra hn
      have hh : F t ≤ s := hs.2 (by
        intro y hy
        exact le_of_not_gt (fun hh => hn ⟨y,hy,hh⟩))
      exact (not_lt_of_ge hh) ht
    obtain ⟨y,hy,hty⟩ := hex
    exact (hz (mem_image_of_mem _ hy)).trans (sInf_le hty)

theorem generalized_inverse_one_sided_continuity
    {α β : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    (F : α → β) (hF : Monotone F) (s : β) :
    ContinuousWithinAt (fun r => sInf {t | r ≤ F t}) (Iic s) s ∧
    ContinuousWithinAt (fun r => sInf {t | r < F t}) (Ici s) s :=
  ⟨(weak_inverse_left_order_continuous F hF).continuousWithinAt_Iic,
   (strict_inverse_right_order_continuous F).continuousWithinAt_Ici⟩

/-- The right limit of the weak inverse has the strict inverse as its
order boundary, including levels inside jumps of F. -/
theorem weak_inverse_right_boundary
    {α β : Type*} [CompleteLinearOrder α]
    [CompleteLinearOrder β] [DenselyOrdered β] (F : α → β) (s : β) :
    sInf ((fun r => sInf {t | r ≤ F t}) '' Ioi s) = sInf {t | s < F t} := by
  apply le_antisymm
  · apply le_sInf
    intro t ht
    obtain ⟨r,hsr,hrt⟩ := exists_between ht
    exact (sInf_le (mem_image_of_mem (fun r => sInf {u | r ≤ F u}) hsr)).trans
      (sInf_le hrt.le)
  · apply le_sInf
    rintro _ ⟨r,hr,rfl⟩
    exact sInf_le_sInf (fun t ht => hr.trans_le ht)

theorem weak_inverse_right_limit
    {α β : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β] (F : α → β) (s : β) :
    Tendsto (fun r => sInf {t | r ≤ F t}) (𝓝[>] s) (𝓝 (sInf {t | s < F t})) := by
  have hh := (generalized_inverse_monotone F).1.tendsto_nhdsGT s
  rwa [weak_inverse_right_boundary] at hh

/-- Right continuity, rather than full continuity, is enough to attain a
weak crossing level. This is the endpoint fact needed for stopping events. -/
theorem right_continuous_inverse_attains
    {α β : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    (F : α → β) (hF : Monotone F)
    (hc : ∀ t,ContinuousWithinAt F (Ici t) t)
    (s : β) (hne : ∃ t,s ≤ F t) : s ≤ F (sInf {t | s ≤ F t}) := by
  have hh := hF.monotoneOn {t | s ≤ F t}
  have hsub : {t | s ≤ F t} ⊆ Ici (sInf {t | s ≤ F t}) :=
    fun t ht => sInf_le ht
  have he := hh.map_csInf_of_continuousWithinAt
    ((hc _).mono hsub) hne (OrderBot.bddBelow _)
  rw [he]
  apply le_sInf
  rintro _ ⟨t,ht,rfl⟩
  exact ht

theorem right_continuous_inverse_event
    {α β : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    (F : α → β) (hF : Monotone F)
    (hc : ∀ t,ContinuousWithinAt F (Ici t) t)
    (s : β) (hne : ∃ t,s ≤ F t) (t : α) :
    F t < s ↔ t < sInf {u | s ≤ F u} := by
  have he : sInf {u | s ≤ F u} ≤ t ↔ s ≤ F t :=
    ⟨fun h => (right_continuous_inverse_attains F hF hc s hne).trans (hF h),
      fun h => sInf_le h⟩
  exact not_le.symm.trans (he.not.symm.trans not_le)

end Asakura.Chapter7
