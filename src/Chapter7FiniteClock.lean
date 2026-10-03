import Chapter7InverseContinuity
import Mathlib.Topology.Order.IntermediateValue

open Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 1200000

/-- The endpoint extension records F_* as the supremum of values strictly
before T. Hence an inverse below F_* never reaches the added endpoint. -/
theorem generalized_inverse_before_terminal
    {α β : Type*} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (F : α → β) (hend : F ⊤ = sSup (F '' Iio ⊤))
    (s : β) (hs : s < F ⊤) :
    (sInf {t | s ≤ F t}) < ⊤ ∧ (sInf {t | s < F t}) < ⊤ := by
  have hex : ∃ t,t < (⊤ : α) ∧ s < F t := by
    by_contra hn
    have hh : F ⊤ ≤ s := by
      rw [hend]
      apply sSup_le
      rintro _ ⟨t,ht,rfl⟩
      exact le_of_not_gt (fun h => hn ⟨t,ht,h⟩)
    exact hs.not_ge hh
  obtain ⟨t,ht,hs⟩ := hex
  exact ⟨(sInf_le (s := {u | s ≤ F u}) hs.le).trans_lt ht,
    (sInf_le (s := {u | s < F u}) hs).trans_lt ht⟩

/-- Adding the terminal point does not change the inverse defined on [0,T),
provided the level is strictly below F_*. -/
theorem generalized_inverse_endpoint_extension
    {α β : Type*} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (F : α → β) (hend : F ⊤ = sSup (F '' Iio ⊤))
    (s : β) (hs : s < F ⊤) :
    sInf {t | t < (⊤ : α) ∧ s ≤ F t} = sInf {t | s ≤ F t} ∧
    sInf {t | t < (⊤ : α) ∧ s < F t} = sInf {t | s < F t} := by
  constructor
  · apply le_antisymm
    · apply le_sInf
      intro t ht
      by_cases htt : t < (⊤ : α)
      · exact sInf_le ⟨htt,ht⟩
      · simpa only [eq_top_iff.mpr (le_of_not_gt htt)] using
          (le_top : sInf {t | t < (⊤ : α) ∧ s ≤ F t} ≤ ⊤)
    · exact sInf_le_sInf (fun t ht => ht.2)
  · apply le_antisymm
    · apply le_sInf
      intro t ht
      by_cases htt : t < (⊤ : α)
      · exact sInf_le ⟨htt,ht⟩
      · simpa only [eq_top_iff.mpr (le_of_not_gt htt)] using
          (le_top : sInf {t | t < (⊤ : α) ∧ s < F t} ≤ ⊤)
    · exact sInf_le_sInf (fun t ht => ht.2)

/-- Continuity eliminates both undershoot and overshoot at either inverse.
Only continuity strictly before the terminal point is required. -/
theorem continuous_clock_inverse_levels
    {α β : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β]
    (F : α → β) (hF : Monotone F) (hc : ContinuousOn F (Iio ⊤))
    (hend : F ⊤ = sSup (F '' Iio ⊤))
    (s : β) (hlo : F ⊥ ≤ s) (hs : s < F ⊤) :
    F (sInf {t | s ≤ F t}) = s ∧ F (sInf {t | s < F t}) = s := by
  let a := sInf {t | s ≤ F t}
  let b := sInf {t | s < F t}
  have hab : a ≤ b := sInf_le_sInf (fun t ht => ht.le)
  have ht := generalized_inverse_before_terminal F hend s hs
  have hcross : s ≤ F a := by
    have hne : ({t | s ≤ F t} : Set α).Nonempty := ⟨⊤,hs.le⟩
    have hca : ContinuousAt F a := hc.continuousAt (Iio_mem_nhds ht.1)
    have he := hF.map_csInf_of_continuousAt hca hne (OrderBot.bddBelow _)
    change s ≤ F (sInf {t | s ≤ F t})
    rw [he]
    apply le_sInf
    rintro _ ⟨t,ht,rfl⟩
    exact ht
  have hca : ContinuousOn F (Icc ⊥ a) := hc.mono (fun t ht' => ht'.2.trans_lt ht.1)
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (bot_le : (⊥ : α) ≤ a) hca ⟨hlo,hcross⟩
  have hea : F a = s := le_antisymm
    ((hF (sInf_le (s := {t | s ≤ F t}) he.ge)).trans_eq he) hcross
  have hcb : ContinuousOn F (Icc ⊥ b) := hc.mono (fun t ht' => ht'.2.trans_lt ht.2)
  have heb : F b ≤ s := by
    by_contra hn
    obtain ⟨v,hsv,hvb⟩ := exists_between (lt_of_not_ge hn)
    obtain ⟨r,hr,her⟩ := intermediate_value_Icc (bot_le : (⊥ : α) ≤ b) hcb
      ⟨hlo.trans hsv.le,hvb.le⟩
    have hrb : r < b := lt_of_le_of_ne hr.2 (by
      intro hh
      rw [hh] at her
      exact hvb.ne her.symm)
    have hbr : b ≤ r := sInf_le (s := {t | s < F t}) (by change s < F r; rw [her]; exact hsv)
    exact hrb.not_ge hbr
  exact ⟨hea,le_antisymm heb (hea.symm.trans_le (hF hab))⟩

theorem lower_inverse_endpoint_removal
    {α β : Type*} [CompleteLinearOrder α] [LinearOrder β]
    (F : α → β) (s : β) (hs : s < F ⊤) :
    sSup {t | t < (⊤ : α) ∧ F t < s} = sSup {t | F t < s} ∧
    sSup {t | t < (⊤ : α) ∧ F t ≤ s} = sSup {t | F t ≤ s} := by
  have ht (t : α) (h : F t ≤ s) : t < ⊤ := by
    by_contra hn
    have he : t = ⊤ := eq_top_iff.mpr (le_of_not_gt hn)
    rw [he] at h
    exact hs.not_ge h
  constructor <;> congr 1 <;> ext t
  · exact ⟨fun h => h.2,fun h => ⟨ht t h.le,h⟩⟩
  · exact ⟨fun h => h.2,fun h => ⟨ht t h,h⟩⟩

end Asakura.Chapter7
