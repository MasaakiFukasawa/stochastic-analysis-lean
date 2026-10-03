import Chapter7FiniteClockPaths

open Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 1300000

/-- Stopping the original path and stopping the changed path agree, even
when the clock has flat pieces and its inverse jumps. -/
theorem finite_clock_stopping_identity
    {α β E : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β]
    (F : α → β) (hF : Monotone F) (hc : ContinuousOn F (Iio ⊤))
    (hend : F ⊤ = sSup (F '' Iio ⊤))
    (X : α → E)
    (hflat : ∀ a b,a < ⊤ → b < ⊤ → F a = F b → X a = X b)
    (a : α) (ha : a < ⊤) (s : β) (hs0 : F ⊥ ≤ s) (hs : s < F ⊤) :
    X (min a (sInf {t | s ≤ F t})) = X (sInf {t | min (F a) s ≤ F t}) := by
  have hmin : min (F a) s < F ⊤ := (min_le_right _ _).trans_lt hs
  have hmin0 : F ⊥ ≤ min (F a) s := le_min (hF bot_le) hs0
  have hl := continuous_clock_inverse_levels F hF hc hend s hs0 hs
  have hr := continuous_clock_inverse_levels F hF hc hend (min (F a) s) hmin0 hmin
  apply hflat _ _ ((min_le_left _ _).trans_lt ha)
    (generalized_inverse_before_terminal F hend _ hmin).1
  rw [hF.map_min,hl.1,hr.1]

/-- Cofinality of the original localizers is preserved by an unbounded
clock. This constructs cofinal changed localizers without an extra limit
assumption about their clock values. -/
theorem clock_localizers_cofinal
    {α β : Type*} [CompleteLinearOrder α] [CompleteLinearOrder β]
    (F : α → β) (hF : Monotone F)
    (hend : F ⊤ = sSup (F '' Iio ⊤))
    (τ : ℕ → α) (hco : ∀ t,t < ⊤ → ∃ n,t < τ n) :
    ∀ s,s < F ⊤ → ∃ n,s < F (τ n) := by
  intro s hs
  have hex : ∃ t,t < (⊤ : α) ∧ s < F t := by
    by_contra hn
    have hh : F ⊤ ≤ s := by
      rw [hend]
      apply sSup_le
      rintro _ ⟨t,ht,rfl⟩
      exact le_of_not_gt (fun h => hn ⟨t,ht,h⟩)
    exact hs.not_ge hh
  obtain ⟨t,ht,hst⟩ := hex
  obtain ⟨n,hn⟩ := hco t ht
  exact ⟨n,hst.trans_le (hF hn.le)⟩

end Asakura.Chapter7
