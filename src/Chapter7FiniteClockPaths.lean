import Chapter7FiniteClock

open Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 1200000

/-- Flat portions of the clock do not introduce jumps into the changed path.
This proves the path assertion also for finite clock lifetime F_*. -/
theorem finite_clock_path_continuity
    {α β E : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β] [TopologicalSpace E]
    (F : α → β) (hF : Monotone F) (hc : ContinuousOn F (Iio ⊤))
    (hend : F ⊤ = sSup (F '' Iio ⊤))
    (φ : α → E) (hφ : ContinuousOn φ (Iio ⊤))
    (hflat : ∀ a b,a < ⊤ → b < ⊤ → F a = F b → φ a = φ b)
    (s : β) (hlo : F ⊥ ≤ s) (hs : s < F ⊤) :
    ContinuousAt (fun r => φ (sInf {t | r ≤ F t})) s := by
  have ht := generalized_inverse_before_terminal F hend s hs
  have he := continuous_clock_inverse_levels F hF hc hend s hlo hs
  have hpa : ContinuousAt φ (sInf {t | s ≤ F t}) := hφ.continuousAt (Iio_mem_nhds ht.1)
  have hpb : ContinuousAt φ (sInf {t | s < F t}) := hφ.continuousAt (Iio_mem_nhds ht.2)
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · exact hpa.comp_continuousWithinAt (f := fun r : β => sInf {t | r ≤ F t})
      ((weak_inverse_left_order_continuous F hF).continuousWithinAt_Iic.mono Iio_subset_Iic_self)
  · have hh := hpb.tendsto.comp (weak_inverse_right_limit F s)
    have hval := hflat _ _ ht.2 ht.1 (he.2.trans he.1.symm)
    rw [hval] at hh
    exact hh

/-- The recovery identity is asserted precisely at t for which F(t)<F_*;
it need not evaluate an inverse at the excluded terminal clock value. -/
theorem finite_clock_path_recovery
    {α β E : Type*} [CompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β]
    (F : α → β) (hF : Monotone F) (hc : ContinuousOn F (Iio ⊤))
    (hend : F ⊤ = sSup (F '' Iio ⊤))
    (φ : α → E)
    (hflat : ∀ a b,a < ⊤ → b < ⊤ → F a = F b → φ a = φ b)
    (t : α) (ht : t < ⊤) (hft : F t < F ⊤) :
    φ (sInf {u | F t ≤ F u}) = φ t := by
  exact hflat _ t (generalized_inverse_before_terminal F hend (F t) hft).1 ht
    (continuous_clock_inverse_levels F hF hc hend (F t) (hF bot_le) hft).1

end Asakura.Chapter7
