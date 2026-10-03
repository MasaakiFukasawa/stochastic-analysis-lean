import Chapter6BorelProgressive

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter6

lemma nonnegative_borel_coefficient_extension {d : ℕ}
    (μ : (Fin d → ℝ) × ℝ≥0 → Fin d → ℝ) (hm : Measurable μ)
    (K : ℝ) (hk : ∀ z i,|μ z i| ≤ K)
    (R : ℝ) (hR : 0 ≤ R) (hs : ∀ x (t : ℝ≥0),R < t → μ (x,t) = 0) :
    let b := fun z : (Fin d → ℝ) × ℝ => μ (z.1,Real.toNNReal z.2)
    Measurable b ∧ (∀ z i,|b z i| ≤ K) ∧
      (∀ x t,R < t → b (x,t) = 0) ∧
      (∀ x (t : ℝ≥0),b (x,t) = μ (x,t)) := by
  refine ⟨hm.comp (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd)),
    fun z i => hk _ i,?_,?_⟩
  · intro x t ht
    apply hs
    simpa only [Real.coe_toNNReal _ (hR.trans ht.le)] using ht
  · intro x t
    simp

end Asakura.Chapter6
