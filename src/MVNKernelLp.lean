import MVNIncrementVariance
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set
namespace Asakura

noncomputable def mvnFutureFunction (H t : ℝ) : ℝ → ℝ :=
  (Ioc 0 t).indicator (fun r => (t-r)^(H-1/2))
noncomputable def mvnPastFunction (H t : ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (mvnPastKernel (H-1/2) t)

lemma mvn_future_function_memLp (H t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    MemLp (mvnFutureFunction H t) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioc).mpr (mvn_future_memLp H t hH ht)

lemma mvn_past_function_memLp (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (ht : 0 ≤ t) :
    MemLp (mvnPastFunction H t) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioi).mpr (mvn_past_memLp H t hH0 hH1 ht)

lemma mvn_future_difference_integral (H s t : ℝ) (hH : 0 < H) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r, (mvnFutureFunction H t r-mvnFutureFunction H s r)^2) =
      (∫ r in Ioc 0 s, ((t-r)^(H-1/2)-(s-r)^(H-1/2))^2) +
      (∫ r in Ioc s t, ((t-r)^(H-1/2))^2) := by
  let f : ℝ → ℝ := fun r => (mvnFutureFunction H t r-mvnFutureFunction H s r)^2
  have hf : Integrable f := (memLp_two_iff_integrable_sq
    ((mvn_future_function_memLp H t hH (hs.trans hst)).sub
      (mvn_future_function_memLp H s hH hs)).aestronglyMeasurable).mp
      ((mvn_future_function_memLp H t hH (hs.trans hst)).sub
        (mvn_future_function_memLp H s hH hs))
  have he : (∫ r, f r) = ∫ r in Ioc 0 t, f r := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hrs : r ∉ Ioc 0 s := fun h => hr ⟨h.1,h.2.trans hst⟩
    simp [f,mvnFutureFunction,hr,hrs]
  have hd : Disjoint (Ioc 0 s) (Ioc s t) := disjoint_left.mpr
    (fun r hr hr' => (not_lt_of_ge hr.2) hr'.1)
  change (∫ r, f r) = _
  rw [he,← Ioc_union_Ioc_eq_Ioc hs hst,
    setIntegral_union hd measurableSet_Ioc hf.integrableOn hf.integrableOn]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have hrt : r ∈ Ioc 0 t := ⟨hr.1,hr.2.trans hst⟩
    simp [f,mvnFutureFunction,hr,hrt]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have hrt : r ∈ Ioc 0 t := ⟨hs.trans_lt hr.1,hr.2⟩
    have hrs : r ∉ Ioc 0 s := fun h => (not_lt_of_ge h.2) hr.1
    simp [f,mvnFutureFunction,hrt,hrs]

lemma mvn_past_difference_integral (H s t : ℝ) :
    (∫ r, (mvnPastFunction H t r-mvnPastFunction H s r)^2) =
      ∫ r in Ioi 0, ((t+r)^(H-1/2)-(s+r)^(H-1/2))^2 := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · simp only [mvnPastFunction,indicator_of_mem hr,mvnPastKernel]
    congr 1
    ring
  · simp [mvnPastFunction,hr]

lemma mvn_kernel_increment_variance (H s t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    mvnNormalization H ^ 2 *
      ((∫ r, (mvnFutureFunction H t r-mvnFutureFunction H s r)^2)+
       (∫ r, (mvnPastFunction H t r-mvnPastFunction H s r)^2)) = (t-s)^(2*H) := by
  rw [mvn_future_difference_integral H s t hH0 hs hst,mvn_past_difference_integral]
  exact mvn_normalized_increment_variance H s t hH0 hH1 hs hst
end Asakura
