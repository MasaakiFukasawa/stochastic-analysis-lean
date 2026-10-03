import Chapter3StoppedPartitionCoordinates

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Cutting the left coefficient at the horizon leaves the weighted
increment unchanged: when the left endpoint is later, the increment is zero. -/
theorem cut_weighted_increment
    {ι : Type*} [LinearOrder ι] (H Q : ι → ℝ)
    (a c b t : ι) (hac : a ≤ c) :
    H (min b a)*(Q (min (min b c) (min b t))-Q (min (min b a) (min b t))) =
      H a*(Q (min c (min b t))-Q (min a (min b t))) := by
  have ha : min (min b a) (min b t) = min a (min b t) := by
    apply le_antisymm
    · exact le_min ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)
    · exact le_min (le_min ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)) (min_le_right _ _)
  have hc : min (min b c) (min b t) = min c (min b t) := by
    apply le_antisymm
    · exact le_min ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)
    · exact le_min (le_min ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)) (min_le_right _ _)
  rw [ha,hc]
  by_cases hab : a ≤ b
  · rw [min_eq_right hab]
  · have hba := (le_of_not_ge hab)
    have hta : min b t ≤ a := (min_le_left _ _).trans hba
    rw [min_eq_right hta,min_eq_right (hta.trans hac),sub_self,mul_zero,mul_zero]

/-- Pathwise Stieltjes approximation on the original stopping partition,
with the measure built from Q. The real coordinate change and the
truncation of coefficients are established in the proof. -/
theorem stopped_stieltjes_uniform_approximation
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (Q H : ClosedTime T → ℝ)
    (hQ : MonotoneOn (fun r => Q (realTimeClamp r)) (Icc 0 d))
    (hr : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r)) (Icc 0 d ∩ Ici x) x)
    (hH : Measurable (fun r => H (realTimeClamp r)))
    (τ : ℕ → ℕ → ClosedTime T)
    (hτ : ∀ n, Monotone (τ n)) (h0 : ∀ n, τ n 0 = ⊥)
    (hcofinal : ∀ n b, b < ⊤ → ∃ N, b < τ n N)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hosc : ∀ n j t, τ n j ≤ t → t ≤ τ n (j+1) → |H (τ n j)-H t| ≤ δ n) :
    let μ := (intervalStieltjes 0 d hd (fun r => Q (realTimeClamp r)) hQ hr).measure
    TendstoUniformly
      (fun n t => ∑' j, H (τ n j)*(Q (min (τ n (j+1)) (min (realTimeClamp d) t))-
        Q (min (τ n j) (min (realTimeClamp d) t))))
      (fun t => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ∂μ) atTop := by
  intro μ
  let u := fun n j => (finitePrefixTime d hd (τ n j)).val
  have hp n := stopped_partition_real_coordinates d hd hdT (τ n) (hτ n) (h0 n) (hcofinal n)
  have he := constructed_stieltjes_uniform_approximation d hd
    (fun r => Q (realTimeClamp r)) (fun r => H (realTimeClamp r)) hQ hr hH
    u (fun n => (hp n).1) (fun n => (hp n).2.1) (fun n => (hp n).2.2)
    δ hδ hlim (fun n => stopped_partition_oscillation_coordinates d hd hdT.le (τ n) H (δ n) (hosc n))
  have hc := he.comp (fun t : ClosedTime T => (finitePrefixTime d hd t).val)
  have hterm (n j : ℕ) (t : ClosedTime T) :
      H (realTimeClamp (u n j)) *
        (Q (realTimeClamp (intervalClamp 0 d hd (min (u n (j+1)) (finitePrefixTime d hd t).val)))-
         Q (realTimeClamp (intervalClamp 0 d hd (min (u n j) (finitePrefixTime d hd t).val)))) =
      H (τ n j)*(Q (min (τ n (j+1)) (min (realTimeClamp d) t))-
        Q (min (τ n j) (min (realTimeClamp d) t))) := by
    have hm (k : ℕ) : min (u n k) (finitePrefixTime d hd t).val ∈ Icc (0:ℝ) d :=
      ⟨le_min (finitePrefixTime d hd (τ n k)).property.1 (finitePrefixTime d hd t).property.1,
        (min_le_left _ _).trans (finitePrefixTime d hd (τ n k)).property.2⟩
    rw [intervalClamp_eq 0 d hd (hm (j+1)),intervalClamp_eq 0 d hd (hm j)]
    rw [real_time_clamp_mono.map_min,real_time_clamp_mono.map_min]
    change H (realTimeClamp (finitePrefixTime d hd (τ n j)).val)*
      (Q (min (realTimeClamp (finitePrefixTime d hd (τ n (j+1))).val) (realTimeClamp (finitePrefixTime d hd t).val))-
       Q (min (realTimeClamp (finitePrefixTime d hd (τ n j)).val) (realTimeClamp (finitePrefixTime d hd t).val))) = _
    simp only [finite_prefix_time_clamp d hd hdT.le]
    exact cut_weighted_increment H Q (τ n j) (τ n (j+1)) (realTimeClamp d) t (hτ n (Nat.le_succ j))
  have heq : (fun n t => ∑' j, H (τ n j)*(Q (min (τ n (j+1)) (min (realTimeClamp d) t))-
        Q (min (τ n j) (min (realTimeClamp d) t)))) =
      (fun n t => ∑' j, H (realTimeClamp (u n j)) *
        (Q (realTimeClamp (intervalClamp 0 d hd (min (u n (j+1)) (finitePrefixTime d hd t).val)))-
         Q (realTimeClamp (intervalClamp 0 d hd (min (u n j) (finitePrefixTime d hd t).val))))) := by
    funext n t
    exact tsum_congr (fun j => (hterm n j t).symm)
  rw [heq]
  exact hc

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.cut_weighted_increment
#print axioms Asakura.Chapter3Complete.stopped_stieltjes_uniform_approximation
