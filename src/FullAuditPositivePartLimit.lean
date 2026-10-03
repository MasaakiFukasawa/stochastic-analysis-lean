import FullAuditConditionalLimit

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 400000

/-- The manuscript's positive-part argument passes an eventual inequality
 through two L2 limits directly, without selecting an a.e. subsequence. -/
theorem ae_order_of_l2_limits {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (U V : ℕ → Ω → ℝ) (u v : Ω → ℝ)
    (hU : ∀ n, AEStronglyMeasurable (U n) P) (hV : ∀ n, AEStronglyMeasurable (V n) P)
    (hu : AEStronglyMeasurable u P) (hv : AEStronglyMeasurable v P)
    (hUV : ∀ᶠ n in atTop, U n ≤ᵐ[P] V n)
    (htu : Tendsto (fun n => eLpNorm (U n-u) 2 P) atTop (𝓝 0))
    (htv : Tendsto (fun n => eLpNorm (V n-v) 2 P) atTop (𝓝 0)) : u ≤ᵐ[P] v := by
  let q := fun ω => max (u ω-v ω) 0
  have hqm : AEStronglyMeasurable q P := ((hu.aemeasurable.sub hv.aemeasurable).max aemeasurable_const).aestronglyMeasurable
  have hbound : ∀ᶠ n in atTop, eLpNorm q 2 P ≤
      eLpNorm (U n-u) 2 P + eLpNorm (V n-v) 2 P := by
    filter_upwards [hUV] with n hn
    calc
      _ ≤ eLpNorm (fun ω => |U n ω-u ω|+|V n ω-v ω|) 2 P := by
        apply eLpNorm_mono_ae hqm
        filter_upwards [hn] with ω hω
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (le_max_right _ _),abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
        apply max_le _ (add_nonneg (abs_nonneg _) (abs_nonneg _))
        have h₁ := neg_abs_le (U n ω-u ω)
        have h₂ := le_abs_self (V n ω-v ω)
        linarith
      _ ≤ _ := by
        have h := Asakura.manuscript_minkowski P (fun ω => |U n ω-u ω|) (fun ω => |V n ω-v ω|) 2 (by norm_num)
        have hU : eLpNorm (fun ω => |U n ω-u ω|) 2 P = eLpNorm (U n-u) 2 P := by
          exact eLpNorm_norm (f := U n-u) ((hU n).sub hu)
        have hV : eLpNorm (fun ω => |V n ω-v ω|) 2 P = eLpNorm (V n-v) 2 P := by
          exact eLpNorm_norm (f := V n-v) ((hV n).sub hv)
        rw [hU,hV] at h
        exact h
  have hlim : Tendsto (fun n => eLpNorm (U n-u) 2 P + eLpNorm (V n-v) 2 P) atTop (𝓝 0) := by
    simpa only [add_zero] using htu.add htv
  have hz : eLpNorm q 2 P = 0 := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound) zero_le
  have hae := (eLpNorm_eq_zero_iff (f := q) (μ := P) (p := 2) (by norm_num)).mp hz
  filter_upwards [hae] with ω hω
  change max (u ω-v ω) 0 = 0 at hω
  have h := le_max_left (u ω-v ω) 0
  rw [hω] at h
  linarith

end Asakura.FullAudit
