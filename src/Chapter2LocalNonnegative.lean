import Chapter2LocalProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- A nonnegative local martingale starting at zero is zero. This uses
bounded localization, the actual mean identity, and a common null set for
all times; no supermartingale convergence theorem is assumed. -/
theorem nonnegative_local_martingale_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hpos : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → 0 ≤ X t ω) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = 0 := by
  obtain ⟨τ,ht,hm,htt,hc,hXτ⟩ := hX.localizers
  have hzero (n) : ∀ᵐ ω ∂P, ∀ t, X (min (τ n ω) t) ω = 0 := by
    apply continuous_zero_marginals_doob P _
      (fun t => ((hXτ n).1.adapted t).mono (hle t) le_rfl) (hXτ n).1.path
    intro t
    have hi := ((hXτ n).1.moment t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
    have hmean := integral_congr_ae (((hXτ n).1.martingale ⊥ t bot_le).trans (hXτ n).1.initial)
    rw [integral_condExp (hle ⊥)] at hmean
    simp only [Pi.zero_apply,integral_zero] at hmean
    apply (integral_eq_zero_iff_of_nonneg_ae _ hi).mp hmean
    exact hpos.mono fun ω hω => hω _ ((min_le_left _ _).trans_lt (htt n ω))
  filter_upwards [ae_all_iff.2 hzero] with ω hω
  intro t ht'
  obtain ⟨n,hn⟩ := hc ω t ht'
  simpa only [min_eq_right hn.le] using hω n t

/-- The zero quadratic-variation argument, expressed through its defining
square-martingale property. -/
theorem local_square_martingale_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (hX2 : LocalMProcessWitness P F (fun t ω => X t ω ^ 2)) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = 0 := by
  have h := nonnegative_local_martingale_zero P F hF hle _ hX2
    (Filter.Eventually.of_forall fun ω t _ => sq_nonneg (X t ω))
  exact h.mono fun ω hω t ht => sq_eq_zero_iff.mp (hω t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.nonnegative_local_martingale_zero
#print axioms Asakura.Chapter2Complete.local_square_martingale_zero
