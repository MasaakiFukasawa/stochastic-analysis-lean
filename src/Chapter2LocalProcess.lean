import Chapter2LocalStopping
import Chapter2LocalGluing
import FullAuditBVMartingaleWritten

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)

/-- The chapter's definition of a local martingale on [0,T).
The value of X at T is unused: every localizer is strictly below T.
Null-set changes are handled separately using the chapter's completeness assumption. -/
structure LocalMProcessWitness (X : ClosedTime T → Ω → ℝ) : Prop where
  localizers : ∃ τ : ℕ → Ω → ClosedTime T,
    (∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t}) ∧
    (∀ ω, Monotone (fun n => τ n ω)) ∧
    (∀ n ω, τ n ω < ⊤) ∧
    (∀ ω t, t < ⊤ → ∃ n, t < τ n ω) ∧
    (∀ n, (fun t ω => X (min (τ n ω) t) ω) ∈ boundedMProcess P F)

/-- Every local witness has continuous paths strictly before T. -/
theorem LocalMProcessWitness.path {X : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (ω : Ω) (t : ClosedTime T) (ht : t < ⊤) :
    ContinuousAt (fun s => X s ω) t := by
  obtain ⟨τ, _, _, _, hc, hb⟩ := hX.localizers
  exact glued_path_continuous_below_terminal (fun n => τ n ω) (hc ω)
    (fun n s => X (min (τ n ω) s) ω) (fun n => (hb n).1.path ω)
    (fun s => X s ω) (fun _ _ => rfl) t ht

/-- Adaptedness follows from the actual measurable stopped processes,
using a pointwise eventually constant limit. -/
theorem LocalMProcessWitness.adapted {X : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (t : ClosedTime T) (ht : t < ⊤) :
    Measurable[F t] (X t) := by
  obtain ⟨τ, _, hm, _, hc, hb⟩ := hX.localizers
  apply @glued_value_measurable Ω (F t) (fun n ω => X (min (τ n ω) t) ω)
    (fun n => (hb n).1.adapted t)
  intro ω
  obtain ⟨n, hn⟩ := hc ω t ht
  refine eventually_atTop.2 ⟨n, fun k hk => ?_⟩
  rw [min_eq_right ((le_of_lt hn).trans (hm ω hk))]

/-- A local process whose stopped paths have bounded variation is zero.
This is Proposition A_loc intersect M_loc = {0}, reduced to the already
verified A intersect M2 result, with one common exceptional null set. -/
theorem local_bv_martingale_zero
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t ≤ τ n ω)
    (hM : ∀ n, ContinuousM2Witness P F (fun t ω => X (min (τ n ω) t) ω))
    (hA : ∀ n ω, ∃ B C : ClosedTime T → ℝ, Monotone B ∧ Monotone C ∧
      ∀ t, X (min (τ n ω) t) ω = B t - C t) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = 0 := by
  have hz (n) := A_inter_M2_zero_written P F hF hle _ (hM n).adapted
    (hM n).moment (hM n).path (hA n) (hM n).martingale (hM n).initial
  have hall : ∀ᵐ ω ∂P, ∀ n, ∀ t, X (min (τ n ω) t) ω = 0 :=
    (ae_all_iff).2 hz
  filter_upwards [hall] with ω hω
  intro t ht
  obtain ⟨n, hn⟩ := hcofinal ω t ht
  simpa only [min_eq_right hn] using hω n t

/-- Two increasing localizing sequences have a common increasing localization. -/
theorem common_localizers_cofinal
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (τ σ : ℕ → ι) (hτ : Monotone τ) (hσ : Monotone σ)
    (hcτ : ∀ t : ι, t < ⊤ → ∃ n, t < τ n)
    (hcσ : ∀ t : ι, t < ⊤ → ∃ n, t < σ n) :
    Monotone (fun n => min (τ n) (σ n)) ∧
    ∀ t : ι, t < ⊤ → ∃ n, t < min (τ n) (σ n) := by
  refine ⟨hτ.min hσ, ?_⟩
  intro t ht
  obtain ⟨n, hn⟩ := hcτ t ht
  obtain ⟨k, hk⟩ := hcσ t ht
  refine ⟨max n k, lt_min ?_ ?_⟩
  · exact hn.trans_le (hτ (le_max_left _ _))
  · exact hk.trans_le (hσ (le_max_right _ _))

/-- Further stopping a bounded stopped process yields a bounded process
at the minimum of the two stopping times. -/
theorem bounded_at_minimum
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (τ σ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hX : (fun t ω => X (min (τ ω) t) ω) ∈ boundedMProcess P F) :
    (fun t ω => X (min (min (τ ω) (σ ω)) t) ω) ∈ boundedMProcess P F := by
  have h := bounded_martingale_stopped P F hF hle ⟨_, hX⟩ σ hσ
  simpa only [min_assoc] using h

/-- Closure of the actual local-martingale definition under addition. -/
theorem LocalMProcessWitness.add
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X Y : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y) :
    LocalMProcessWitness P F (fun t ω => X t ω + Y t ω) := by
  obtain ⟨τ, ht, htm, htt, htc, hx⟩ := hX.localizers
  obtain ⟨σ, hs, hsm, hst, hsc, hy⟩ := hY.localizers
  refine ⟨fun n ω => min (τ n ω) (σ n ω), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (written_stopping_min_max F (τ n) (σ n) (ht n) (hs n)).1
  · intro ω
    exact (htm ω).min (hsm ω)
  · intro n ω
    exact (min_le_left _ _).trans_lt (htt n ω)
  · intro ω
    exact (common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
      (htm ω) (hsm ω) (htc ω) (hsc ω)).2
  · intro n
    have ha := bounded_at_minimum P F hF hle X (τ n) (σ n) (hs n) (hx n)
    have hb := bounded_at_minimum P F hF hle Y (σ n) (τ n) (ht n) (hy n)
    have hb' : (fun t ω => Y (min (min (τ n ω) (σ n ω)) t) ω) ∈ boundedMProcess P F := by
      simpa only [min_comm (σ n _) (τ n _)] using hb
    exact (boundedMProcess P F).add_mem ha hb'

/-- The full local finite-variation intersection argument, allowing distinct
localizers for the martingale and finite-variation assumptions. -/
theorem local_finite_variation_intersection_zero
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ : ℕ → Ω → ClosedTime T)
    (hσ : ∀ n t, MeasurableSet[F t] {ω | σ n ω ≤ t})
    (hσmono : ∀ ω, Monotone (fun n => σ n ω))
    (hσcofinal : ∀ ω t, t < ⊤ → ∃ n, t < σ n ω)
    (hBV : ∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, X (min (σ n ω) t) ω = U t - V t) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = 0 := by
  obtain ⟨τ, ht, htm, htt, htc, hx⟩ := hX.localizers
  apply local_bv_martingale_zero P F hF hle X (fun n ω => min (τ n ω) (σ n ω))
  · intro ω t ht'
    exact ((common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
      (htm ω) (hσmono ω) (htc ω) (hσcofinal ω)).2 t ht').imp fun n hn => hn.le
  · intro n
    exact (bounded_at_minimum P F hF hle X (τ n) (σ n) (hσ n) (hx n)).1
  · intro n ω
    obtain ⟨U,V,hU,hV,he⟩ := hBV n ω
    refine ⟨fun t => U (min (τ n ω) t), fun t => V (min (τ n ω) t),
      hU.comp (monotone_const.min monotone_id), hV.comp (monotone_const.min monotone_id), ?_⟩
    intro t
    simpa only [← min_assoc, min_comm (σ n ω) (τ n ω)] using he (min (τ n ω) t)

/-- Scalar multiplication preserves the same localizing sequence. -/
theorem LocalMProcessWitness.smul {X : ClosedTime T → Ω → ℝ}
    (hX : LocalMProcessWitness P F X) (c : ℝ) :
    LocalMProcessWitness P F (fun t ω => c * X t ω) := by
  obtain ⟨τ,ht,hm,hb,hc,hXτ⟩ := hX.localizers
  refine ⟨τ,ht,hm,hb,hc,?_⟩
  intro n
  exact (boundedMProcess P F).smul_mem c (hXτ n)

/-- Stopping a local martingale preserves its original cofinal localizers.
The argument uses commutation of the two stopping operations. -/
theorem LocalMProcessWitness.stopped
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) :
    LocalMProcessWitness P F (fun t ω => X (min (σ ω) t) ω) := by
  obtain ⟨τ,ht,hm,hb,hc,hXτ⟩ := hX.localizers
  refine ⟨τ,ht,hm,hb,hc,?_⟩
  intro n
  have h := bounded_martingale_stopped P F hF hle ⟨_,hXτ n⟩ σ hσ
  convert h using 1
  funext t ω
  change X (min (σ ω) (min (τ n ω) t)) ω = X (min (τ n ω) (min (σ ω) t)) ω
  rw [min_left_comm]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.path
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.adapted
#print axioms Asakura.Chapter2Complete.local_bv_martingale_zero

#print axioms Asakura.Chapter2Complete.common_localizers_cofinal
#print axioms Asakura.Chapter2Complete.bounded_at_minimum
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.add

#print axioms Asakura.Chapter2Complete.local_finite_variation_intersection_zero

#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.smul
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.stopped
