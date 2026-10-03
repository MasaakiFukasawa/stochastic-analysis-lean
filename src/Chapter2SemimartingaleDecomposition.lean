import Chapter2AdaptedVariationAlgebra
import Chapter2LocalPathEncoding
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- A decomposition in the actual manuscript spaces, with continuity of X
and unused values at the open terminal time. -/
structure SemimartingaleDecomposition {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (X A M : ClosedTime T → Ω → ℝ) : Prop where
  variation : AdaptedLocalVariationWitness F A
  martingale : LocalMProcessWitness P F M
  continuous : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t
  decomposition : ∀ t, t < ⊤ → ∀ ω, X t ω = A t ω + M t ω

theorem SemimartingaleDecomposition.variation_continuous
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X A M : ClosedTime T → Ω → ℝ} (h : SemimartingaleDecomposition P F X A M) :
    ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t := by
  intro ω t ht
  apply ((h.continuous ω t ht).sub (h.martingale.path P F ω t ht)).congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds ht] with s hs
  have he := h.decomposition s hs ω
  change A s ω = X s ω-M s ω
  linarith

theorem SemimartingaleDecomposition.unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X A M B N : ClosedTime T → Ω → ℝ}
    (h : SemimartingaleDecomposition P F X A M)
    (k : SemimartingaleDecomposition P F X B N) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → A t ω = B t ω ∧ M t ω = N t ω := by
  have hd := (h.martingale.smul P F (-1)).add P F hF hle k.martingale
  have heq : ∀ t, t < ⊤ → (fun ω => -1*M t ω+N t ω) = (fun ω => A t ω-B t ω) := by
    intro t ht; funext ω
    have he := h.decomposition t ht ω
    have ke := k.decomposition t ht ω
    linarith
  have hm := hd.congr_before_terminal P F heq
  have hv := (h.variation.add (k.variation.smul (-1)) hF).toPathwise
  obtain ⟨τ,hs,hmono,_,hc,hv⟩ := hv.localizers
  have hparts n ω : ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A (min (τ n ω) t) ω-B (min (τ n ω) t) ω = U t-V t := by
    simpa only [neg_one_mul,← sub_eq_add_neg] using hv n ω
  have hz := local_finite_variation_intersection_zero P F hF hle _ hm τ hs hmono hc hparts
  filter_upwards [hz] with ω hω
  intro t ht
  have he := h.decomposition t ht ω
  have ke := k.decomposition t ht ω
  have hzero := hω t ht
  exact ⟨by linarith,by linarith⟩

theorem SemimartingaleDecomposition.stopped
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X A M : ClosedTime T → Ω → ℝ} (h : SemimartingaleDecomposition P F X A M)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) :
    SemimartingaleDecomposition P F (fun t ω => X (min (σ ω) t) ω)
      (fun t ω => A (min (σ ω) t) ω) (fun t ω => M (min (σ ω) t) ω) := by
  refine ⟨h.variation.stopped hF σ hσ,h.martingale.stopped P F hF hle σ hσ,?_,?_⟩
  · intro ω t ht
    exact (h.continuous ω _ ((min_le_right _ _).trans_lt ht)).comp
      (continuous_const.min continuous_id).continuousAt
  · intro t ht ω
    exact h.decomposition _ ((min_le_right _ _).trans_lt ht) ω

/-- Defining covariation through the martingale parts is independent of
the semimartingale decompositions, by the proved uniqueness theorem. -/
theorem semimartingale_covariance_independent
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    {X Y A M B N A' M' B' N' C : ClosedTime T → Ω → ℝ}
    (hX : SemimartingaleDecomposition P F X A M)
    (hX' : SemimartingaleDecomposition P F X A' M')
    (hY : SemimartingaleDecomposition P F Y B N)
    (hY' : SemimartingaleDecomposition P F Y B' N')
    (hC : LocalCovarianceWitness P F M N C) : LocalCovarianceWitness P F M' N' C := by
  exact hC.congr_ae_processes P F hF hle hX.martingale hY.martingale hX'.martingale hY'.martingale
    ((hX.unique P F hF hle hX').mono (fun ω hω t ht => (hω t ht).2))
    ((hY.unique P F hF hle hY').mono (fun ω hω t ht => (hω t ht).2))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.SemimartingaleDecomposition.unique
#print axioms Asakura.Chapter2Complete.semimartingale_covariance_independent
