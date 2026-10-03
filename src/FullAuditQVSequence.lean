import FullAuditQVConvex
import FullAuditQuadraticBound

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem real_toLp_norm_sqrt {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ = Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have he : ⟪hf.toLp f,hf.toLp f⟫_ℝ = ∫ ω, f ω ^ 2 ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    simp only [hω,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [← he,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

/-- The square-defect processes for the printed dyadic partitions satisfy all
 defining conditions of M2, and have the stated uniform terminal norm bound. -/
theorem qv_partition_witness {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hTop : ∀ t, MemLp (X t) ∞ P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0) (n : ℕ) :
    ContinuousM2Witness P F (fun t ω => X t ω ^ 2-partitionSquares X (qvPartition n) (qvPartitionLength n) t ω) := by
  have h2 (t) : MemLp (X t) 2 P := (hTop t).mono_exponent (by simp)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t
    exact (partition_square_defect_adapted_integrable P F hF X hm h2 _ _ t).1
  · intro t
    exact (partition_defect_memLp_top P X hTop _ _ t).mono_exponent (by simp)
  · exact partition_square_defect_continuous X hc _ _
  · exact partition_square_martingale_written P F hF hle X hm h2 hmart _
      (qv_partition_mono n) (qv_partition_endpoints n).1 _ (qv_partition_endpoints (T := T) n).2
  · filter_upwards [hz] with ω hω
    simp [partition_squares_initial,hω]

/-- A single bounded sequence in the already proved Hilbert space, carrying
 all the coarser-grid inequalities needed by the convex-tail construction. -/
theorem qv_bounded_terminal_sequence {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hTop : ∀ t, MemLp (X t) ∞ P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0) :
    ∃ f : ℕ → continuousM2Terminal P F,
      (∀ n, ‖f n‖ ≤ 2*(eLpNorm (X ⊤) ∞ P).toReal*Real.sqrt (∫ ω, X ⊤ ω^2 ∂P)) ∧
      (∀ n k, n ≤ k → f k ∈ gridConstrainedTerminals P F X (range (qvPartition n))) := by
  let Y := fun n t ω => X t ω^2-partitionSquares X (qvPartition n) (qvPartitionLength n) t ω
  have hY (n) : ContinuousM2Witness P F (Y n) := qv_partition_witness P F hF hle X hm hTop hc hmart hz n
  let f : ℕ → continuousM2Terminal P F := fun n =>
    ⟨((hY n).moment ⊤).toLp (Y n ⊤),Y n,hY n,((hY n).moment ⊤).coeFn_toLp.symm⟩
  refine ⟨f,?_,?_⟩
  · intro n
    change ‖((hY n).moment ⊤).toLp (Y n ⊤)‖ ≤ _
    rw [real_toLp_norm_sqrt]
    exact bounded_partition_square_norm P F hF hle X hm hTop hmart hz _
      (qv_partition_mono n) (qv_partition_endpoints n).1 _ (qv_partition_endpoints (T := T) n).2
  · intro n k hnk
    refine ⟨Y k,hY k,((hY k).moment ⊤).coeFn_toLp.symm,?_⟩
    intro s hs t ht hst
    apply Eventually.of_forall
    intro ω
    simp only [Y,sub_sub_cancel]
    exact qv_partition_increases_on_coarser_grid X hnk hs ht hst ω

end Asakura.FullAudit
