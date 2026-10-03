import FullAuditFiniteBrownianHitting

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The exercise's uncapped infimum is taken in extended real time, not
inside [0,T], so the empty hitting set has value infinity rather than T. -/
noncomputable def uncappedFiniteHit {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ) (c : ℝ) (ω : Ω) : EReal :=
  sInf (Subtype.val '' {s : ClosedTime T | X s ω = c})

theorem uncapped_finite_hit_event {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : T < ⊤)
    (X : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun s => X s ω))
    (c : ℝ) (ω : Ω) (t : ClosedTime T) :
    uncappedFiniteHit X c ω ≤ t.val ↔ ∃ s ≤ t, X s ω = c := by
  let B := Subtype.val '' {s : ClosedTime T | X s ω = c}
  have hclosed : IsClosed B :=
    ((isClosed_eq (hc ω) continuous_const).isCompact.image continuous_subtype_val).isClosed
  constructor
  · intro ht
    have hne : B.Nonempty := by
      by_contra hn
      have he : B = ∅ := not_nonempty_iff_eq_empty.mp hn
      change sInf B ≤ t.val at ht
      rw [he,sInf_empty] at ht
      exact (not_le_of_gt (t.property.2.trans_lt hT)) ht
    obtain ⟨s,hs,hsv⟩ := hclosed.sInf_mem hne
    refine ⟨s,?_,hs⟩
    change s.val ≤ t.val
    rw [hsv]
    exact ht
  · rintro ⟨s,hst,hs⟩
    exact (sInf_le (show s.val ∈ B from ⟨s,hs,rfl⟩)).trans hst

theorem uncapped_finite_hit_measurable {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : T < ⊤)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun s => X s ω)) (c : ℝ) (t : ClosedTime T) :
    MeasurableSet[F t] {ω | uncappedFiniteHit X c ω ≤ t.val} := by
  letI : MeasurableSpace Ω := F t
  letI : Nonempty (Iic t) := ⟨⟨t,by change t ≤ t; exact le_rfl⟩⟩
  letI : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (isClosed_Iic : IsClosed (Iic t)).isCompact
  let q := TopologicalSpace.denseSeq (Iic t)
  let d := fun ω => ⨅ n, Metric.infDist (X (q n).val ω) ({c}:Set ℝ)
  have hd : Measurable d := Measurable.iInf fun n =>
    (Metric.continuous_infDist_pt {c}).measurable.comp ((hm _).mono (hF (q n).property) le_rfl)
  have he : {ω | uncappedFiniteHit X c ω ≤ t.val} = d ⁻¹' {0} := by
    ext ω
    rw [mem_setOf_eq,uncapped_finite_hit_event hT X hc c ω t]
    change (∃ s ≤ t, X s ω = c) ↔ (⨅ n, Metric.infDist (X (q n).val ω) ({c}:Set ℝ)) = 0
    rw [compact_dense_distance_zero q (TopologicalSpace.denseRange_denseSeq _)
      (fun s : Iic t => X s.val ω) ((hc ω).comp continuous_subtype_val)
      {c} isClosed_singleton (singleton_nonempty c)]
    constructor
    · rintro ⟨s,hs,he⟩; exact ⟨⟨s,hs⟩,he⟩
    · rintro ⟨s,he⟩; exact ⟨s.val,s.property,he⟩
  rw [he]
  exact hd (measurableSet_singleton 0)

/-- Both assertions of the uncapped hitting exercise follow for every
continuous zero-initial martingale and nonzero level, hence for Brownian motion.
Optional sampling, not a distributional hitting-time formula, proves failure
to take values in the finite interval. -/
theorem uncapped_hitting_exercise {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)] (hT : T < ⊤)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, Integrable (X t) P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0)
    (c : ℝ) (hc0 : c ≠ 0) :
    (∀ t, MeasurableSet[F t] {ω | uncappedFiniteHit X c ω ≤ t.val}) ∧
    0 < P {ω | T < uncappedFiniteHit X c ω} := by
  refine ⟨uncapped_finite_hit_measurable hT F hF X hm hc c,?_⟩
  have hn := nonzero_level_not_hit_by_terminal P F hF hle X hm hi hc hM hz c hc0
  have he : {ω | T < uncappedFiniteHit X c ω} = {ω | ∀ t, X t ω ≠ c} := by
    ext ω
    change T < uncappedFiniteHit X c ω ↔ ∀ t, X t ω ≠ c
    rw [← not_le]
    change (¬uncappedFiniteHit X c ω ≤ (⊤ : ClosedTime T).val) ↔ _
    rw [uncapped_finite_hit_event hT X hc c ω ⊤]
    simp
  rw [he]
  exact hn


/-- Instantiation with the actual Brownian motion of the preceding exercise. -/
theorem brownian_uncapped_hitting_exercise {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (T : ℝ≥0)
    [Fact (0 ≤ ((T:ℝ):EReal))] :
    let X := fun t : ClosedTime (T:ℝ) => B (finiteTimeToNNReal T t)
    let F := fun t : ClosedTime (T:ℝ) => pastSigma B (finiteTimeToNNReal T t)
    (∀ t, MeasurableSet[F t] {ω | uncappedFiniteHit X 1 ω ≤ t.val}) ∧
      0 < P {ω | ((T:ℝ):EReal) < uncappedFiniteHit X 1 ω} := by
  intro X F
  let ρ := finiteTimeToNNReal T
  have hzρ : ρ ⊥ = 0 := by
    apply Subtype.ext
    change (0:EReal).toReal = (0:ℝ)
    rfl
  have hz : X ⊥ =ᵐ[P] 0 := by
    change (fun ω => B (ρ ⊥) ω) =ᵐ[P] (fun _ => 0)
    rw [hzρ]
    exact hB.eval_zero_ae_eq_zero
  exact uncapped_hitting_exercise P (EReal.coe_lt_top _) F
    ((past_sigma_mono B).comp (finite_time_to_nnreal_mono T))
    (fun t => past_sigma_le B hm (ρ t)) X
    (fun t => natural_process_adapted B (ρ t)) (fun t => hB.integrable_eval (ρ t))
    (fun ω => (hc ω).comp (finite_time_to_nnreal_continuous T))
    (fun s t hst => brownian_natural_martingale_written P B hB hm _ _
      (finite_time_to_nnreal_mono T hst)) hz 1 (by norm_num)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.uncapped_hitting_exercise

#print axioms Asakura.Chapter2Complete.brownian_uncapped_hitting_exercise
