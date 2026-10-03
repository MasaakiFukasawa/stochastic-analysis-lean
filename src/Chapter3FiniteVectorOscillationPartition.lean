import Chapter3VectorOscillationCofinality

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Recursive oscillation partition. The auxiliary deterministic stop c n
makes all functions used to define the hit continuous at the terminal
point; it does not change the first hit before c n. -/
noncomputable def vectorOscillationPartition
    {J : Type*} [Fintype J]
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → (J → ℝ)) (c : ℕ → ClosedTime T) (δ : ℝ) :
    ℕ → Ω → ClosedTime T
  | 0, _ => ⊥
  | n+1, ω => min (sInf {s | δ ≤ ‖X (min (c n) s) ω-
      X (min (c n) (min (vectorOscillationPartition X c δ n ω) s)) ω‖}) (c n)

/-- Construct the partition, with its stopping-time property, local finite
endpoints, cofinality and the original all-time increment bound. -/
theorem constructed_finite_vector_oscillation_partition
    {J : Type*} [Fintype J]
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → (J → ℝ))
    (hm : ∀ i t, t < ⊤ → Measurable[F t] (fun ω => X t ω i))
    (hX : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (c : ℕ → ClosedTime T) (hc : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (δ : ℝ) (hδ : 0 < δ) :
    let τ := vectorOscillationPartition X c δ
    (∀ ω, τ 0 ω = ⊥) ∧
    (∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t}) ∧
    (∀ ω, Monotone (fun n => τ n ω)) ∧
    (∀ n ω, τ n ω < ⊤) ∧
    (∀ ω t, t < ⊤ → ∃ n, t < τ n ω) ∧
    (∀ n ω t, ‖X (min (τ (n+1) ω) t) ω-X (min (τ n ω) t) ω‖ ≤ δ) := by
  intro τ
  let Z := fun n t ω => X (min (c n) t) ω
  have hZm (n i t) : Measurable[F t] (fun ω => Z n t ω i) :=
    (hm i _ ((min_le_left _ _).trans_lt (hct n))).mono (hF (min_le_right _ _)) le_rfl
  have hZc (n ω) : Continuous (fun t => Z n t ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX ω _ ((min_le_left _ _).trans_lt (hct n))).comp
      (continuous_const.min continuous_id).continuousAt
  have hbase : ∀ n, (∀ t, MeasurableSet[F t] {ω | τ n ω ≤ t}) ∧ ∀ ω, τ n ω ≤ c n := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro t
        change MeasurableSet[F t] {ω : Ω | (⊥ : ClosedTime T) ≤ t}
        simp only [bot_le,Set.ofPred_true]
        exact MeasurableSet.univ
      · intro ω; exact bot_le
    | succ n ih =>
      constructor
      · exact finite_vector_oscillation_step_stopping F hF (Z n) (hZm n) (hZc n) (τ n) ih.1 (c n) δ
      · intro ω
        exact (min_le_right _ _).trans (hc (Nat.le_succ n))
  have hstep (n ω) := vector_oscillation_step_path (fun t => Z n t ω) (hZc n ω)
    (τ n ω) (c n) ((hbase n).2 ω) δ hδ
  have hmon (ω) : Monotone (fun n => τ n ω) := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hstep n ω).1
  have hle (n ω) : τ (n+1) ω ≤ c n := (hstep n ω).2.1
  have hbound (n ω t) : ‖X (min (τ (n+1) ω) t) ω-X (min (τ n ω) t) ω‖ ≤ δ := by
    have ha : min (τ (n+1) ω) t ≤ c n := (min_le_left _ _).trans (hle n ω)
    have hb : min (τ n ω) t ≤ c n := (min_le_left _ _).trans ((hbase n).2 ω)
    have h := (hstep n ω).2.2.1 t
    change ‖Z n (min (τ (n+1) ω) t) ω-Z n (min (τ n ω) t) ω‖ ≤ δ at h
    simpa only [Z,min_eq_right ha,min_eq_right hb] using h
  have hh (n ω) (hn : τ (n+1) ω < c n) : δ ≤ ‖X (τ (n+1) ω) ω-X (τ n ω) ω‖ := by
    have h := (hstep n ω).2.2.2 hn
    change δ ≤ ‖Z n (τ (n+1) ω) ω-Z n (τ n ω) ω‖ at h
    simpa only [Z,min_eq_right (hle n ω),min_eq_right ((hbase n).2 ω)] using h
  exact ⟨fun _ => rfl,fun n => (hbase n).1,hmon,
    fun n ω => ((hbase n).2 ω).trans_lt (hct n),
    fun ω => vector_oscillation_partition_cofinal (fun t => X t ω) (hX ω)
      (fun n => τ n ω) c (hmon ω) hc hcc δ hδ (fun n => hh n ω),hbound⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.constructed_finite_vector_oscillation_partition
