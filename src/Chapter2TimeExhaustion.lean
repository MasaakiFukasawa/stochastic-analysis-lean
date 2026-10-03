import Chapter2LevelLocalization
import Chapter2CompactPathCauchy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- The time intervals [0,u_n] form a genuine compact exhaustion of
[0,T) when u_n is strictly increasing and cofinal below T. -/
noncomputable def intervalTimeExhaustion
    {T : EReal} [Fact (0 ≤ T)] (u : ℕ → ClosedTime T)
    (hu : StrictMono u) (hut : ∀ n, u n < ⊤)
    (hcofinal : ∀ t, t < ⊤ → ∃ n, t < u n) :
    CompactExhaustion (Iio (⊤ : ClosedTime T)) where
  toFun n := {t | t.val ≤ u n}
  isCompact' n := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.2
    have he : Subtype.val '' {t : Iio (⊤ : ClosedTime T) | t.val ≤ u n} = Iic (u n) := by
      ext t
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact hx
      · intro ht
        exact ⟨⟨t,ht.trans_lt (hut n)⟩,ht,rfl⟩
    rw [he]
    exact isClosed_Iic.isCompact
  subset_interior_succ' n := by
    have ho : IsOpen {t : Iio (⊤ : ClosedTime T) | t.val < u (n+1)} :=
      isOpen_Iio.preimage continuous_subtype_val
    apply subset_trans _ (interior_mono (show {t : Iio (⊤ : ClosedTime T) | t.val < u (n+1)} ⊆
      {t | t.val ≤ u (n+1)} from fun t ht => by
        change t.val ≤ u (n+1)
        exact (show t.val < u (n+1) from ht).le))
    rw [ho.interior_eq]
    intro t ht
    exact ht.trans_lt (hu (Nat.lt_succ_self n))
  iUnion_eq' := by
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨n,hn⟩ := hcofinal t.val t.property
    exact mem_iUnion.2 ⟨n,hn.le⟩

/-- A strictly increasing time exhaustion exists also at an infinite
terminal time. Thus the compact-path completeness argument applies to the
actual time domain used throughout Chapter 2. -/
theorem exists_strict_time_exhaustion
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) :
    ∃ u : ℕ → ClosedTime T, StrictMono u ∧ (∀ n, u n < ⊤) ∧
      ∀ t, t < ⊤ → ∃ n, t < u n := by
  have hb : (⊥ : ClosedTime T) < ⊤ := hT
  obtain ⟨u,hu,hm,ht⟩ := exists_seq_strictMono_tendsto' hb
  exact ⟨u,hu,fun n => (hm n).2,fun t ht' => (ht.eventually (lt_mem_nhds ht')).exists⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.exists_strict_time_exhaustion

#print axioms Asakura.Chapter2Complete.intervalTimeExhaustion
