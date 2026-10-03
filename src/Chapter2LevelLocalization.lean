import Chapter2LocalProcess
import FullAuditClosedHitting
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IsLUB

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Continuity rules out overshooting a closed level at its first hit. -/
theorem continuous_level_stop_bound
    {ι : Type*} [CompleteLinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [OrderTopology ι]
    (f : ι → ℝ) (hf : Continuous f) (k : ℝ) (h0 : f ⊥ ≤ k) :
    ∀ t ≤ sInf {s | k ≤ f s}, f t ≤ k := by
  let τ := sInf {s | k ≤ f s}
  have hbefore : Iio τ ⊆ f ⁻¹' Iic k := by
    intro t ht
    change f t ≤ k
    by_contra h
    exact (not_le_of_gt ht) (sInf_le (show t ∈ {s | k ≤ f s} from (lt_of_not_ge h).le))
  by_cases hz : τ = ⊥
  · intro t ht
    have he : t = ⊥ := le_bot_iff.mp (by simpa only [τ, hz] using ht)
    simpa only [he] using h0
  · have hn : (Iio τ).Nonempty := ⟨⊥, bot_lt_iff_ne_bot.mpr hz⟩
    have hs := closure_minimal hbefore (isClosed_Iic.preimage hf)
    rw [closure_Iio' hn] at hs
    exact fun t ht => hs ht

/-- The explicit first-level localizers in the manuscript put an M2
martingale in M_loc. u is the arbitrary increasing deterministic exhaustion
T_n < T chosen in the written proof. -/
theorem continuous_m2_is_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) :
    LocalMProcessWitness P F X := by
  let hit (n : ℕ) (ω : Ω) := sInf {t | (n:ℝ) ≤ |X t ω|}
  let τ (n : ℕ) (ω : Ω) := min (hit n ω) (u n)
  have hh (n) : ∀ t, MeasurableSet[F t] {ω | hit n ω ≤ t} :=
    continuous_hitting_stopping_written F hF (fun t ω => |X t ω|)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        simpa only [Real.norm_eq_abs] using (hX.adapted t).norm) (fun ω => (hX.path ω).abs) (Ici (n:ℝ)) isClosed_Ici
  have hτ (n) := (written_stopping_min_max F (hit n) (fun _ => u n) (hh n)
    (fun t => by by_cases h : u n ≤ t <;> simp [h])).1
  have hhitmono (ω) : Monotone (fun n => hit n ω) := by
    intro n k hnk
    apply sInf_le_sInf
    intro t ht
    exact (show (n:ℝ) ≤ k by exact_mod_cast hnk).trans ht
  have hτmono (ω) : Monotone (fun n => τ n ω) := (hhitmono ω).min hu
  have hcofinal (ω t) (ht : t < ⊤) : ∃ n, t < τ n ω := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖(⟨fun s => X s ω, hX.path ω⟩ : C(ClosedTime T,ℝ))‖
    obtain ⟨k, hk⟩ := huc t ht
    refine ⟨max n k, lt_min ?_ (hk.trans_le (hu (le_max_right _ _)))⟩
    have hempty : {s | ((max n k:ℕ):ℝ) ≤ |X s ω|} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hb := (⟨fun s => X s ω, hX.path ω⟩ : C(ClosedTime T,ℝ)).norm_coe_le_norm s
      have hnm : (n:ℝ) ≤ (max n k:ℕ) := by exact_mod_cast le_max_left n k
      exact (not_le_of_gt (hn.trans_le hnm)) (hs.trans (by simpa only [Real.norm_eq_abs, ContinuousMap.coe_mk] using hb))
    simpa only [hit, hempty, sInf_empty] using ht
  refine ⟨τ,hτ,hτmono,(fun n ω => (min_le_right _ _).trans_lt (hut n)),hcofinal,?_⟩
  intro n
  have hm := continuous_m2_stopped P F hF hle X hX (τ n) (hτ n)
  refine ⟨hm, ?_⟩
  intro t
  apply memLp_top_of_bound ((hm.adapted t).mono (hle t) le_rfl).aestronglyMeasurable (n:ℝ)
  filter_upwards [hX.initial] with ω hω
  have hb := continuous_level_stop_bound (fun s => |X s ω|) (hX.path ω).abs (n:ℝ)
    (by simpa only [hω, Pi.zero_apply, abs_zero] using Nat.cast_nonneg (α := ℝ) n)
    (min (τ n ω) t) ((min_le_left _ _).trans (min_le_left _ _))
  simpa only [Real.norm_eq_abs] using hb

/-- The same explicit proof works for every integrable continuous martingale,
so in particular for every M_p with p at least one. -/
theorem continuous_integrable_is_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n)
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t)) (hi : ∀ t, Integrable (X t) P)
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0) :
    LocalMProcessWitness P F X := by
  let hit (n : ℕ) (ω : Ω) := sInf {t | (n:ℝ) ≤ |X t ω|}
  let τ (n : ℕ) (ω : Ω) := min (hit n ω) (u n)
  have hh (n) : ∀ t, MeasurableSet[F t] {ω | hit n ω ≤ t} :=
    continuous_hitting_stopping_written F hF (fun t ω => |X t ω|)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        simpa only [Real.norm_eq_abs] using (hm t).norm) (fun ω => (hc ω).abs) (Ici (n:ℝ)) isClosed_Ici
  have hτ (n) := (written_stopping_min_max F (hit n) (fun _ => u n) (hh n)
    (fun t => by by_cases h : u n ≤ t <;> simp [h])).1
  have hhitmono (ω) : Monotone (fun n => hit n ω) := by
    intro n k hnk
    apply sInf_le_sInf
    intro t ht
    exact (show (n:ℝ) ≤ k by exact_mod_cast hnk).trans ht
  have hτmono (ω) : Monotone (fun n => τ n ω) := (hhitmono ω).min hu
  have hcofinal (ω t) (ht : t < ⊤) : ∃ n, t < τ n ω := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖(⟨fun s => X s ω, hc ω⟩ : C(ClosedTime T,ℝ))‖
    obtain ⟨k, hk⟩ := huc t ht
    refine ⟨max n k, lt_min ?_ (hk.trans_le (hu (le_max_right _ _)))⟩
    have hempty : {s | ((max n k:ℕ):ℝ) ≤ |X s ω|} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hb := (⟨fun s => X s ω, hc ω⟩ : C(ClosedTime T,ℝ)).norm_coe_le_norm s
      have hnm : (n:ℝ) ≤ (max n k:ℕ) := by exact_mod_cast le_max_left n k
      exact (not_le_of_gt (hn.trans_le hnm)) (hs.trans (by simpa only [Real.norm_eq_abs, ContinuousMap.coe_mk] using hb))
    simpa only [hit, hempty, sInf_empty] using ht
  refine ⟨τ,hτ,hτmono,(fun n ω => (min_le_right _ _).trans_lt (hut n)),hcofinal,?_⟩
  intro n
  apply bounded_stop_of_integrable_martingale P F hF hle X hm hi hc hM hz (τ n) (hτ n) (n:ℝ)
  intro t
  filter_upwards [hz] with ω hω
  have hb := continuous_level_stop_bound (fun s => |X s ω|) (hc ω).abs (n:ℝ)
    (by simpa only [hω, Pi.zero_apply, abs_zero] using Nat.cast_nonneg (α := ℝ) n)
    (min (τ n ω) t) ((min_le_left _ _).trans (min_le_left _ _))
  simpa only [Real.norm_eq_abs] using hb

/-- Existence of the deterministic exhaustion is proved also when T is
infinite. This discharges the sequence supplied explicitly above. -/
theorem deterministic_time_exhaustion
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) :
    ∃ u : ℕ → ClosedTime T, Monotone u ∧ (∀ n, u n < ⊤) ∧
      ∀ t, t < ⊤ → ∃ n, t < u n := by
  have hb : (⊥ : ClosedTime T) < ⊤ := hT
  obtain ⟨u,hu,hm,ht⟩ := exists_seq_strictMono_tendsto' hb
  refine ⟨u,hu.monotone,fun n => (hm n).2,?_⟩
  intro t ht'
  exact (ht.eventually (lt_mem_nhds ht')).exists

/-- Proposition 2.5.1 for all p >= 1, including p = infinity,
with the exhaustion constructed rather than assumed. -/
theorem continuous_lp_martingale_is_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t)) (hLp : ∀ t, MemLp (X t) p P)
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0) : LocalMProcessWitness P F X := by
  obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion hT
  exact continuous_integrable_is_local P F hF hle u hu hut huc X hm
    (fun t => (hLp t).integrable hp) hc hM hz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_level_stop_bound
#print axioms Asakura.Chapter2Complete.continuous_m2_is_local

#print axioms Asakura.Chapter2Complete.continuous_integrable_is_local

#print axioms Asakura.Chapter2Complete.deterministic_time_exhaustion
#print axioms Asakura.Chapter2Complete.continuous_lp_martingale_is_local
