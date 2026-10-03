import Chapter2LevelLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Explicit common level localizers for a continuous adapted process on
[0,T). No martingale assumption is needed for their construction. -/
theorem continuous_process_bounded_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (htop : ∀ n ω, τ n ω < ⊤)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (hAdapted : ∀ n t, Measurable[F t] (fun ω => X (min (τ n ω) t) ω))
    (hContinuous : ∀ n ω, Continuous (fun t => X (min (τ n ω) t) ω))
    (hInitial : ∀ n, (fun ω => X (min (τ n ω) ⊥) ω) =ᵐ[P] 0) :
    ∃ σ : ℕ → Ω → ClosedTime T,
      (∀ n t, MeasurableSet[F t] {ω | σ n ω ≤ t}) ∧
      (∀ ω, Monotone (fun n => σ n ω)) ∧ (∀ n ω, σ n ω < ⊤) ∧
      (∀ ω t, t < ⊤ → ∃ n, t < σ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ n ω) t) ω‖ ≤ (n:ℝ)) := by
  let Y := fun (n : ℕ) (t : ClosedTime T) (ω : Ω) => X (min (τ n ω) t) ω
  let hit := fun (n : ℕ) (ω : Ω) => sInf {t | (n:ℝ) ≤ |Y n t ω|}
  let σ := fun (n : ℕ) (ω : Ω) => min (hit n ω) (τ n ω)
  have hhit (n) : ∀ t, MeasurableSet[F t] {ω | hit n ω ≤ t} :=
    continuous_hitting_stopping_written F hF (fun t ω => |Y n t ω|)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        simpa only [Real.norm_eq_abs] using (hAdapted n t).norm)
      (fun ω => (hContinuous n ω).abs) (Ici (n:ℝ)) isClosed_Ici
  have hσ (n) := (written_stopping_min_max F (hit n) (τ n) (hhit n) (hτ n)).1
  have hσle (n ω) : σ n ω ≤ τ n ω := min_le_right _ _
  have hσtop (n ω) : σ n ω < ⊤ := (hσle n ω).trans_lt (htop n ω)
  have hσmono (ω) : Monotone (fun n => σ n ω) := by
    intro n k hnk
    by_contra hn
    have hlt : σ k ω < σ n ω := lt_of_not_ge hn
    have hkt : σ k ω < τ k ω := hlt.trans_le ((hσle n ω).trans (hmono ω hnk))
    have hh : hit k ω < τ k ω := by
      exact (min_lt_iff.mp hkt).resolve_right (lt_irrefl _)
    have hσk : σ k ω = hit k ω := min_eq_left hh.le
    have hex : ∃ s ≤ σ k ω, (k:ℝ) ≤ |Y k s ω| := by
      apply (closed_hitting_lower_event (fun s => |Y k s ω|) (hContinuous k ω).abs
        (Ici (k:ℝ)) isClosed_Ici (σ k ω) (hσtop k ω)).mp
      exact hσk.ge
    obtain ⟨s,hs,hlevel⟩ := hex
    have hsn : s ≤ τ n ω := hs.trans (hlt.le.trans (hσle n ω))
    have hsk : s ≤ τ k ω := hsn.trans (hmono ω hnk)
    have hsame : Y n s ω = Y k s ω := by
      simp only [Y,min_eq_right hsn,min_eq_right hsk]
    have hhitle : hit n ω ≤ s := sInf_le (show (n:ℝ) ≤ |Y n s ω| by
      rw [hsame]
      exact (show (n:ℝ) ≤ k by exact_mod_cast hnk).trans hlevel)
    exact (not_le_of_gt hlt) ((min_le_left _ _).trans (hhitle.trans hs))
  have hσcofinal (ω t) (ht : t < ⊤) : ∃ n, t < σ n ω := by
    obtain ⟨j,hj⟩ := hcofinal ω t ht
    let f : C(ClosedTime T,ℝ) := ⟨fun s => Y j s ω,hContinuous j ω⟩
    obtain ⟨k,hk⟩ := exists_nat_gt ‖f‖
    let n := max j k
    have htτ : t < τ n ω := hj.trans_le (hmono ω (le_max_left _ _))
    have hthit : t < hit n ω := by
      by_contra hh
      obtain ⟨s,hs,hlevel⟩ := (closed_hitting_lower_event (fun s => |Y n s ω|)
        (hContinuous n ω).abs (Ici (n:ℝ)) isClosed_Ici t ht).mp (le_of_not_gt hh)
      have hsame : Y n s ω = f s := by
        simp only [Y,f,ContinuousMap.coe_mk,min_eq_right (hs.trans htτ.le),min_eq_right (hs.trans hj.le)]
      rw [hsame] at hlevel
      have hb : |f s| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm s
      have hkn : (k:ℝ) ≤ n := by exact_mod_cast le_max_right j k
      exact (not_le_of_gt (hk.trans_le hkn)) (hlevel.trans hb)
    exact ⟨n,lt_min hthit htτ⟩
  refine ⟨σ,hσ,hσmono,hσtop,hσcofinal,?_⟩
  intro n
  have heq : (fun t ω => Y n (min (σ n ω) t) ω) =
      (fun t ω => X (min (σ n ω) t) ω) := by
    funext t ω
    exact congrArg (fun s => X s ω) (min_eq_right ((min_le_left _ _).trans (hσle n ω)))
  filter_upwards [hInitial n] with ω hω
  intro t
  have h0 : |Y n ⊥ ω| ≤ (n:ℝ) := by
    simpa only [Y,hω,Pi.zero_apply,abs_zero] using Nat.cast_nonneg (α := ℝ) n
  have hb := continuous_level_stop_bound (fun s => |Y n s ω|) (hContinuous n ω).abs
    (n:ℝ) h0 (min (σ n ω) t) ((min_le_left _ _).trans (min_le_left _ _))
  have he := congrFun (congrFun heq t) ω
  simpa only [Real.norm_eq_abs,he] using hb

/-- The half-open version, using a deterministic exhaustion of [0,T).
The value at T is used only for the harmless adapted extension, never in
a stopped value. No left limit at T is required. -/
theorem halfopen_continuous_bounded_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (hz : X ⊥ =ᵐ[P] 0) :
    ∃ σ : ℕ → Ω → ClosedTime T,
      (∀ n t, MeasurableSet[F t] {ω | σ n ω ≤ t}) ∧
      (∀ ω, Monotone (fun n => σ n ω)) ∧ (∀ n ω, σ n ω < ⊤) ∧
      (∀ ω t, t < ⊤ → ∃ n, t < σ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ n ω) t) ω‖ ≤ (n:ℝ)) := by
  obtain ⟨u,hu,hut,huc⟩ := deterministic_time_exhaustion hT
  have hr (ω t) : ContinuousWithinAt (fun s => X s ω) (Ici t) t := by
    by_cases ht : t < ⊤
    · exact (hc ω t ht).continuousWithinAt
    · have he : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
      subst t
      simp only [Ici_top]
      exact continuousWithinAt_singleton
  apply continuous_process_bounded_localizers P F hF X (fun n _ => u n)
    (fun n t => by by_cases h : u n ≤ t <;> simp [h]) (fun _ => hu) (fun n _ => hut n)
    (fun _ => huc)
  · intro n
    exact stopped_min_value_measurable F hF (fun _ => u n)
      (fun t => by by_cases h : u n ≤ t <;> simp [h]) X hm hr
  · intro n ω
    apply continuous_iff_continuousAt.2
    intro t
    exact (hc ω _ ((min_le_left _ _).trans_lt (hut n))).comp
      (continuous_const.min continuous_id).continuousAt
  · intro n
    simpa only [min_bot_right] using hz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_process_bounded_localizers

#print axioms Asakura.Chapter2Complete.halfopen_continuous_bounded_localizers
