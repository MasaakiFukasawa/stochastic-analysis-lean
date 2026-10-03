import Chapter2LevelLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- An increasing M2-localization can be refined to the bounded
localization required by the manuscript's definition of M_loc. The new
localizers are actual first-level hitting times, cut off at the old ones. -/
theorem m2_localization_implies_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (htop : ∀ n ω, τ n ω < ⊤)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (hM : ∀ n, ContinuousM2Witness P F (fun t ω => X (min (τ n ω) t) ω)) :
    LocalMProcessWitness P F X := by
  let Y := fun (n : ℕ) (t : ClosedTime T) (ω : Ω) => X (min (τ n ω) t) ω
  let hit := fun (n : ℕ) (ω : Ω) => sInf {t | (n:ℝ) ≤ |Y n t ω|}
  let σ := fun (n : ℕ) (ω : Ω) => min (hit n ω) (τ n ω)
  have hhit (n) : ∀ t, MeasurableSet[F t] {ω | hit n ω ≤ t} :=
    continuous_hitting_stopping_written F hF (fun t ω => |Y n t ω|)
      (fun t => by
        letI : MeasurableSpace Ω := F t
        simpa only [Real.norm_eq_abs] using ((hM n).adapted t).norm)
      (fun ω => ((hM n).path ω).abs) (Ici (n:ℝ)) isClosed_Ici
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
      apply (closed_hitting_lower_event (fun s => |Y k s ω|) ((hM k).path ω).abs
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
    let f : C(ClosedTime T,ℝ) := ⟨fun s => Y j s ω,(hM j).path ω⟩
    obtain ⟨k,hk⟩ := exists_nat_gt ‖f‖
    let n := max j k
    have htτ : t < τ n ω := hj.trans_le (hmono ω (le_max_left _ _))
    have hthit : t < hit n ω := by
      by_contra hh
      obtain ⟨s,hs,hlevel⟩ := (closed_hitting_lower_event (fun s => |Y n s ω|)
        ((hM n).path ω).abs (Ici (n:ℝ)) isClosed_Ici t ht).mp (le_of_not_gt hh)
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
  have hstop := continuous_m2_stopped P F hF hle (Y n) (hM n) (σ n) (hσ n)
  rw [heq] at hstop
  refine ⟨hstop,?_⟩
  intro t
  apply memLp_top_of_bound ((hstop.adapted t).mono (hle t) le_rfl).aestronglyMeasurable (n:ℝ)
  filter_upwards [(hM n).initial] with ω hω
  have h0 : |Y n ⊥ ω| ≤ (n:ℝ) := by
    simpa only [Y,hω,Pi.zero_apply,abs_zero] using Nat.cast_nonneg (α := ℝ) n
  have hb := continuous_level_stop_bound (fun s => |Y n s ω|) ((hM n).path ω).abs
    (n:ℝ) h0 (min (σ n ω) t) ((min_le_left _ _).trans (min_le_left _ _))
  have he := congrFun (congrFun heq t) ω
  simpa only [Real.norm_eq_abs,he] using hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.m2_localization_implies_local
