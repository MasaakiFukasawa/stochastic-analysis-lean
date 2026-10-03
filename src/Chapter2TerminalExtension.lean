import Chapter2LocalProcess
import RecentItoTerminalCheck

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- Terminal extension of a half-open-time process. The terminal value of X
is never used. The L2 limit is constructed from the increment energy bound,
and the resulting process has continuous paths on [0,T] and satisfies the
actual conditional-expectation martingale identities, including T. -/
theorem terminal_extension_from_stopped_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n, u n < ⊤)
    (hucofinal : ∀ t, t < ⊤ → ∃ n, t ≤ u n)
    (hX : ∀ n, ContinuousM2Witness P F (fun t ω => X (min (u n) t) ω))
    (a : ℕ → ℝ) (aT : ℝ) (ha : Tendsto a atTop (𝓝 aT))
    (henergy : ∀ n k,
      ‖((hX n).moment ⊤).toLp (fun ω => X (min (u n) ⊤) ω) -
        ((hX k).moment ⊤).toLp (fun ω => X (min (u k) ⊤) ω)‖ ^ 2 ≤ dist (a n) (a k))
    (hisometry : ∀ n,
      ‖((hX n).moment ⊤).toLp (fun ω => X (min (u n) ⊤) ω)‖ ^ 2 = a n) :
    ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
      (∀ t, t < ⊤ → Y t =ᵐ[P] X t) ∧
      Tendsto (fun n => eLpNorm ((fun ω => X (u n) ω) - Y ⊤) 2 P) atTop (𝓝 0) ∧
      ‖(hY.moment ⊤).toLp (Y ⊤)‖ ^ 2 = aT := by
  let V (n) := ((hX n).moment ⊤).toLp (fun ω => X (min (u n) ⊤) ω)
  letI : CompleteSpace (Lp ℝ 2 P) := current_lp_complete
  obtain ⟨v,hv⟩ := Asakura.RecentItoTerminal.terminal_exists_of_energy_bound V a ha.cauchySeq henergy
  obtain ⟨Y,hm,h2,hc,hM,hz,hconv⟩ := continuous_martingale_cauchy_completion P F hF hle hnull
    (fun n t ω => X (min (u n) t) ω)
    (fun n => (hX n).adapted) (fun n => (hX n).moment)
    (fun n => (hX n).path) (fun n => (hX n).martingale) (fun n => (hX n).initial)
    hv.cauchySeq
  let hY : ContinuousM2Witness P F Y := ⟨hm,h2,hc,hM,hz⟩
  refine ⟨Y,hY,?_,?_,?_⟩
  · intro t ht
    obtain ⟨n, hn⟩ := hucofinal t ht
    have hXt : MemLp (X t) 2 P := by
      simpa only [min_eq_right hn] using (hX n).moment t
    have hpoint : Tendsto (fun k => eLpNorm ((fun ω => X (min (u k) t) ω) - X t) 2 P)
        atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      refine eventually_atTop.2 ⟨n, fun k hk => ?_⟩
      simp only [min_eq_right (hn.trans (hu hk)), sub_self, eLpNorm_zero]
    have hcond := conditional_l2_limit_identity P (hle t)
      (fun n ω => X (min (u n) t) ω) (fun n ω => X (min (u n) ⊤) ω)
      (X t) (Y ⊤) (fun n => (hX n).moment t) (fun n => (hX n).moment ⊤)
      hXt (h2 ⊤) (fun n => ((hX n).martingale t ⊤ le_top).symm) hpoint hconv
    exact (hM t ⊤ le_top).symm.trans hcond.symm
  · simpa only [min_top_right] using hconv
  · have hLp := (current_lp_tendsto_Lp_iff_tendsto_eLpNorm_prime_prime
      (fun n ω => X (min (u n) ⊤) ω) (fun n => (hX n).moment ⊤) (Y ⊤) (h2 ⊤)).mpr hconv
    exact Asakura.RecentItoTerminal.terminal_energy_identity V _ a aT hLp ha hisometry

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.terminal_extension_from_stopped_energy
