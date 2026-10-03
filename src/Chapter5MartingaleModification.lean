import Chapter5ConstructedPastedIntegral
import Chapter5FiniteTimeMartingaleTelescoping

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The pasted Ito integral is a continuous modification of the original
martingale. Only finite-time measurability, moments and conditional expectation
identities of that martingale are assumed. -/
theorem martingale_modification_from_interval_representations
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (H : ℕ → Ω × ℝ → ℝ) (hm : ∀ j,Measurable (H j))
    (hp : ∀ j l,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c l) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c l) => H j (z.1,z.2.val)))
    (hi : ∀ j,MemLp (H j) 2 (P.prod (volume.restrict (Ioi 0))))
    (hNat : ∀ N : ℕ,((N:ℝ):EReal)<T)
    (Y : ClosedTime T → Ω → ℝ)
    (hYm : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hYi : ∀ t,t<⊤ → Integrable (Y t) P)
    (hY : ∀ s t,t<⊤ → s≤t → P[Y t|F s] =ᵐ[P] Y s)
    (M : ℕ → ClosedTime T → Ω → ℝ) (hM : ∀ j,ContinuousM2Witness P F (M j))
    (hI : ∀ (j : ℕ),ItoCovarianceFormula P F W
      (fun z => (Ioc (j:ℝ) (j+1)).indicator (fun r => H j (z.1,r)) z.2) (M j))
    (hend : ∀ j,M j ⊤ =ᵐ[P] fun w => Y (realTimeClamp ((j+1:ℕ):ℝ)) w-Y (realTimeClamp (j:ℝ)) w) :
    let G := fun z : Ω × ℝ => H (Nat.ceil z.2-1) z
    ∃ J : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F J ∧ ItoCovarianceFormula P F W G J ∧
      (∀ R : ℝ,MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) ∧
      ∀ t,t<⊤ → Y t =ᵐ[P] fun w => Y ⊥ w+J t w := by
  dsimp only
  have hMl j := continuous_m2_is_local P F hF hle
    (fun l => realTimeClamp (T := T) (c l)) hct.monotone hcut hcc (M j) (hM j)
  obtain ⟨J,hJ,hJI,hgl,hprefix⟩ := ceil_pasted_integral_constructed P hT F hF hle hnull W A hW hA
    c hc hcm hcT hct hcut hcc hclock H hm hp hi M hMl hI
  refine ⟨J,hJ,hJI,hgl,?_⟩
  have hq (N : ℕ) : realTimeClamp (T := T) (N:ℝ)<⊤ := by
    change (realTimeClamp (N:ℝ):EReal)<T
    rw [real_time_clamp_eq _ (Nat.cast_nonneg N) (hNat N).le]
    exact hNat N
  have hzero : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    exact (real_time_clamp_eq 0 le_rfl (by exact_mod_cast hT.le)).trans (by simp)
  intro t ht
  obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t ht
  let N := Nat.ceil r
  have htN : realTimeClamp (T := T) r≤realTimeClamp (N:ℝ) := real_time_clamp_mono (Nat.le_ceil r)
  have htel := finite_time_martingale_increments_telescope P F hF hle Y hYm hYi hY
    (fun j => realTimeClamp (j:ℝ)) hq M hM hend (realTimeClamp r) N
    (by simp only [Nat.cast_zero,hzero]; exact bot_le) htN
  filter_upwards [htel,hprefix] with w hw hpw
  simp only [Nat.cast_zero,hzero] at hw
  have hh := hpw N (realTimeClamp r) ht
  rw [min_eq_right htN] at hh
  rw [← hh] at hw
  exact hw

end Asakura.Chapter5
