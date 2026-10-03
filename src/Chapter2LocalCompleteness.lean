import Chapter2PathMetricLimit
import Chapter2LocalAELimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- A continuous local martingale is a measurable random continuous path
for the local uniform topology. -/
theorem local_martingale_path_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t, F t ≤ m)
    (X : Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : LocalMProcessWitness P F (fun t ω => extendOpenPath (X ω) t)) : Measurable X := by
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  have h := (hX.adapted P F t.val t.property).mono (hle t.val) le_rfl
  convert h using 1
  funext ω
  unfold extendOpenPath
  split_ifs with ht
  · rfl
  · exact (ht t.property).elim

/-- The complete Cauchy construction for local martingales in the
expectation of the geometric-series local uniform distance. Rapid subsequence,
Borel-Cantelli, measurable/null-set handling, common bounded localizers,
dominated convergence, and convergence of the whole sequence are all supplied
by the proved lemmas, rather than included as hypotheses. -/
theorem local_martingale_cauchy_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (K : CompactExhaustion (Iio (⊤ : ClosedTime T)))
    (X : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, LocalMProcessWitness P F (fun t ω => extendOpenPath (X n ω) t))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (∫ ω, pathDistance K (X n ω) (X m ω) ∂P) < ε) :
    ∃ Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ),
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) ∧
      Tendsto (fun n => ∫ ω, pathDistance K (X n ω) (Y ω) ∂P) atTop (𝓝 0) := by
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  have hm (n) := local_martingale_path_measurable P F hle (X n) (hX n)
  obtain ⟨Y,k,N,hY,_,hN,hNP,hsub,hlim⟩ := path_metric_cauchy_limit P K X hm hc
  obtain ⟨Z,hZY,hZ⟩ := ae_locally_uniform_limit_local P hT F hF hle hnull
    (fun n => X (k n)) Y (fun n => hX (k n)) N hN hNP hsub
  refine ⟨Z,hZ,?_⟩
  have he (n) : (∫ ω, pathDistance K (X n ω) (Z ω) ∂P) =
      ∫ ω, pathDistance K (X n ω) (Y ω) ∂P :=
    integral_congr_ae (hZY.mono fun ω hω => congrArg (fun z => pathDistance K (X n ω) z) hω)
  simpa only [he] using hlim

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_martingale_path_measurable
#print axioms Asakura.Chapter2Complete.local_martingale_cauchy_limit
