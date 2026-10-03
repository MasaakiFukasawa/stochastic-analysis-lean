import Chapter5RepresentationEndpoints

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Each terminal increment representation determines its conditional
expectation at every time. Summing them recovers the original martingale,
without assuming its path continuity. -/
theorem martingale_represented_increments_telescope
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hYm : ∀ t,Measurable[F t] (Y t))
    (hYi : ∀ t,Integrable (Y t) P)
    (hY : ∀ s t,s ≤ t → P[Y t|F s] =ᵐ[P] Y s)
    (q : ℕ → ClosedTime T) (M : ℕ → ClosedTime T → Ω → ℝ)
    (hM : ∀ n,ContinuousM2Witness P F (M n))
    (hend : ∀ n,M n ⊤ =ᵐ[P] fun w => Y (q (n+1)) w-Y (q n) w)
    (t : ClosedTime T) (N : ℕ) (h0t : q 0 ≤ t) (htN : t ≤ q N) :
    Y t =ᵐ[P] fun w => Y (q 0) w+∑ n ∈ Finset.range N,M n t w := by
  let U := fun n => Y (q (n+1))-Y (q n)
  have hu n : Integrable (U n) P := (hYi _).sub (hYi _)
  have hm n : P[U n|F t] =ᵐ[P] M n t := by
    exact (condExp_congr_ae (hend n).symm).trans ((hM n).martingale t ⊤ le_top)
  have hs : (∑ n ∈ Finset.range N,U n) = Y (q N)-Y (q 0) :=
    Finset.sum_range_sub (fun n => Y (q n)) N
  have hh := condExp_finsetSum (s := Finset.range N) (fun n _ => hu n) (F t)
  rw [hs] at hh
  have hb := condExp_sub (m := F t) (hYi (q N)) (hYi (q 0))
  rw [condExp_of_stronglyMeasurable (hle t)
    ((hYm (q 0)).mono (hF h0t) le_rfl).stronglyMeasurable (hYi (q 0))] at hb
  have hmAll : ∀ᵐ w ∂P,∀ n,P[U n|F t] w=M n t w := ae_all_iff.mpr hm
  filter_upwards [hh,hb,hY t (q N) htN,hmAll] with w hhw hbw hyt hmw
  have he : Y t w-Y (q 0) w=∑ n ∈ Finset.range N,M n t w := by
    simpa only [Pi.sub_apply,Finset.sum_apply,hyt,hmw] using hbw.symm.trans hhw
  linarith only [he]

end Asakura.Chapter5
