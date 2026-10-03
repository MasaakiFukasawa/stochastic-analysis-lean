import Chapter11BarrierStockTerminal
import Chapter11BarrierPrintedUniqueness
import Chapter11LocalSmoothSlices

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- At maturity the payoff defines the price; the excluded barrier corner
 may be assigned any value. Before maturity this is the printed formula. -/
noncomputable def barrierClosedPrice (b K r σ T t x : ℝ) : ℝ :=
  if t<T then barrierStockPrice b K r σ (T-t) x else max (x-K) 0

lemma barrier_closed_preterminal {b K r σ T t x : ℝ} (ht : t<T) :
    barrierClosedPrice b K r σ T t x=barrierStockPrice b K r σ (T-t) x := if_pos ht

lemma barrier_closed_terminal (b K r σ T x : ℝ) :
    barrierClosedPrice b K r σ T T x=max (x-K) 0 := if_neg (lt_irrefl T)

lemma barrier_closed_smooth (b K r σ T t x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (ht : t<T) (hx : 0<x) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => barrierClosedPrice b K r σ T z.1 z.2) (t,x) := by
  have hF := (barrier_stock_price_pde b K r σ (T-t) x hb hK hKb hσ (sub_pos.mpr ht) hx).1
  have hg : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (T-z.1,z.2)) (t,x) :=
    (contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd
  apply (hF.comp (t,x) hg).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds ht] with z hz
  exact barrier_closed_preterminal hz

/-- Joint continuity of the closed price at every allowed terminal point.
 The proof joins the preterminal Gaussian limit and the terminal payoff. -/
theorem barrier_closed_terminal_continuous (b K r σ T x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hx : x∈Ioo 0 b) :
    ContinuousWithinAt (fun z : ℝ × ℝ => barrierClosedPrice b K r σ T z.1 z.2)
      (Icc 0 T ×ˢ Ioc 0 b) (T,x) := by
  rw [ContinuousWithinAt,barrier_closed_terminal]
  change Tendsto (fun z : ℝ × ℝ => if z.1<T then barrierStockPrice b K r σ (T-z.1) z.2 else max (z.2-K) 0)
    (𝓝[Icc 0 T ×ˢ Ioc 0 b] (T,x)) (𝓝 (max (x-K) 0))
  apply Filter.Tendsto.if_nhdsWithin
  · have hl := barrier_stock_joint_terminal b K r σ x hb hK hKb hσ hx.1 hx.2
    have hm : Tendsto (fun z : ℝ × ℝ => (T-z.1,z.2))
        (𝓝[(Icc 0 T ×ˢ Ioc 0 b) ∩ {z : ℝ × ℝ | z.1<T}] (T,x))
        (𝓝[{q : ℝ × ℝ | 0<q.1 ∧ 0<q.2}] (0,x)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
      · have hc : ContinuousAt (fun z : ℝ × ℝ => (T-z.1,z.2)) (T,x) := by fun_prop
        simpa only [sub_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
      · apply Filter.Eventually.mono (self_mem_nhdsWithin (s := (Icc 0 T ×ˢ Ioc 0 b) ∩ {z : ℝ × ℝ | z.1<T}) (a := (T,x)))
        intro z hz
        change 0 < T-z.1 ∧ 0 < z.2
        exact ⟨sub_pos.mpr hz.2,hz.1.2.1⟩
    simpa only [Function.comp_def] using hl.comp hm
  · have hh : ContinuousAt (fun z : ℝ × ℝ => max (z.2-K) 0) (T,x) := by fun_prop
    exact hh.tendsto.mono_left nhdsWithin_le_nhds

end Asakura.Chapter11
