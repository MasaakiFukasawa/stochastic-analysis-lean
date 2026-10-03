import Chapter11BarrierClosedPrice

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The actual call/digital image formula satisfies every condition of
 the bounded C1,2 uniqueness class, with its terminal payoff attached. -/
theorem barrier_price_candidate (b K r σ T : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) :
    StockBarrierCandidate T b r σ (fun x => max (x-K) 0) (barrierClosedPrice b K r σ T) := by
  let u := barrierClosedPrice b K r σ T
  let F := fun z : ℝ × ℝ => u z.1 z.2
  have hsm t x (ht : t<T) (hx : 0<x) : ContDiffAt ℝ ∞ F (t,x) :=
    barrier_closed_smooth b K r σ T t x hb hK hKb hσ ht hx
  have hpart := local_smooth_partial_regular F (Ioo 0 T ×ˢ Ioo 0 b) (isOpen_Ioo.prod isOpen_Ioo)
    (fun z hz => hsm z.1 z.2 hz.1.2 hz.2.1)
  refine ⟨?_,?_,?_,hpart.1,hpart.2.1,hpart.2.2,?_,?_,?_,?_,?_,?_⟩
  · intro t ht x hx
    exact (((hsm t x ht.2 hx.1).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  · intro t ht x hx
    exact ((hsm t x ht.2 hx.1).comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  · intro z hz
    exact (hsm z.1 z.2 hz.1.2 hz.2.1).continuousAt.continuousWithinAt
  · intro t ht x hx
    have he : (fun s => u s x)=ᶠ[𝓝 t] fun s => barrierStockPrice b K r σ (T-s) x := by
      filter_upwards [eventually_lt_nhds ht.2] with s hs
      exact barrier_closed_preterminal hs
    have hspace : u t=barrierStockPrice b K r σ (T-t) := funext fun y => barrier_closed_preterminal ht.2
    change deriv (fun s => u s x) t+r*x*deriv (u t) x+σ^2*x^2/2*deriv (deriv (u t)) x-r*u t x=0
    rw [he.deriv_eq,hspace]
    exact barrier_stock_backward_equation b K r σ T t x hb hK hKb hσ ht.2 hx.1
  · intro R hR z hz
    exact (hsm z.1 z.2 (hz.1.2.trans_lt hR.2) hz.2.1).continuousAt.continuousWithinAt
  · refine ⟨b,hb.le,?_⟩
    intro t ht x hx
    have hlog : Real.log (x/b)≤0 := Real.log_nonpos (div_nonneg hx.1.le hb.le) ((div_le_one hb).mpr hx.2)
    have hh := barrier_stock_price_bounds b K r σ (T-t) (Real.log (x/b)) hb hK hKb hσ (sub_pos.mpr ht.2) hlog
    have he : b*Real.exp (Real.log (x/b))=x := by rw [Real.exp_log (div_pos hx.1 hb)];field_simp
    rw [he] at hh
    rw [barrier_closed_preterminal ht.2,abs_of_nonneg hh.1]
    exact hh.2.1.trans hx.2
  · intro t ht
    rw [barrier_closed_preterminal ht.2,barrier_stock_boundary b K r σ (T-t) hb]
  · intro x _
    exact barrier_closed_terminal b K r σ T x
  · intro x hx
    exact barrier_closed_terminal_continuous b K r σ T x hb hK hKb hσ hx

end Asakura.Chapter11
