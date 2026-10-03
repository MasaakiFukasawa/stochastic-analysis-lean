import Chapter11BarrierStockPDE
import Chapter11BarrierLowerBoundary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The barrier value vanishes exactly, before maturity. -/
theorem barrier_stock_boundary (b K r σ θ : ℝ) (hb : 0<b) :
    barrierStockPrice b K r σ θ b=0 := by
  dsimp only [barrierStockPrice]
  rw [div_self hb.ne',Real.one_rpow,one_mul,show b^2/b=b by field_simp]
  exact sub_self _

/-- The original stock price has the correct joint terminal limit at
every interior stock value; no continuity is required at the corner x=b. -/
theorem barrier_stock_joint_terminal (b K r σ x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hx : 0<x) (hxb : x<b) :
    Tendsto (fun q : ℝ × ℝ => barrierStockPrice b K r σ q.1 q.2)
      (𝓝[{q : ℝ × ℝ | 0<q.1 ∧ 0<q.2}] (0,x)) (𝓝 (max (x-K) 0)) := by
  have hy : Real.log (x/b)<0 := Real.log_neg (div_pos hx hb) ((div_lt_one hb).mpr hxb)
  have hh := barrier_image_joint_endpoint b K (r-σ^2/2) σ (2*r/σ^2-1) r (Real.log (x/b)) hb hK hKb hσ.le hy
  have hmap : ContinuousAt (fun q : ℝ × ℝ => (q.1,Real.log (q.2/b))) (0,x) :=
    continuousAt_fst.prodMk ((continuousAt_snd.div_const b).log (div_pos hx hb).ne')
  have hmap' : Tendsto (fun q : ℝ × ℝ => (q.1,Real.log (q.2/b))) (𝓝 (0,x)) (𝓝 (0,Real.log (x/b))) := hmap.tendsto
  have hl := (hh.comp hmap').mono_left (nhdsWithin_le_nhds (s:={q : ℝ × ℝ | 0<q.1 ∧ 0<q.2}))
  have he : b*Real.exp (Real.log (x/b))=x := by rw [Real.exp_log (div_pos hx hb)];field_simp
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hqx : b*Real.exp (Real.log (q.2/b))=q.2 := by rw [Real.exp_log (div_pos hq.2 hb)];field_simp
  have h := barrier_stock_gaussian_formula b K r σ q.1 (Real.log (q.2/b)) hb hK hKb hσ hq.1
  rw [hqx] at h
  exact h.symm

end Asakura.Chapter11
