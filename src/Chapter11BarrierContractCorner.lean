import Chapter11BarrierConstructionComplete

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript assigns zero at the excluded terminal barrier corner. -/
noncomputable def barrierContractPrice (b K r σ T t x : ℝ) : ℝ :=
  if t=T ∧ x=b then 0 else barrierClosedPrice b K r σ T t x

lemma barrier_contract_preterminal {b K r σ T t x : ℝ} (ht : t<T) :
    barrierContractPrice b K r σ T t x=barrierStockPrice b K r σ (T-t) x := by
  rw [barrierContractPrice,if_neg (fun h => ht.ne h.1),barrier_closed_preterminal ht]

lemma barrier_contract_terminal (b K r σ T x : ℝ) (hx : x<b) :
    barrierContractPrice b K r σ T T x=max (x-K) 0 := by
  rw [barrierContractPrice,if_neg (fun h => hx.ne h.2),barrier_closed_terminal]

lemma barrier_contract_corner (b K r σ T : ℝ) : barrierContractPrice b K r σ T T b=0 := by
  simp only [barrierContractPrice,and_self,if_true]

lemma barrier_contract_smooth (b K r σ T t x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (ht : t<T) (hx : 0<x) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => barrierContractPrice b K r σ T z.1 z.2) (t,x) := by
  apply (barrier_closed_smooth b K r σ T t x hb hK hKb hσ ht hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds ht] with z hz
  exact if_neg (fun h => hz.ne h.1)

lemma barrier_contract_terminal_continuous (b K r σ T x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hx : x∈Ioo 0 b) :
    ContinuousWithinAt (fun z : ℝ × ℝ => barrierContractPrice b K r σ T z.1 z.2)
      (Icc 0 T ×ˢ Ioc 0 b) (T,x) := by
  apply (barrier_closed_terminal_continuous b K r σ T x hb hK hKb hσ hx).congr_of_eventuallyEq
  · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hx.2] with z hz
    exact if_neg (fun h => hz.ne h.2)
  · exact if_neg (fun h => hx.2.ne h.2)

theorem barrier_contract_candidate (b K r σ T : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) :
    StockBarrierCandidate T b r σ (fun x => max (x-K) 0) (barrierContractPrice b K r σ T) := by
  let u := barrierContractPrice b K r σ T
  let F := fun z : ℝ × ℝ => u z.1 z.2
  have hsm t x (ht : t<T) (hx : 0<x) : ContDiffAt ℝ ∞ F (t,x) :=
    barrier_contract_smooth b K r σ T t x hb hK hKb hσ ht hx
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
      exact barrier_contract_preterminal hs
    have hspace : u t=barrierStockPrice b K r σ (T-t) := funext fun y => barrier_contract_preterminal ht.2
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
    rw [barrier_contract_preterminal ht.2,abs_of_nonneg hh.1]
    exact hh.2.1.trans hx.2
  · intro t ht
    rw [barrier_contract_preterminal ht.2,barrier_stock_boundary b K r σ (T-t) hb]
  · intro x hx
    exact barrier_contract_terminal b K r σ T x hx.2
  · intro x hx
    exact barrier_contract_terminal_continuous b K r σ T x hb hK hKb hσ hx


/-- The contract's specified corner value completes uniqueness on the
 entire stock/time domain, including the excluded continuity point. -/
theorem stock_barrier_unique_with_corner {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (B : Asakura.Chapter4.BrownianSystem P 1)
    (T b r σ : ℝ) (hT : 0<T) (hb : 0<b) (hσ : 0<σ)
    (payoff : ℝ → ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : StockBarrierCandidate T b r σ payoff u)
    (hv : StockBarrierCandidate T b r σ payoff v) (he : u T b=v T b) :
    ∀ t∈Icc 0 T,∀ x∈Ioc 0 b,u t x=v t x := by
  intro t ht x hx
  rcases stock_barrier_candidates_unique P B T b r σ hT hb hσ payoff u v hu hv t ht x hx with h|h
  · exact h
  · rcases h with ⟨rfl,rfl⟩;exact he

end Asakura.Chapter11
