import Chapter11BarrierStockTerminal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

noncomputable def barrierGaussianStockPrice (b K r σ θ x : ℝ) : ℝ :=
  Real.exp (-r*θ)*(barrierGaussianAverage b K (r-σ^2/2) σ θ (Real.log (x/b))-
    Real.exp (-(2*r/σ^2-1)*Real.log (x/b))*barrierGaussianAverage b K (r-σ^2/2) σ θ (-Real.log (x/b)))

theorem barrier_gaussian_stock_eq (b K r σ θ x : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hθ : 0<θ) (hx : 0<x) :
    barrierGaussianStockPrice b K r σ θ x=barrierStockPrice b K r σ θ x := by
  have he : b*Real.exp (Real.log (x/b))=x := by rw [Real.exp_log (div_pos hx hb)];field_simp
  have h := barrier_stock_gaussian_formula b K r σ θ (Real.log (x/b)) hb hK hKb hσ hθ
  rw [he] at h
  exact h.symm

theorem barrier_gaussian_stock_zero (b K r σ x : ℝ) (hb : 0<b) (hx : 0<x) (hxb : x<b) :
    barrierGaussianStockPrice b K r σ 0 x=max (x-K) 0 := by
  have hy : Real.log (x/b)<0 := Real.log_neg (div_pos hx hb) ((div_lt_one hb).mpr hxb)
  have hn : ¬ -Real.log (x/b)<0 := by linarith
  simp only [barrierGaussianStockPrice,barrierGaussianAverage,mul_zero,neg_zero,Real.exp_zero,
    Real.sqrt_zero,zero_mul,add_zero,hy,ite_true,hn,ite_false,integral_const,
    probReal_univ,one_smul,integral_zero,sub_zero,one_mul]
  rw [Real.exp_log (div_pos hx hb)]
  congr 1
  field_simp

/-- The compact-uniform terminal convergence asserted in the barrier
proof follows from joint continuity of the Gaussian image formula. -/
theorem barrier_uniform_terminal (b K r σ : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ)
    (E : Set ℝ) (hE : IsCompact E) (hEsub : E⊆Ioo 0 b) :
    TendstoUniformlyOn (barrierGaussianStockPrice b K r σ) (fun x => max (x-K) 0)
      (𝓝[Icc (0:ℝ) 1] 0) E := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => barrierGaussianStockPrice b K r σ q.1 q.2) (Icc (0:ℝ) 1 ×ˢ E) := by
    intro q hq
    have hx := hEsub hq.2
    rcases eq_or_lt_of_le hq.1.1 with hzero|hpos
    · have hy : Real.log (q.2/b)<0 := Real.log_neg (div_pos hx.1 hb) ((div_lt_one hb).mpr hx.2)
      have hh := barrier_image_joint_endpoint b K (r-σ^2/2) σ (2*r/σ^2-1) r (Real.log (q.2/b)) hb hK hKb hσ.le hy
      have hmap : ContinuousAt (fun p : ℝ × ℝ => (p.1,Real.log (p.2/b))) q :=
        continuousAt_fst.prodMk ((continuousAt_snd.div_const b).log (div_pos hx.1 hb).ne')
      have hmap' : Tendsto (fun p : ℝ × ℝ => (p.1,Real.log (p.2/b))) (𝓝 q) (𝓝 (0,Real.log (q.2/b))) := by
        simpa only [←hzero] using hmap.tendsto
      have hlim := hh.comp hmap'
      have he : b*Real.exp (Real.log (q.2/b))=q.2 := by rw [Real.exp_log (div_pos hx.1 hb)];field_simp
      rw [he] at hlim
      have hcq : ContinuousAt (fun p : ℝ × ℝ => barrierGaussianStockPrice b K r σ p.1 p.2) q := by
        change Tendsto (fun p : ℝ × ℝ => barrierGaussianStockPrice b K r σ p.1 p.2) (𝓝 q) (𝓝 (barrierGaussianStockPrice b K r σ q.1 q.2))
        rw [←hzero,barrier_gaussian_stock_zero b K r σ q.2 hb hx.1 hx.2]
        exact hlim
      exact hcq.continuousWithinAt
    · have heq : (fun p : ℝ × ℝ => barrierGaussianStockPrice b K r σ p.1 p.2)=ᶠ[𝓝 q]
          fun p => barrierStockPrice b K r σ p.1 p.2 := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hpos,
          (isOpen_lt continuous_const continuous_snd).mem_nhds hx.1] with p hpθ hpx
        exact barrier_gaussian_stock_eq b K r σ p.1 p.2 hb hK hKb hσ hpθ hpx
      exact ((barrier_stock_price_pde b K r σ q.1 q.2 hb hK hKb hσ hpos hx.1).1.continuousAt.congr heq.symm).continuousWithinAt
  have hu := (isCompact_Icc.prod hE).uniformContinuousOn_of_continuous hc
  have ht := UniformContinuousOn.tendstoUniformlyOn (F:=barrierGaussianStockPrice b K r σ)
    (by convert hu using 1;funext q;rcases q with ⟨t,x⟩;rfl) (show (0:ℝ)∈Icc 0 1 by simp)
  apply ht.congr_right
  intro x hx
  exact barrier_gaussian_stock_zero b K r σ x hb (hEsub hx).1 (hEsub hx).2

end Asakura.Chapter11
