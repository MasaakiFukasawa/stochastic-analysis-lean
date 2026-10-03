import Chapter11BarrierCandidateClass

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 7500000

/-- Restart a stock-coordinate candidate at an interior time and discount
 it in logarithmic coordinates. All local regularity is derived by the
 chain rule; no second derivative in time is introduced. -/
theorem stock_barrier_candidate_transform
    (T b r σ t0 : ℝ) (hb : 0<b) (ht0 : t0∈Ioo 0 T)
    (payoff : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hu : StockBarrierCandidate T b r σ payoff u) :
    AffineBarrierCandidate (r-σ^2/2) σ (-t0) (T-t0)
      (fun y => Real.exp (-r*(T-t0))*payoff (b*Real.exp y))
      (fun s y => Real.exp (-r*s)*u (t0+s) (b*Real.exp y)) := by
  let v := fun s y => Real.exp (-r*s)*u (t0+s) (b*Real.exp y)
  let g := fun z : ℝ × ℝ => (t0+z.1,b*Real.exp z.2)
  have hg : Continuous g := (continuous_const.add continuous_fst).prodMk
    (continuous_const.mul (Real.continuous_exp.comp continuous_snd))
  have hpos y : 0<b*Real.exp y := mul_pos hb (Real.exp_pos y)
  have hlt y (hy : y<0) : b*Real.exp y<b := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr hy) hb
  have hle y (hy : y≤0) : b*Real.exp y≤b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hy) hb.le
  have htime s (hs : s∈Ioo (-t0) (T-t0)) : t0+s∈Ioo 0 T := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hmap : MapsTo g (Ioo (-t0) (T-t0) ×ˢ Iio 0) (Ioo 0 T ×ˢ Ioo 0 b) :=
    fun z hz => ⟨htime z.1 hz.1,⟨hpos _,hlt _ hz.2⟩⟩
  have hec : Continuous (fun z : ℝ × ℝ => Real.exp (-r*z.1)) := by fun_prop
  have hxc : Continuous (fun z : ℝ × ℝ => b*Real.exp z.2) := by fun_prop
  have hspace s (hs : s∈Ioo (-t0) (T-t0)) y (hy : y<0) : ContDiffAt ℝ 2 (u (t0+s)) (b*Real.exp y) :=
    (hu.space _ (htime s hs)).contDiffAt (isOpen_Ioo.mem_nhds ⟨hpos y,hlt y hy⟩)
  have hdx s (hs : s∈Ioo (-t0) (T-t0)) y (hy : y<0) :=
    discount_log_space_derivatives (u (t0+s)) b (Real.exp (-r*s)) y (hspace s hs y hy)
  have hdt s (hs : s∈Ioo (-t0) (T-t0)) y (hy : y<0) :=
    discount_shift_time_derivative (fun q => u q (b*Real.exp y)) t0 r s
      (hu.time _ (htime s hs) _ ⟨hpos y,hlt y hy⟩)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s hs y hy
    have hh : ContDiffAt ℝ 2 (fun z => u (t0+s) (b*Real.exp z)) y :=
      (hspace s hs y hy).comp y (contDiffAt_const.mul Real.contDiff_exp.contDiffAt)
    exact (contDiffAt_const.mul hh).contDiffWithinAt
  · intro s hs y hy
    exact (hdt s hs y hy).differentiableAt
  · exact hec.continuousOn.mul (hu.joint.comp hg.continuousOn hmap)
  · apply (hec.continuousOn.mul ((hu.dt.comp hg.continuousOn hmap).sub
      ((hu.joint.comp hg.continuousOn hmap).const_mul r))).congr
    intro z hz
    exact (hdt z.1 hz.1 z.2 hz.2).deriv
  · apply ((hec.continuousOn.mul hxc.continuousOn).mul (hu.dx.comp hg.continuousOn hmap)).congr
    intro z hz
    exact (hdx z.1 hz.1 z.2 hz.2).1
  · apply (hec.continuousOn.mul (((hxc.continuousOn.pow 2).mul (hu.dxx.comp hg.continuousOn hmap)).add
      (hxc.continuousOn.mul (hu.dx.comp hg.continuousOn hmap)))).congr
    intro z hz
    exact (hdx z.1 hz.1 z.2 hz.2).2
  · intro s hs y hy
    have hs' : s∈Ioo (-t0) (T-t0) := ⟨by linarith [ht0.1,hs.1],hs.2⟩
    rw [(hdt s hs' y hy).deriv,(hdx s hs' y hy).1,(hdx s hs' y hy).2]
    exact discounted_log_generator_algebra _ _ _ _ _ _ r σ (hu.pde _ (htime s hs') _ ⟨hpos y,hlt y hy⟩)
  · intro R hR
    have hR' : t0+R∈Ico 0 T := ⟨by linarith [ht0.1,hR.1],by linarith [hR.2]⟩
    exact hec.continuousOn.mul ((hu.preterminal _ hR').comp hg.continuousOn (fun z hz =>
      ⟨⟨by linarith [ht0.1,hz.1.1],by linarith [hz.1.2]⟩,⟨hpos _,hle _ hz.2⟩⟩))
  · obtain ⟨K,hK,hbound⟩ := hu.bound
    refine ⟨Real.exp (|r| *(T-t0))*K,?_⟩
    intro s hs y hy
    have hs' : t0+s∈Ico 0 T := ⟨by linarith [ht0.1,hs.1],by linarith [hs.2]⟩
    have hbnd := hbound _ hs' _ ⟨hpos y,hle y hy⟩
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul (Real.exp_le_exp.mpr ?_) hbnd (abs_nonneg _) (Real.exp_pos _).le
    calc
      -r*s ≤ |r| *s := mul_le_mul_of_nonneg_right (neg_le_abs r) hs.1
      _ ≤ |r| *(T-t0) := mul_le_mul_of_nonneg_left hs.2.le (abs_nonneg r)
  · intro s hs
    have hs' : t0+s∈Ico 0 T := ⟨by linarith [ht0.1,hs.1],by linarith [hs.2]⟩
    simp only [Real.exp_zero,mul_one,hu.boundary _ hs',mul_zero]
  · intro y hy
    rw [add_sub_cancel,hu.terminal _ ⟨hpos y,hlt y hy⟩]
  · intro y hy
    have hmap' : MapsTo g (Icc 0 (T-t0) ×ˢ Iic 0) (Icc 0 T ×ˢ Ioc 0 b) := fun z hz =>
      ⟨⟨by linarith [ht0.1,hz.1.1],by linarith [hz.1.2]⟩,⟨hpos _,hle _ hz.2⟩⟩
    have hh0 : ContinuousWithinAt (fun z : ℝ × ℝ => u z.1 z.2)
        (Icc 0 T ×ˢ Ioc 0 b) (g (T-t0,y)) := by
      simpa only [g,add_sub_cancel] using hu.terminal_continuous _ ⟨hpos y,hlt y hy⟩
    have hh := hh0.comp (hg.continuousAt.continuousWithinAt) hmap' 
    exact hec.continuousAt.continuousWithinAt.mul (by simpa only [g,add_sub_cancel,Function.comp_def] using hh)

end Asakura.Chapter11
