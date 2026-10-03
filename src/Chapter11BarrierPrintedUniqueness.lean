import Chapter11BarrierCandidateTransform

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4200000

/-- Uniqueness in exactly the bounded C1,2 stock-coordinate class.
 A fresh logarithmic stock is started at each interior point. Continuity
 extends the result to time zero, so no differentiability there is required. -/
theorem stock_barrier_candidates_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (T b r σ : ℝ) (hT : 0<T) (hb : 0<b) (hσ : 0<σ)
    (payoff : ℝ → ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : StockBarrierCandidate T b r σ payoff u)
    (hv : StockBarrierCandidate T b r σ payoff v) :
    ∀ t∈Icc 0 T,∀ x∈Ioc 0 b,u t x=v t x ∨ (t=T ∧ x=b) := by
  have hinterior (t : ℝ) (ht : t∈Ioo 0 T) (x : ℝ) (hx : x∈Ioo 0 b) : u t x=v t x := by
    have hy : Real.log (x/b)<0 := Real.log_neg (div_pos hx.1 hb) ((div_lt_one hb).mpr hx.2)
    have hh := affine_barrier_candidates_equal P B (r-σ^2/2) σ (-t) (T-t) (Real.log (x/b))
      (neg_neg_of_pos ht.1) (sub_pos.mpr ht.2) hσ hy
      (fun y => Real.exp (-r*(T-t))*payoff (b*Real.exp y))
      (fun s y => Real.exp (-r*s)*u (t+s) (b*Real.exp y))
      (fun s y => Real.exp (-r*s)*v (t+s) (b*Real.exp y))
      (stock_barrier_candidate_transform T b r σ t hb ht payoff u hu)
      (stock_barrier_candidate_transform T b r σ t hb ht payoff v hv)
    have he : b*Real.exp (Real.log (x/b))=x := by
      rw [Real.exp_log (div_pos hx.1 hb)]
      field_simp
    simpa only [mul_zero,Real.exp_zero,one_mul,add_zero,he] using hh
  have hinitial (x : ℝ) (hx : x∈Ioo 0 b) : u 0 x=v 0 x := by
    let q := fun n : ℕ => (T/2)*(1/((n:ℝ)+1))
    have hqpos n : 0<q n := by dsimp only [q];positivity
    have hqle n : q n≤T/2 := by
      dsimp only [q]
      apply mul_le_of_le_one_right (by linarith : 0≤T/2)
      exact (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hqlim : Tendsto q atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (T/2)
    have hp : Tendsto (fun n => (q n,x)) atTop (𝓝[Icc 0 (T/2) ×ˢ Ioc 0 b] (0,x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hqlim.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨⟨(hqpos n).le,hqle n⟩,hx.1,hx.2.le⟩⟩
    have hmid : T/2∈Ico 0 T := ⟨by linarith,by linarith⟩
    have hmem : (0,x)∈Icc 0 (T/2) ×ˢ Ioc 0 b := ⟨⟨le_rfl,hmid.1⟩,hx.1,hx.2.le⟩
    have hlu := ((hu.preterminal _ hmid) _ hmem).tendsto.comp hp
    have hlv := ((hv.preterminal _ hmid) _ hmem).tendsto.comp hp
    have he : (fun n => u (q n) x)=(fun n => v (q n) x) := funext fun n =>
      hinterior _ ⟨hqpos n,(hqle n).trans_lt hmid.2⟩ x hx
    exact tendsto_nhds_unique (by simpa only [Function.comp_def,he] using hlu) hlv
  intro t ht x hx
  rcases lt_or_eq_of_le hx.2 with hxb | hxb
  · left
    rcases lt_or_eq_of_le ht.2 with htT | htT
    · rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [←ht0];exact hinitial x ⟨hx.1,hxb⟩
      · exact hinterior t ⟨ht0,htT⟩ x ⟨hx.1,hxb⟩
    · rw [htT,hu.terminal x ⟨hx.1,hxb⟩,hv.terminal x ⟨hx.1,hxb⟩]
  · rcases lt_or_eq_of_le ht.2 with htT | htT
    · left
      rw [hxb,hu.boundary t ⟨ht.1,htT⟩,hv.boundary t ⟨ht.1,htT⟩]
    · exact Or.inr ⟨htT,hxb⟩

end Asakura.Chapter11
