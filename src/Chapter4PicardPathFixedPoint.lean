import Chapter4PicardFatou

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Restore the initial path to the convergent increment series. The output
is the limit of the actual iterates, simultaneously adapted, continuous,
and L2-convergent. -/
theorem adapted_picard_iterates_limit
    {Ω D : Type*} {m : MeasurableSpace Ω}
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : D → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ℕ → Ω → C(D,ℝ)) (hm : ∀ n, Measurable[m] (X n))
    (ha : ∀ n t, Measurable[F t] (fun ω => X n ω t))
    (hi : MemLp (X 0) 2 P) (A a : ℝ) (ha0 : 0 ≤ a)
    (hb : ∀ n, eLpNorm (fun ω => X (n+1) ω-X n ω) 2 P ≤
      ENNReal.ofReal (A*Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∃ Y : Ω → C(D,ℝ), Measurable[m] Y ∧
      (∀ t, Measurable[F t] (fun ω => Y ω t)) ∧ MemLp Y 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => eLpNorm (fun ω => Y ω-X n ω) 2 P) atTop (𝓝 0) := by
  let Z : ℕ → Ω → C(D,ℝ) := fun n ω => X (n+1) ω-X n ω
  have hZm n : Measurable[m] (Z n) := (hm (n+1)).sub (hm n)
  have hZa n t : Measurable[F t] (fun ω => Z n ω t) := by
    change Measurable[F t] (fun ω => X (n+1) ω t-X n ω t)
    exact (ha (n+1) t).sub (ha n t)
  obtain ⟨Y,hYm,hYa,hYi,hlim,hL2⟩ := adapted_picard_series_L2_limit P F hnull Z
    hZm hZa A a ha0 hb
  have hsum n ω : (∑ k ∈ Finset.range n, Z k ω) = X n ω-X 0 ω :=
    Finset.sum_range_sub (fun k => X k ω) n
  refine ⟨fun ω => X 0 ω+Y ω,?_,?_,?_,?_,?_⟩
  · exact (hm 0).add hYm
  · intro t
    change Measurable[F t] (fun ω => X 0 ω t+Y ω t)
    exact (ha 0 t).add (hYa t)
  · exact MemLp.add (f := X 0) (g := Y) (p := 2) (μ := P) hi hYi
  · filter_upwards [hlim] with ω hω
    have h := (tendsto_const_nhds (x := X 0 ω) (f := atTop)).add hω
    have he n : X 0 ω+(∑ k ∈ Finset.range n, Z k ω) = X n ω := by
      rw [hsum]
      abel
    simpa only [he] using h
  · have he n : (fun ω => X 0 ω+Y ω-X n ω) =
        (fun ω => Y ω-∑ k ∈ Finset.range n, Z k ω) := by
      funext ω
      rw [hsum]
      abel
    simpa only [← he] using hL2

/-- Identify the already constructed adapted L2 limit as a fixed point,
using the manuscript's three-term estimate. Equality holds outside one
null set as an equality of continuous paths, not separately at each time. -/
theorem picard_path_limit_fixed_ae
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Φ : (Ω → E) → Ω → E)
    (X : ℕ → Ω → E) (Y : Ω → E)
    (hiter : ∀ n, X (n+1) =ᵐ[P] Φ (X n))
    (hlim : Tendsto (fun n => eLpNorm (fun ω => Y ω-X n ω) 2 P) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hest : ∀ n, eLpNorm (fun ω => Φ (X n) ω-Φ Y ω) 2 P ≤
      C*eLpNorm (fun ω => Y ω-X n ω) 2 P) : Y =ᵐ[P] Φ Y := by
  have hb n : eLpNorm (fun ω => Y ω-Φ Y ω) 2 P ≤
      eLpNorm (fun ω => Y ω-X (n+1) ω) 2 P+C*eLpNorm (fun ω => Y ω-X n ω) 2 P := by
    have he : (fun ω => Y ω-Φ Y ω) =ᵐ[P]
        (fun ω => (Y ω-X (n+1) ω)+(Φ (X n) ω-Φ Y ω)) := by
      filter_upwards [hiter n] with ω hω
      rw [hω]
      abel
    rw [eLpNorm_congr_ae he]
    exact (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans (add_le_add le_rfl (hest n))
  have ht := (hlim.comp (tendsto_add_atTop_nat 1)).add
    ((ENNReal.continuous_const_mul hC).tendsto 0 |>.comp hlim)
  have hz : eLpNorm (fun ω => Y ω-Φ Y ω) 2 P = 0 := by
    apply le_antisymm _ bot_le
    change eLpNorm (fun ω => Y ω-Φ Y ω) 2 P ≤ (0:ℝ≥0∞)
    exact ge_of_tendsto (by simpa only [Function.comp_apply,mul_zero,add_zero] using ht) (.of_forall hb)
  have he := (eLpNorm_eq_zero_iff (by norm_num : (2:ℝ≥0∞) ≠ 0)).1 hz
  filter_upwards [he] with ω hω
  exact sub_eq_zero.mp hω

end Asakura.Chapter4
