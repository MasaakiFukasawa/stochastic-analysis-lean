import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter Finset
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- Addition in probability for an arbitrary observation-time filter. -/
theorem probability_add_filter {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter I) (X Y : I → Ω → ℝ) (x y : Ω → ℝ)
    (hX : TendstoInMeasure P X l x) (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i ω => X i ω+Y i ω) l (fun ω => x ω+y ω) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have h1 := tendstoInMeasure_iff_dist.mp hX (ε/2) (by positivity)
  have h2 := tendstoInMeasure_iff_dist.mp hY (ε/2) (by positivity)
  have hh := h1.add h2
  simp only [zero_add] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro i
  apply (measure_mono (show {ω | ε ≤ dist (X i ω+Y i ω) (x ω+y ω)} ⊆
    {ω | ε/2 ≤ dist (X i ω) (x ω)} ∪ {ω | ε/2 ≤ dist (Y i ω) (y ω)} from ?_)).trans
    (measure_union_le _ _)
  intro ω hω
  by_contra hn
  have hx : dist (X i ω) (x ω) < ε/2 := lt_of_not_ge (fun h => hn (Or.inl h))
  have hy : dist (Y i ω) (y ω) < ε/2 := lt_of_not_ge (fun h => hn (Or.inr h))
  have ht := dist_add_add_le (X i ω) (Y i ω) (x ω) (y ω)
  change ε ≤ dist (X i ω+Y i ω) (x ω+y ω) at hω
  linarith

/-- Deterministic multiplication in probability, without restricting the
observation index to a sequence. -/
theorem probability_const_mul_filter {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter I) (X : I → Ω → ℝ) (x : Ω → ℝ)
    (hX : TendstoInMeasure P X l x) (b : ℝ) :
    TendstoInMeasure P (fun i ω => b*X i ω) l (fun ω => b*x ω) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  by_cases hb : b=0
  · simpa [hb,hε.not_ge] using
      (show Tendsto (fun _ : I => (0:ℝ≥0∞)) l (𝓝 0) from tendsto_const_nhds)
  have hab : 0 < |b| := abs_pos.mpr hb
  have hh := tendstoInMeasure_iff_dist.mp hX (ε/|b|) (div_pos hε hab)
  convert hh using 1
  funext i
  congr 1
  ext ω
  simp only [mem_setOf_eq,Real.dist_eq,← mul_sub,abs_mul]
  rw [div_le_iff₀ hab,mul_comm |b|]

/-- Finite sums commute with convergence in probability. -/
theorem probability_sum_filter {Ω I ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter I) (s : Finset ι) (X : ι → I → Ω → ℝ) (x : ι → Ω → ℝ)
    (hX : ∀ j∈s,TendstoInMeasure P (X j) l (x j)) :
    TendstoInMeasure P (fun i ω => ∑ j∈s,X j i ω) l (fun ω => ∑ j∈s,x j ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    simpa [hε.not_ge] using (show Tendsto (fun _ : I => (0:ℝ≥0∞)) l (𝓝 0) from tendsto_const_nhds)
  | @insert j s hj ih =>
    simp only [sum_insert hj]
    exact probability_add_filter P l _ _ _ _ (hX j (mem_insert_self _ _))
      (ih (fun k hk => hX k (mem_insert_of_mem hk)))

/-- Entrywise convergence of the information matrix implies convergence
of every quadratic projection used in the martingale CLT. -/
theorem probability_quadratic_projection {Ω I ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (l : Filter I) (J : I → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hJ : ∀ i j,TendstoInMeasure P (fun t ω => J t ω i j) l (fun _ => S i j))
    (v : ι → ℝ) :
    TendstoInMeasure P (fun t ω => ∑ j,v j*(∑ i,v i*J t ω i j)) l
      (fun _ => ∑ j,v j*(∑ i,v i*S i j)) := by
  apply probability_sum_filter P l univ
  intro j _
  apply probability_const_mul_filter
  apply probability_sum_filter P l univ
  intro i _
  exact probability_const_mul_filter P l _ _ (hJ i j) (v i)

end Asakura.Chapter8
