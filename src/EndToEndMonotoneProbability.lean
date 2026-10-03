import Chapter7MonotoneClockProbability
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.EndToEnd
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The appendix's general continuous deterministic limit, on a finite
interval. No almost-sure convergent subsequence is used. -/
theorem monotone_uniform_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (hT : 0 ≤ T)
    (A : ℕ → ℝ → Ω → ℝ) (a : ℝ → ℝ)
    (hm : ∀ n ω, MonotoneOn (fun t => A n t ω) (Icc 0 T))
    (ha : ContinuousOn a (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, TendstoInMeasure P (fun n => A n t) atTop (fun _ => a t))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ∃ t ∈ Icc 0 T, ε ≤ |A n t ω - a t|}) atTop (𝓝 0) := by
  classical
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous ha) (ε/4) (by positivity)
  let η := δ/2
  have hη : 0 < η := half_pos hδ
  obtain ⟨N,hN⟩ := exists_nat_gt (T/η)
  let grid := fun k : Fin (N+1) => min ((k:ℕ)*η) T
  have hg k : grid k ∈ Icc 0 T := ⟨le_min (by positivity) hT,min_le_right _ _⟩
  let E := fun n (k : Fin (N+1)) => {ω | ε/2 ≤ |A n (grid k) ω - a (grid k)|}
  have hsub n : {ω | ∃ t ∈ Icc 0 T, ε ≤ |A n t ω - a t|} ⊆ ⋃ k : Fin (N+1), E n k := by
    intro ω hω
    obtain ⟨t,ht,he⟩ := hω
    by_contra hnot
    have hsmall (k : Fin (N+1)) : |A n (grid k) ω - a (grid k)| < ε/2 :=
      lt_of_not_ge (fun hk => hnot (mem_iUnion.mpr ⟨k,hk⟩))
    let k := Nat.floor (t/η)
    have hlo : (k:ℝ)*η ≤ t := (le_div_iff₀ hη).mp (Nat.floor_le (div_nonneg ht.1 hη.le))
    have hhi : t < ((k:ℝ)+1)*η := (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one (t/η))
    have hkN : k < N := by
      have hh : (k:ℝ) < N := (Nat.floor_le (div_nonneg ht.1 hη.le)).trans_lt
        ((div_le_div_of_nonneg_right ht.2 hη.le).trans_lt hN)
      exact_mod_cast hh
    let l : Fin (N+1) := ⟨k,by omega⟩
    let u : Fin (N+1) := ⟨k+1,by omega⟩
    have hgl : grid l = (k:ℝ)*η := min_eq_left (hlo.trans ht.2)
    have hgu : grid u = min (((k:ℝ)+1)*η) T := by simp [grid,u]
    have hlt : grid l ≤ t := by rw [hgl];exact hlo
    have htu : t ≤ grid u := by rw [hgu];exact le_min hhi.le ht.2
    have hdl : dist (grid l) t < δ := by
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hlt),hgl]
      dsimp [η] at hhi ⊢
      linarith
    have hdu : dist (grid u) t < δ := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr htu)]
      have hb : grid u ≤ ((k:ℝ)+1)*η := by rw [hgu];exact min_le_left _ _
      dsimp [η] at hlo hb
      linarith
    have hal := hcont (grid l) (hg l) t ht hdl
    have hau := hcont (grid u) (hg u) t ht hdu
    have hAl := hm n ω (hg l) ht hlt
    have hAu := hm n ω ht (hg u) htu
    have hsl := abs_lt.mp (hsmall l)
    have hsu := abs_lt.mp (hsmall u)
    rw [Real.dist_eq] at hal hau
    have hal' := abs_lt.mp hal
    have hau' := abs_lt.mp hau
    have hab : |A n t ω - a t| < ε := by
      apply abs_lt.mpr
      constructor <;> linarith
    exact (not_lt_of_ge he) hab
  have hsum : Tendsto (fun n => ∑ k : Fin (N+1), P (E n k)) atTop (𝓝 0) := by
    have hk (k : Fin (N+1)) := (tendstoInMeasure_iff_dist.mp (hp (grid k) (hg k)))
      (ε/2) (half_pos hε)
    simpa only [E,Real.dist_eq,Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun k _ => hk k)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  exact (measure_mono (hsub n)).trans (measure_iUnion_fintype_le P (E n))

/-- The preceding event estimate gives convergence of the actual supremum. -/
theorem monotone_sup_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (hT : 0 ≤ T)
    (A : ℕ → ℝ → Ω → ℝ) (a : ℝ → ℝ)
    (hm : ∀ n ω, MonotoneOn (fun t => A n t ω) (Icc 0 T))
    (ha : ContinuousOn a (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, TendstoInMeasure P (fun n => A n t) atTop (fun _ => a t)) :
    TendstoInMeasure P
      (fun n ω => sSup ((fun t => |A n t ω - a t|) '' Icc 0 T)) atTop (fun _ => 0) := by
  have hne : (Icc (0:ℝ) T).Nonempty := ⟨0,⟨le_rfl,hT⟩⟩
  obtain ⟨K,hK⟩ := isCompact_Icc.bddAbove_image ha.abs
  have hb n ω : BddAbove ((fun t => |A n t ω-a t|) '' Icc 0 T) := by
    refine ⟨|A n 0 ω|+|A n T ω|+K,?_⟩
    rintro _ ⟨t,ht,rfl⟩
    have hlo := hm n ω ⟨le_rfl,hT⟩ ht ht.1
    have hhi := hm n ω ht ⟨hT,le_rfl⟩ ht.2
    have haK := hK (mem_image_of_mem (fun t => |a t|) ht)
    have hAt : |A n t ω| ≤ |A n 0 ω|+|A n T ω| := by
      apply abs_le.mpr
      constructor <;> linarith [le_abs_self (A n 0 ω),neg_abs_le (A n 0 ω),
        le_abs_self (A n T ω),abs_nonneg (A n 0 ω),abs_nonneg (A n T ω)]
    exact (abs_sub _ _).trans (add_le_add hAt haK)
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hlim := monotone_uniform_probability P T hT A a hm ha hp (ε/2) (half_pos hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω he
  have hnonneg : 0 ≤ sSup ((fun t => |A n t ω-a t|) '' Icc 0 T) :=
    (abs_nonneg _).trans (le_csSup (hb n ω) (mem_image_of_mem _ ⟨le_rfl,hT⟩))
  simp only [mem_setOf_eq] at he ⊢
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg] at he
  by_contra hn
  have hs : sSup ((fun t => |A n t ω-a t|) '' Icc 0 T) ≤ ε/2 := by
    apply csSup_le (hne.image _)
    rintro _ ⟨t,ht,rfl⟩
    exact (lt_of_not_ge (fun hh => hn ⟨t,ht,hh⟩)).le
  linarith

#print axioms monotone_uniform_probability
#print axioms monotone_sup_probability
end Asakura.EndToEnd
