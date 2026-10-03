import Chapter4C12Coordinates
import Chapter4TimeSpacePartition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The C1,2 formula follows from the actual first-order partition sums,
spatial covariation sums, and the separate time/space Taylor estimate. -/
theorem c12_time_space_path_limit
    {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (U : ClosedTime T → ℝ) (X : ClosedTime T → (Fin dim → ℝ))
    (f : ℝ → (Fin dim → ℝ) → ℝ) (ft : ℝ × (Fin dim → ℝ) → ℝ)
    (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hft : ∀ a x,HasDerivAt (fun s => f s x) (ft (a,x)) a) (hftc : Continuous ft)
    (hhc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (τ : ℕ → ℕ → ClosedTime T) (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=⊥)
    (hco : ∀ n t,t<⊤ → ∃ N,t<τ n N)
    (t : ClosedTime T) (ht : t<⊤) (R : ℝ)
    (hUm : Monotone U) (hUb : ∀ s,s≤t → U s∈Icc 0 R)
    (hXb : ∀ s,s≤t → X s∈Metric.closedBall 0 R)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hUstep : ∀ n j,U (min (τ n (j+1)) t)-U (min (τ n j) t)≤η n)
    (hXstep : ∀ n j,‖X (min (τ n (j+1)) t)-X (min (τ n j) t)‖≤η n)
    (Z0 : ℝ) (Z : Fin dim → ℝ) (J : Fin dim → Fin dim → ℝ) (Q : Fin dim → ℝ)
    (hZ0 : Tendsto (fun n => partitionLinear U (fun s => ft (U s,X s)) (τ n) t) atTop (𝓝 Z0))
    (hZ : ∀ i,Tendsto (fun n => partitionLinear (fun s => X s i)
      (fun s => fderiv ℝ (f (U s)) (X s) (Pi.single i 1)) (τ n) t) atTop (𝓝 (Z i)))
    (hJ : ∀ i j,Tendsto (fun n => partitionCross (fun s => X s i) (fun s => X s j)
      (fun s => fderiv ℝ (fderiv ℝ (f (U s))) (X s) (Pi.single i 1) (Pi.single j 1)) (τ n) t)
      atTop (𝓝 (J i j)))
    (hQ : ∀ i,Tendsto (fun n => partitionCross (fun s => X s i) (fun s => X s i)
      (fun _ => 1) (τ n) t) atTop (𝓝 (Q i))) :
    f (U t) (X t)=f (U ⊥) (X ⊥)+Z0+(∑ i,Z i)+(∑ i,∑ j,J i j)/2 := by
  have hu := tendsto_finsetSum Finset.univ (fun i _ => hZ i)
  have hv := tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun j _ => hJ i j))
  have hq := tendsto_finsetSum Finset.univ (fun i _ => hQ i)
  have hr := ((((tendsto_const_nhds (x := f (U t) (X t)-f (U ⊥) (X ⊥))).sub hZ0).sub hu).sub (hv.div_const 2)).abs
  have hb ε (hε : 0<ε) :
      |f (U t) (X t)-f (U ⊥) (X ⊥)-Z0-(∑ i,Z i)-(∑ i,∑ j,J i j)/2|≤
        ε*(U t-U ⊥)+(ε/2)*∑ i,Q i := by
    obtain ⟨δ,hδ,hTaylor⟩ := c12_uniform_coordinate_taylor f ft hf hft hftc hhc R ε hε
    have hn : ∀ᶠ n in atTop,η n≤δ := (hη.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
    have he := hn.mono (fun n hn => by
      obtain ⟨N,hN⟩ := hco n t ht
      apply time_space_partition_taylor_bound U X f (fun a x => ft (a,x))
        (fun i a x => fderiv ℝ (f a) x (Pi.single i 1))
        (fun i j a x => fderiv ℝ (fderiv ℝ (f a)) x (Pi.single i 1) (Pi.single j 1))
        (τ n) (hm n) (h0 n) t N hN.le ε
      intro j hj
      have hst : τ n j≤min (τ n (j+1)) t := le_min ((hm n) (Nat.le_succ j)) hj
      apply hTaylor _ (hUb _ hj) _ (hUb _ (min_le_right _ _)) (hUm hst)
        _ (hXb _ hj) _ (hXb _ (min_le_right _ _))
      · simpa only [min_eq_left hj] using (hUstep n j).trans hn
      · simpa only [min_eq_left hj] using (hXstep n j).trans hn)
    exact le_of_tendsto_of_tendsto hr ((tendsto_const_nhds (x := ε*(U t-U ⊥))).add (hq.const_mul (ε/2))) he
  have hz : Tendsto (fun n : ℕ => (1/2:ℝ)^n*((U t-U ⊥)+(∑ i,Q i)/2)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const ((U t-U ⊥)+(∑ i,Q i)/2)
  have hzero : |f (U t) (X t)-f (U ⊥) (X ⊥)-Z0-(∑ i,Z i)-(∑ i,∑ j,J i j)/2|≤0 := by
    apply ge_of_tendsto hz
    apply Filter.Eventually.of_forall
    intro n
    convert hb ((1/2:ℝ)^n) (pow_pos (by norm_num) n) using 1 <;> ring
  have he := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  linarith

end Asakura.Chapter4
