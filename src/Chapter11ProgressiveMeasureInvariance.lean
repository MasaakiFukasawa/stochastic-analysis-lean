import Chapter11LocalClockStepDensity
import Chapter11ItoDifferenceContinuity
import Chapter11ElementaryGains
import Chapter11ElementaryDecomposition
import Chapter11GainsProbabilityIdentification
import Chapter11SignedCumulativeBound
import Chapter11ProbabilityTransfer

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Measure invariance for an arbitrary progressive integrand, on a finite
 prefix. The common elementary approximants are constructed, rather than
 assumed. The signed measure is the actual variation part of the price. -/
theorem progressive_integral_measure_invariant_prefix
    {Ω : Type*} {m : MeasurableSpace Ω} (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnullP : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E=0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (Z : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness Q F Z)
    (hAQ : LocalCovarianceWitness Q F Z Z A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hH : ∀ d : ℝ,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (hi : ∀ n,∀ᵐ w ∂P,Integrable (fun r => H (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure)
    (I K : ClosedTime T → Ω → ℝ) (hI : LocalMProcessWitness P F I) (hK : LocalMProcessWitness Q F K)
    (hII : ItoCovarianceFormula P F X H I) (hKI : ItoCovarianceFormula Q F Z H K)
    (j : ℕ) (B : Ω → ℝ → ℝ)
    (hB : ∀ w,MonotoneOn (B w) (Icc 0 (c j)))
    (hBc : ∀ w,ContinuousOn (B w) (Icc 0 (c j)))
    (hBm : ∀ t,Measurable (fun w => B w t))
    (hBa : ∀ t : Icc (0:ℝ) (c j),Measurable[F (realTimeClamp t.val)] (fun w => B w t.val))
    (ν : Ω → SignedMeasure ℝ) :
    let β := fun w => (intervalStieltjes 0 (c j) (hc j).le (B w) (hB w) (fun r hr => (hBc w r hr).mono inter_subset_left)).measure
    (∀ᵐ w ∂P,(ν w).totalVariation≤β w) →
    (∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|) (β w)) →
    (∀ᵐ w ∂P,∀ a b,a∈Icc 0 (c j) → b∈Icc 0 (c j) → a≤b →
      ν w (Ioc a b)=(Z (realTimeClamp b) w-Z (realTimeClamp a) w)-
        (X (realTimeClamp b) w-X (realTimeClamp a) w)) →
    ∀ t,t∈Icc 0 (c j) →
      (fun w => I (realTimeClamp t) w+signedCumulative (ν w) (fun r => H (w,r)) t)=ᵐ[Q] K (realTimeClamp t) := by
  intro β hν hiB hinc
  classical
  letI : Fact (0≤c j) := ⟨(hc j).le⟩
  let α := fun n w => (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
    (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure
  have hAa (r : Icc (0:ℝ) (c j)) := hA.adapted P F hX hX (realTimeClamp r.val)
    (lt_of_le_of_lt (real_time_clamp_mono r.property.2) (hcut j))
  have hArm r (hr : r∈Icc 0 (c j)) : Measurable (fun w => A (realTimeClamp r) w) :=
    (hAa ⟨r,hr⟩).mono (hle _) le_rfl
  obtain ⟨N,u,V,hum,hub,hVm,hJm,hJp,hJiA,hJiB,hpA,hpB⟩ :=
    local_clock_step_density P (c j) (hc j) (fun w r => A (realTimeClamp r) w) B
      (hAm j) hB (hAc j) hBc hArm (fun r _ => hBm r) F hF hle hAa hBa hnullP H (hH (c j)) (hi j) hiB
  let J := fun n (z : Ω × ℝ) => ∑ i∈Finset.range (N n),(Ioc (u n i) (u n (i+1))).indicator (fun _ => V n i z.1) z.2
  have hab n i (hi : i∈Finset.range (N n)) : u n i≤u n (i+1) :=
    (hum n (by exact (Finset.mem_range.mp hi).le) (by exact Nat.succ_le_of_lt (Finset.mem_range.mp hi)) (Nat.lt_succ_self i)).le
  let Y := fun n t w => ∑ i∈Finset.range (N n),V n i w*(X (min (realTimeClamp (u n (i+1))) t) w-X (min (realTimeClamp (u n i)) t) w)
  let W := fun n t w => ∑ i∈Finset.range (N n),V n i w*(Z (min (realTimeClamp (u n (i+1))) t) w-Z (min (realTimeClamp (u n i)) t) w)
  have hy n := finite_elementary_gains P hT F hF hle hnullP X hX (Finset.range (N n)) (u n) (fun i => u n (i+1)) (V n)
    (fun i _ => (hub n i).1) (hab n) (fun i hi => (hVm n i (Finset.mem_range.mp hi)).1) (fun i hi => (hVm n i (Finset.mem_range.mp hi)).2)
  have hw n := finite_elementary_gains Q hT F hF hle hnullQ Z hZ (Finset.range (N n)) (u n) (fun i => u n (i+1)) (V n)
    (fun i _ => (hub n i).1) (hab n) (fun i hi => (hVm n i (Finset.mem_range.mp hi)).1)
    (fun i hi => bounded_coefficient_transfer P Q hQP (V n i) ((hVm n i (Finset.mem_range.mp hi)).1.mono (hle _) le_rfl) (hVm n i (Finset.mem_range.mp hi)).2)
  have hdiff k n : ∀ᵐ w ∂P,Integrable (fun r => (J k (w,r)-H (w,r))^2) (α n w) := by
    filter_upwards [hi n] with w hh
    letI : IsFiniteMeasure (α n w) := intervalStieltjes_finite _ _ _ _ _ _
    have hJ : MemLp (fun r => J k (w,r)) 2 (α n w) := memLp_finsetSum _ (fun i _ => (memLp_const (V k i w)).indicator measurableSet_Ioc)
    have hH' : MemLp (fun r => H (w,r)) 2 (α n w) := (memLp_two_iff_integrable_sq (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2 hh
    exact (memLp_two_iff_integrable_sq (hJ.sub hH').aestronglyMeasurable).1 (hJ.sub hH')
  have hpQ := nonnegative_probability_transfer P Q hQP
    (fun n w => ∫ r,(J n (w,r)-H (w,r))^2 ∂α j w)
    (fun n => random_stieltjes_integral_measurable_on (c j) (hc j).le _ (hAm j) (hAc j) hArm
      (fun z => (J n z-H z)^2) (((hJm n).sub hHm).pow_const 2))
    (fun n w => integral_nonneg (fun r => sq_nonneg _)) hpA
  have hp := ito_difference_probability_at_time P hT F hF hle hnullP X A hX hA c hc hcm hcT hct hcut hcc hAm hAc J H
    (fun k n => (hJp k (c n)).sub (hH (c n))) hdiff Y I (fun n => (hy n).1) hI (fun n => (hy n).2) hII
    j (c j) (hc j).le le_rfl (hAm j) (hAc j) hpA
  have hq := ito_difference_probability_at_time Q hT F hF hle hnullQ Z A hZ hAQ c hc hcm hcT hct hcut hcc hAm hAc J H
    (fun k n => (hJp k (c n)).sub (hH (c n))) (fun k n => hQP.ae_le (hdiff k n)) W K (fun n => (hw n).1) hK (fun n => (hw n).2) hKI
    j (c j) (hc j).le le_rfl (hAm j) (hAc j) hpQ
  have hjB n : ∀ᵐ w ∂P,Integrable (fun r => J n (w,r)) (β w) := by
    apply ae_of_all
    intro w
    letI : IsFiniteMeasure (β w) := intervalStieltjes_finite _ _ _ _ _ _
    change Integrable (fun r => ∑ i∈Finset.range (N n),(Ioc (u n i) (u n (i+1))).indicator (fun _ => V n i w) r) (β w)
    exact integrable_finsetSum _ (fun i _ => (integrable_const (V n i w)).indicator measurableSet_Ioc)
  intro t ht
  have hv := signed_cumulative_probability_limit P ν β hν (fun n w r => J n (w,r)) (fun w r => H (w,r)) hjB
    (hiB.mono (fun w hh => (integrable_norm_iff (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using hh))) hpB (fun _ => t)
  apply gains_probability_identification P Q hQP (fun n => Y n (realTimeClamp t))
    (fun n w => signedCumulative (ν w) (fun r => J n (w,r)) t) (fun n => W n (realTimeClamp t))
    (I (realTimeClamp t)) (fun w => signedCumulative (ν w) (fun r => H (w,r)) t) (K (realTimeClamp t))
    (fun n => (((hw n).1.adapted Q F _ (lt_of_le_of_lt (real_time_clamp_mono ht.2) (hcut j))).mono (hle _) le_rfl).aestronglyMeasurable) _
    (hp _ (real_time_clamp_mono ht.2)) hv (hq _ (real_time_clamp_mono ht.2))
  intro n
  filter_upwards [hν,hinc] with w hdom hinc
  letI : NullSingletonClass (β w) := interval_stieltjes_no_atoms_on 0 (c j) (hc j).le (B w) (hB w) _ (hBc w)
  letI : NullSingletonClass (ν w).totalVariation := ⟨fun r => le_antisymm ((hdom {r}).trans (le_of_eq (measure_singleton r))) bot_le⟩
  have hmem (i : ℕ) : min (u n i) t∈Icc 0 (c j) := ⟨le_min (hub n i).1 ht.1,(min_le_right _ _).trans ht.2⟩
  have he := elementary_gains_decomposition (ν w) (Finset.range (N n)) (u n) (fun i => u n (i+1)) (fun i => V n i w) (hab n) t
    (fun r => Z (realTimeClamp r) w-X (realTimeClamp r) w) (fun r => X (realTimeClamp r) w) (fun r => Z (realTimeClamp r) w)
    (fun i hi => by rw [hinc _ _ (hmem i) (hmem (i+1)) (min_le_min_right t (hab n i hi))];ring)
    (fun i _ => by ring)
  simpa only [Y,W,J,real_time_clamp_mono.map_min] using he

end Asakura.Chapter11
