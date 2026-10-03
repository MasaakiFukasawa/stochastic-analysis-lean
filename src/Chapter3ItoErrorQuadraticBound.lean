import Chapter3BoundedDiscreteIntegralIdentification
import Chapter3ItoAllTimeEnergy
import Chapter3ContinuousCommonBounds
import Chapter3PartitionStepEnergy
import Chapter3LocalEnergyMaximal
import Chapter2ItoCharacterizedEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The actual Karandikar error has quadratic variation bounded by the
squared partition oscillation times the actual quadratic variation of X.
This bound is simultaneous at every finite time.
The actual Karandikar sums converge almost surely uniformly on a finite
prefix. Only the initial value H(0) is bounded; subsequent coefficients
are controlled by the partition oscillations. This reduction combines the discrete integral identity,
Ito energy formula, Stieltjes error estimate, Doob and dyadic summability. -/
theorem ito_discrete_error_quadratic_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A H Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (K : ℝ) (hK : ∀ᵐ ω ∂P, |H ⊥ ω| ≤ K)
    (c : ℕ → ℝ) (hc : ∀ j, 0 < c j) (hcm : StrictMono c) (hcT : ∀ j, (c j:EReal) < T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j, realTimeClamp (T := T) (c j) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ j, t < realTimeClamp (T := T) (c j))
    (hAm : ∀ j ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c j)))
    (hAc : ∀ j ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c j)))
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτt : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (hosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n)
    :
    let E := fun n t ω => Y t ω-
      ∑' j, H (τ n j ω) ω*(X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω)
    (∀ n, LocalMProcessWitness P F (E n)) ∧
      ∃ B : ℕ → ClosedTime T → Ω → ℝ,
        (∀ n, LocalCovarianceWitness P F (E n) (E n) (B n)) ∧
        (∀ n, ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
          0 ≤ B n t ω ∧ B n t ω ≤ ((1/2:ℝ)^n)^2*A t ω) := by
  intro E
  let R := fun n t ω => ∑' j, H (τ n j ω) ω*
    (X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω)
  let G := fun n (z : Ω × ℝ) => H (realTimeClamp z.2) z.1-
    partitionStep (fun t => H t z.1) (fun j => τ n j z.1) (realTimeClamp z.2)
  have hcoeff (n j) :
      Measurable[writtenStoppedSpace m F (τ n j) (hτ n j)] (fun ω => H (τ n j ω) ω) ∧
      MemLp (fun ω => H (τ n j ω) ω) ∞ P := by
    obtain ⟨hm,hcont⟩ := open_continuous_adapted_stopped_regular F hF H hHm hHc
      (fun j => realTimeClamp (c j)) hct.monotone hcut hcc (τ n j) (hτ n j) (hτt n j)
    have ha := stopped_value_measurable_right_continuous m (show (0:EReal) ≤ T from Fact.out)
      F hF hle (τ n j) (hτ n j) (fun t ω => H (min (τ n j ω) t) ω) hm
      (fun ω t => (hcont ω).continuousAt.continuousWithinAt)
    have ha' : Measurable[writtenStoppedSpace m F (τ n j) (hτ n j)]
        (fun ω => H (τ n j ω) ω) := by simpa only [min_self] using ha
    refine ⟨ha',?_⟩
    apply memLp_top_of_bound (ha'.mono (fun E hE => hE.1) le_rfl).aestronglyMeasurable
      (K+(j:ℝ)*(1/2:ℝ)^n)
    filter_upwards [hK,hosc] with ω hKω hoscω
    have hb (i : ℕ) : |H (τ n i ω) ω| ≤ K+(i:ℝ)*(1/2:ℝ)^n := by
      induction i with
      | zero => simpa only [hτ0,Nat.cast_zero,zero_mul,add_zero] using hKω
      | succ i ih =>
        have ho := hoscω n i (τ n (i+1) ω) (hτm n ω (Nat.le_succ i)) le_rfl
        have ht := abs_le.mp ho
        have hi := abs_le.mp ih
        rw [Nat.cast_succ]
        apply abs_le.mpr
        constructor <;> linarith
    simpa only [Real.norm_eq_abs] using hb j
  have hR (n) : LocalMProcessWitness P F (R n) := discrete_integral_local_martingale P F hF hle
    X hX (τ n) (hτ n) (hτm n) (hτt n) (hτc n) (fun j ω => H (τ n j ω) ω)
    (fun j => (hcoeff n j).1) (fun j => (hcoeff n j).2)
  have hRI (n) := discrete_integral_ito_formula P F hF hle hnull X H hX
    (fun j => realTimeClamp (c j)) hct.monotone hcut hcc (τ n) (hτ n) (hτm n)
    (hτt n) (hτc n) (fun j => (hcoeff n j).1) (fun j => (hcoeff n j).2)
  have hEL (n) : LocalMProcessWitness P F (E n) := by
    convert ((hR n).smul P F (-1)).add P F hF hle hY using 1
    funext t ω
    change Y t ω-R n t ω = -1*R n t ω+Y t ω
    ring
  have hEI (n) : ItoCovarianceFormula P F X (G n) (E n) := by
    convert (hRI n).add_smul P F hF hle X _ Y _ _ hYI (-1) using 1
    · funext z
      dsimp only [G]
      ring
    · funext t ω
      change Y t ω-R n t ω = -1*R n t ω+Y t ω
      ring
  have hGp (n j) : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c j) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c j) => G n (z.1,z.2.val)) := by
    have hHp := continuous_adapted_real_progressive F hF (fun z : Ω × ℝ => H (realTimeClamp z.2) z.1)
      (c j) (hc j).le (fun r hr => hHm _ ((real_time_clamp_mono hr.2).trans_lt (hcut j)))
      (fun ω r hr => ((hHc ω _ ((real_time_clamp_mono hr.2).trans_lt (hcut j))).comp
        real_time_clamp_continuous.continuousAt).continuousWithinAt)
    have hSp := partition_step_prefix_progressive F hF H hHm hHc
      (fun j => realTimeClamp (c j)) hct.monotone hcut hcc (τ n) (hτ n) (hτt n) (c j) (hc j).le
    exact hHp.sub hSp
  have henergy (n j) : ∀ᵐ ω ∂P,
      Integrable (fun r => G n (ω,r)^2)
        (intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
          (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure ∧
      (∫ r, G n (ω,r)^2 ∂(intervalStieltjes 0 (c j) (hc j).le
        (fun r => A (realTimeClamp r) ω) (hAm j ω)
          (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure) ≤
        ((1/2:ℝ)^n)^2*A (realTimeClamp (c j)) ω := by
    filter_upwards [hosc] with ω hω
    have h := partition_step_stieltjes_error_energy (c j) (hc j).le (hcT j) (fun t => H t ω) (hHc ω)
      (fun r => A (realTimeClamp r) ω) (hAm j ω) (fun r hr => (hAc j ω r hr).mono inter_subset_left)
      (fun i => τ n i ω) (hτm n ω) (hτ0 n ω) (hτc n ω)
      ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hω n)
    have hz : realTimeClamp (T := T) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
    simpa only [G,hz,hA0 ω,sub_zero] using h
  have hb (n) := ito_covariance_formula_all_time_energy P hT F hF hle hnull X A hX hA c hc hcm hcT
    hct hcut hcc hAm hAc (G n) (hGp n) (fun j => (henergy n j).mono (fun _ h => h.1))
    (E n) (hEL n) (hEI n)
  choose B hB hBe using hb
  refine ⟨hEL,B,hB,?_⟩
  intro n
  have hpoint (t : ClosedTime T) (ht : t < ⊤) : ∀ᵐ ω ∂P,
      0 ≤ B n t ω ∧ B n t ω ≤ ((1/2:ℝ)^n)^2*A t ω := by
    obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
    obtain ⟨j,hj⟩ := hcc (realTimeClamp d) ht
    have hdj : d ≤ c j := by
      change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
      rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
      exact (EReal.coe_lt_coe_iff.mp hj).le
    obtain ⟨hmA,hcontA,he⟩ := hBe n j d hd hdj
    filter_upwards [he,hosc] with ω heω hoω
    have h := partition_step_stieltjes_error_energy d hd hdT (fun t => H t ω) (hHc ω)
      (fun r => A (realTimeClamp r) ω) (hmA ω) (fun r hr => (hcontA ω r hr).mono inter_subset_left)
      (fun i => τ n i ω) (hτm n ω) (hτ0 n ω) (hτc n ω)
      ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hoω n)
    have hz : realTimeClamp (T := T) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
    rw [heω]
    refine ⟨integral_nonneg (fun r => sq_nonneg _),?_⟩
    simpa only [G,hz,hA0 ω,sub_zero] using h.2
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have hcommon := continuous_process_common_bounds P
    (fun t : Iio (⊤ : ClosedTime T) => B n t.val)
    (fun t : Iio (⊤ : ClosedTime T) => fun ω => ((1/2:ℝ)^n)^2*A t.val ω)
    ((hB n).continuous_open_paths P F (E n) (E n) (B n) (hEL n) (hEL n))
    (fun ω => continuous_const.mul (hA.continuous_open_paths P F X X A hX hX ω))
    (fun t => hpoint t.val t.property)
  exact hcommon.mono (fun ω hω t ht => hω ⟨t,ht⟩)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_discrete_error_quadratic_bound
