import Chapter1WrittenStopping
import Mathlib.MeasureTheory.Function.Floor

/- prop:st3: positive/negative parts, the actual truncated floor approximations,
then nonzero level sets of simple functions. -/
open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter1Written

/-- For x≥0 and n>0 this is min(n, floor(nx)/n), as in the manuscript. -/
noncomputable def stoppedApprox (n : ℕ) (x : ℝ) : ℝ :=
  (min (n*n) (Nat.floor ((n : ℝ)*x)) : ℕ) / (n : ℝ)

theorem stopped_approx_formula (n : ℕ) (x : ℝ) :
    stoppedApprox n x = min (n : ℝ) ((Nat.floor ((n : ℝ)*x) : ℝ)/(n : ℝ)) := by
  by_cases hn : n = 0
  · simp [hn, stoppedApprox]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [stoppedApprox, Nat.cast_min, Nat.cast_mul]
    rw [← min_div_div_right (Nat.cast_nonneg n), mul_div_cancel_right₀ _ hn']

theorem stopped_approx_zero (n : ℕ) : stoppedApprox n 0 = 0 := by simp [stoppedApprox]

theorem stopped_approx_measurable (n : ℕ) : Measurable (stoppedApprox n) := by
  have h : Measurable (fun x : ℝ => min (n*n) (Nat.floor ((n : ℝ)*x))) :=
    measurable_const.min ((measurable_const.mul measurable_id).nat_floor)
  have hc : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  exact (hc.comp h).div_const _

theorem stopped_approx_finite (n : ℕ) : (range (stoppedApprox n)).Finite := by
  apply ((finite_Iic (n*n)).image (fun k : ℕ => (k : ℝ)/(n : ℝ))).subset
  rintro y ⟨x, rfl⟩
  exact ⟨min (n*n) (Nat.floor ((n : ℝ)*x)), (show min (n*n) (Nat.floor ((n : ℝ)*x)) ≤ n*n from min_le_left _ _), rfl⟩

theorem stopped_approx_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => stoppedApprox n x) atTop (𝓝 x) := by
  have ht := (tendsto_nat_floor_mul_div_atTop hx).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply ht.congr'
  have hn : ∀ᶠ n : ℕ in atTop, x ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop x)
  filter_upwards [hn] with n hn
  have hfloor : Nat.floor ((n : ℝ)*x) ≤ n*n := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg n)
  change (Nat.floor (x*(n : ℝ)) : ℝ)/(n : ℝ) = stoppedApprox n x
  unfold stoppedApprox
  rw [min_eq_right hfloor, mul_comm]

/-- A finite-valued function is measurable once its nonzero level sets are.
The missing zero level is the complement of their finite union. -/
theorem finite_range_measurable_nonzero {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (hfin : (range X).Finite)
    (hlevels : ∀ a : ℝ, a ≠ 0 → MeasurableSet {ω | X ω = a}) : Measurable X := by
  classical
  let f : SimpleFunc Ω ℝ :=
    { toFun := X
      finite_range' := hfin
      measurableSet_fiber' := by
        intro a
        by_cases ha : a = 0
        · subst a
          have he : X ⁻¹' {0} = (⋃ a ∈ (range X \ {0}), {ω | X ω = a})ᶜ := by
            ext ω
            simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, Set.mem_sdiff,
              mem_range, mem_ofPred_eq]
            aesop
          rw [he]
          apply MeasurableSet.compl
          apply MeasurableSet.biUnion (hfin.sdiff).countable
          intro a ha
          exact hlevels a ha.2
        · exact hlevels a ha }
  exact f.measurable

/-- The finite-valued part of prop:st3, proved with the printed nonzero fibers. -/
theorem finite_stopped_measurable_iff {Ω ι : Type*} (m : MeasurableSpace Ω) [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i}) (X : Ω → ℝ)
    (hmX : Measurable[m] X) (hfin : (range X).Finite) :
    Measurable[writtenStoppedSpace m F τ hτ] X ↔
      ∀ i, Measurable[F i] ({ω | τ ω ≤ i}.indicator X) := by
  classical
  constructor
  · intro hX i
    letI : MeasurableSpace Ω := F i
    apply finite_range_measurable_nonzero
    · exact (hfin.insert 0).subset (by
        rintro y ⟨ω, rfl⟩
        by_cases h : τ ω ≤ i <;> simp [Set.indicator, h, mem_range_self])
    · intro a ha
      rw [indicator_nonzero_level X _ a ha]
      exact (hX (measurableSet_singleton a)).2 i
  · intro h
    letI : MeasurableSpace Ω := writtenStoppedSpace m F τ hτ
    apply finite_range_measurable_nonzero X hfin
    intro a ha
    refine ⟨hmX (measurableSet_singleton a), fun i => ?_⟩
    rw [← indicator_nonzero_level X _ a ha]
    exact h i (measurableSet_singleton a)

/-- Truncated floor approximation reduces the nonnegative case to the finite case. -/
theorem nonnegative_stopped_measurable_iff {Ω ι : Type*} (m : MeasurableSpace Ω) [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i}) (X : Ω → ℝ)
    (hmX : Measurable[m] X) (hpos : ∀ ω, 0 ≤ X ω) :
    Measurable[writtenStoppedSpace m F τ hτ] X ↔
      ∀ i, Measurable[F i] ({ω | τ ω ≤ i}.indicator X) := by
  classical
  let Xn := fun n ω => stoppedApprox n (X ω)
  have hmn (n : ℕ) : Measurable[m] (Xn n) := (stopped_approx_measurable n).comp hmX
  have hfn (n : ℕ) : (range (Xn n)).Finite :=
    (stopped_approx_finite n).subset (by rintro y ⟨ω, rfl⟩; exact ⟨X ω, rfl⟩)
  have hcomm (n : ℕ) (i : ι) : {ω | τ ω ≤ i}.indicator (Xn n) =
      fun ω => stoppedApprox n ({ω | τ ω ≤ i}.indicator X ω) := by
    funext ω
    by_cases h : τ ω ≤ i <;> simp [Set.indicator, h, Xn, stopped_approx_zero]
  have ht (ω : Ω) : Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω)) := stopped_approx_tendsto _ (hpos ω)
  constructor
  · intro hX i
    have hn (n : ℕ) : Measurable[F i] ({ω | τ ω ≤ i}.indicator (Xn n)) :=
      (finite_stopped_measurable_iff m F τ hτ (Xn n) (hmn n) (hfn n)).mp
        ((stopped_approx_measurable n).comp hX) i
    letI : MeasurableSpace Ω := F i
    apply measurable_of_tendsto_metrizable hn
    apply tendsto_pi_nhds.mpr
    intro ω
    by_cases h : τ ω ≤ i
    · simpa [Set.indicator, h] using ht ω
    · simp [Set.indicator, h]
  · intro h
    have hn (n : ℕ) : Measurable[writtenStoppedSpace m F τ hτ] (Xn n) := by
      apply (finite_stopped_measurable_iff m F τ hτ (Xn n) (hmn n) (hfn n)).mpr
      intro i
      rw [hcomm]
      exact (stopped_approx_measurable n).comp (h i)
    letI : MeasurableSpace Ω := writtenStoppedSpace m F τ hτ
    exact measurable_of_tendsto_metrizable hn (tendsto_pi_nhds.mpr ht)

/-- Full prop:st3, reducing a real function to its positive and negative parts. -/
theorem stopped_measurable_iff_written {Ω ι : Type*} (m : MeasurableSpace Ω) [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (τ : Ω → ι)
    (hτ : ∀ i, MeasurableSet[F i] {ω | τ ω ≤ i}) (X : Ω → ℝ) (hmX : Measurable[m] X) :
    Measurable[writtenStoppedSpace m F τ hτ] X ↔
      ∀ i, Measurable[F i] ({ω | τ ω ≤ i}.indicator X) := by
  classical
  let Xp := fun ω => max (X ω) 0
  let Xm := fun ω => max (-X ω) 0
  have hp : Measurable[m] Xp := hmX.max measurable_const
  have hm : Measurable[m] Xm := hmX.neg.max measurable_const
  have he : X = Xp-Xm := by
    funext ω
    dsimp [Xp, Xm]
    by_cases h : 0 ≤ X ω <;> simp [max_eq_left, max_eq_right, h, le_of_not_ge, neg_nonpos, neg_nonneg] <;> linarith
  have hep (i : ι) : {ω | τ ω ≤ i}.indicator Xp = fun ω => max ({ω | τ ω ≤ i}.indicator X ω) 0 := by
    funext ω; by_cases h : τ ω ≤ i <;> simp [Set.indicator, h, Xp]
  have hem (i : ι) : {ω | τ ω ≤ i}.indicator Xm = fun ω => max (-({ω | τ ω ≤ i}.indicator X ω)) 0 := by
    funext ω; by_cases h : τ ω ≤ i <;> simp [Set.indicator, h, Xm]
  have hpiff := nonnegative_stopped_measurable_iff m F τ hτ Xp hp (fun ω => le_max_right _ _)
  have hmiff := nonnegative_stopped_measurable_iff m F τ hτ Xm hm (fun ω => le_max_right _ _)
  constructor
  · intro hX i
    have h1 := hpiff.mp (hX.max measurable_const) i
    have h2 := hmiff.mp (hX.neg.max measurable_const) i
    rw [he]
    change Measurable[F i] ({ω | τ ω ≤ i}.indicator (fun ω => Xp ω - Xm ω))
    rw [Set.indicator_sub]
    exact h1.sub h2
  · intro h
    have h1 : Measurable[writtenStoppedSpace m F τ hτ] Xp := hpiff.mpr (fun i => by
      rw [hep]; exact (h i).max measurable_const)
    have h2 : Measurable[writtenStoppedSpace m F τ hτ] Xm := hmiff.mpr (fun i => by
      rw [hem]; exact (h i).neg.max measurable_const)
    rw [he]
    exact h1.sub h2

end Asakura.Chapter1Written
