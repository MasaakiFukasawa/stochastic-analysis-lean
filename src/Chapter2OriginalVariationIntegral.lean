import Chapter2LocalSignedIntegral
import Chapter2LocalVariationRealRegularity
import Chapter2LocalVariationContinuity
import Chapter2WeightedPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construction from the manuscript's original A_loc assumption. The
positive measure is characterized by increments of the actual path total
variation; integrability with respect to it alone suffices. -/
theorem original_local_variation_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A) :
    ∃ κ : ℕ → Ω → Measure ℝ,
      (∀ n ω, IsFiniteMeasure (κ n ω)) ∧
      (∀ n ω, ∀ᵐ r ∂κ n ω, r ∈ Ioc 0 (c n)) ∧
      (∀ n ω s t, s ≤ t → (κ n ω).real (Ioc s t) =
        pathVariation (fun r => A r ω) (realTimeClamp (intervalClamp 0 (c n) (hc n) t))-
        pathVariation (fun r => A r ω) (realTimeClamp (intervalClamp 0 (c n) (hc n) s))) ∧
      ((∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) →
        ∀ n ω, NullSingletonClass (κ n ω)) ∧
      ∀ H : Ω × ℝ → ℝ,
        (∀ n, @Measurable _ _
          (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
          (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val))) →
        (∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω)) →
        ∃ (ξ : ℕ → Ω → SignedMeasure ℝ) (I : ClosedTime T → Ω → ℝ),
          AdaptedLocalVariationWitness F I ∧
          (∀ n ω s t, s ≤ t → ξ n ω (Ioc s t) =
            A (realTimeClamp (intervalClamp 0 (c n) (hc n) t)) ω-
            A (realTimeClamp (intervalClamp 0 (c n) (hc n) s)) ω) ∧
          (∀ n ω, (ξ n ω).totalVariation ≤ κ n ω) ∧
          (∀ᵐ ω ∂P, ∀ n t, I (min (realTimeClamp (c n)) t) ω =
            signedCumulative (ξ n ω) (fun r => H (ω,r)) (finitePrefixTime (c n) (hc n) t).val) := by
  let V := fun t ω => pathVariation (fun s => A s ω) t
  let U := fun t ω => (V t ω+A t ω)/2
  let W := fun t ω => (V t ω-A t ω)/2
  obtain ⟨hU,hW,hmon⟩ := local_variation_jordan_regular F hF A hA
  have hUm n := finite_real_monotone_of_local U (fun ω => (hmon ω).1) (c n) (hc n) (hcT n)
  have hWm n := finite_real_monotone_of_local W (fun ω => (hmon ω).2) (c n) (hc n) (hcT n)
  have hUr n := (hU.real_interval_regular (c n) (hc n) (hcT n)).1
  have hWr n := (hW.real_interval_regular (c n) (hc n) (hcT n)).1
  have hUa n := (hU.real_interval_regular (c n) (hc n) (hcT n)).2
  have hWa n := (hW.real_interval_regular (c n) (hc n) (hcT n)).2
  let Ur := fun ω r => U (realTimeClamp r) ω
  let Wr := fun ω r => W (realTimeClamp r) ω
  let α := fun n ω => (intervalStieltjes 0 (c n) (hc n) (Ur ω) (hUm n ω) (hUr n ω)).measure
  let β := fun n ω => (intervalStieltjes 0 (c n) (hc n) (Wr ω) (hWm n ω) (hWr n ω)).measure
  letI : ∀ n ω, IsFiniteMeasure (α n ω) := fun n ω => intervalStieltjes_finite _ _ _ _ _ _
  letI : ∀ n ω, IsFiniteMeasure (β n ω) := fun n ω => intervalStieltjes_finite _ _ _ _ _ _
  let κ := fun n ω => α n ω+β n ω
  refine ⟨κ,fun _ _ => inferInstance,?_,?_,?_,?_⟩
  · intro n ω
    exact ae_add_measure_iff.mpr
      ⟨interval_stieltjes_ae_mem_Ioc 0 (c n) (hc n) (Ur ω) (hUm n ω) (hUr n ω),
       interval_stieltjes_ae_mem_Ioc 0 (c n) (hc n) (Wr ω) (hWm n ω) (hWr n ω)⟩
  · intro n ω s t hst
    change (α n ω+β n ω).real (Ioc s t) = _
    rw [Measure.real,Measure.add_apply,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    change (α n ω).real (Ioc s t)+(β n ω).real (Ioc s t) = _
    rw [intervalStieltjes_Ioc_real 0 (c n) (hc n) (Ur ω) (hUm n ω) (hUr n ω) s t hst,
      intervalStieltjes_Ioc_real 0 (c n) (hc n) (Wr ω) (hWm n ω) (hWr n ω) s t hst]
    dsimp only [Ur,Wr,U,W,V]
    ring
  · intro hcont n ω
    have hVc := local_path_variation_continuous hA hcont
    have hUc ω t ht : ContinuousAt (fun s => U s ω) t :=
      ((hVc ω t ht).add (hcont ω t ht)).div_const 2
    have hWc ω t ht : ContinuousAt (fun s => W s ω) t :=
      ((hVc ω t ht).sub (hcont ω t ht)).div_const 2
    have hbelow r (hr : r ∈ Icc 0 (c n)) : realTimeClamp (T := T) r < ⊤ := by
      change (realTimeClamp r : EReal) < T
      rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
      exact (EReal.coe_le_coe hr.2).trans_lt (hcT n)
    have hUrc : ContinuousOn (Ur ω) (Icc 0 (c n)) := fun r hr =>
      ((hUc ω _ (hbelow r hr)).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
    have hWrc : ContinuousOn (Wr ω) (Icc 0 (c n)) := fun r hr =>
      ((hWc ω _ (hbelow r hr)).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
    letI : NullSingletonClass (α n ω) := interval_stieltjes_no_atoms_on 0 (c n) (hc n)
      (Ur ω) (hUm n ω) (hUr n ω) hUrc
    letI : NullSingletonClass (β n ω) := interval_stieltjes_no_atoms_on 0 (c n) (hc n)
      (Wr ω) (hWm n ω) (hWr n ω) hWrc
    refine ⟨fun r => ?_⟩
    change (α n ω+β n ω) {r} = 0
    rw [Measure.add_apply,measure_singleton,measure_singleton,add_zero]
  · intro H hH hi
    obtain ⟨ξ,I,hI,hξ,hdom,he⟩ := local_signed_stieltjes_integral_constructed P F hF hnull
      c hc hcm hcT hcc Ur Wr hUm hWm hUr hWr hUa hWa H hH hi
    refine ⟨ξ,I,hI,?_,hdom,he⟩
    intro n ω s t hst
    rw [hξ n ω s t hst]
    dsimp only [Ur,Wr,U,W]
    ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.original_local_variation_integral_constructed
