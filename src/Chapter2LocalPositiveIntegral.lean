import Chapter2FiniteVariationIntegralMember
import Chapter2LocalIntegrableRepresentative

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem finite_prefix_time_stop
    {T : EReal} [Fact (0 ≤ T)] (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (haT : (a:EReal) ≤ T) (t : ClosedTime T) :
    (finitePrefixTime b (ha.trans hab) (min (realTimeClamp a) t)).val =
      (finitePrefixTime a ha t).val := by
  change (min (min (realTimeClamp a : EReal) (t:EReal)) (b:EReal)).toReal =
    (min (t:EReal) (a:EReal)).toReal
  rw [real_time_clamp_eq a ha haT]
  congr 1
  calc
    min (min (a:EReal) (t:EReal)) (b:EReal) = min (t:EReal) (min (a:EReal) (b:EReal)) := by ac_rfl
    _ = min (t:EReal) (a:EReal) := by rw [min_eq_left (EReal.coe_le_coe hab)]

/-- Local positive Stieltjes integration on the original time space.
The common null set is removed before forming finite-interval Jordan parts;
the compatible pieces are then glued in the actual space A_loc. -/
theorem local_positive_stieltjes_integral_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (c n)))
    (hr : ∀ n ω r, r ∈ Icc 0 (c n) → ContinuousWithinAt (A ω) (Icc 0 (c n) ∩ Ici r) r)
    (hm : ∀ n (r : Icc (0:ℝ) (c n)), Measurable[F (realTimeClamp r.val)] (fun ω => A ω r.val))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r))
      (intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω) (hr n ω)).measure) :
    ∃ I : ClosedTime T → Ω → ℝ, AdaptedLocalVariationWitness F I ∧
      (∀ᵐ ω ∂P, ∀ n t, I (min (realTimeClamp (c n)) t) ω =
        ∫ r in Iic (finitePrefixTime (c n) (hc n) t).val,
          H (ω,r) ∂(intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω) (hr n ω)).measure) := by
  let κ := fun n ω => (intervalStieltjes 0 (c n) (hc n) (A ω) (hA n ω) (hr n ω)).measure
  obtain ⟨J,hJ,hJi,hJH⟩ := local_integrable_progressive_representative P F hnull c κ H hH hi
  let I := fun n (t : ClosedTime T) ω => ∫ r in Iic (finitePrefixTime (c n) (hc n) t).val,
    J (ω,r) ∂κ n ω
  have hI n : AdaptedVariationWitness F (I n) := finite_stieltjes_integral_member F hF
    (c n) (hc n) (hcT n).le A (hA n) (hr n) (hm n) J (hJ n) (hJi n)
  have hcompat : ∀ᵐ ω ∂P, ∀ n k, n ≤ k → ∀ t,
      I k (min (realTimeClamp (c n)) t) ω = I n t ω := by
    apply ae_of_all
    intro ω n k hnk t
    have heκ : κ n ω = (κ k ω).restrict (Iic (c n)) :=
      interval_stieltjes_restrict_Iic 0 (c k) (c n) (hc n) (hcm hnk) (A ω)
        (hA k ω) (hr k ω) (hA n ω) (hr n ω)
    dsimp only [I]
    rw [finite_prefix_time_stop (c n) (c k) (hc n) (hcm hnk) (hcT n).le]
    rw [heκ,Measure.restrict_restrict measurableSet_Iic]
    have heSet : Iic (finitePrefixTime (c n) (hc n) t).val ∩ Iic (c n) =
        Iic (finitePrefixTime (c n) (hc n) t).val :=
      inter_eq_left.mpr (Iic_subset_Iic.mpr (finitePrefixTime (c n) (hc n) t).property.2)
    rw [heSet]
  have hstop n t : MeasurableSet[F t] {ω : Ω | realTimeClamp (T := T) (c n) ≤ t} := by
    by_cases ht : realTimeClamp (T := T) (c n) ≤ t <;> simp [ht]
  have htop n (_ : Ω) : realTimeClamp (T := T) (c n) < ⊤ := by
    change (realTimeClamp (c n) : EReal) < T
    rw [real_time_clamp_eq (c n) (hc n) (hcT n).le]
    exact hcT n
  obtain ⟨G,hG,_,_,heG⟩ := adapted_right_continuous_variation_gluing P F hnull
    (fun n _ => realTimeClamp (c n)) hstop (fun _ => real_time_clamp_mono.comp hcm)
    htop (fun _ => hcc) I hI hcompat
  refine ⟨G,hG,?_⟩
  filter_upwards [heG,hJH] with ω hGω hHω
  intro n t
  rw [hGω n t]
  exact integral_congr_ae (.of_forall hHω)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_positive_stieltjes_integral_constructed
