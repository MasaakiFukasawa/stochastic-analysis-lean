import Chapter2LocalFatou

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The tail infima used in the manuscript's conditional Fatou argument. -/
theorem real_tail_infimum_properties (f : ℕ → ℝ) (a v : ℝ)
    (hb : ∀ n, a ≤ f n) (hf : Tendsto f atTop (𝓝 v)) :
    (∀ n, a ≤ ⨅ k, f (n+k)) ∧
    (∀ n k, (⨅ j, f (n+j)) ≤ f (n+k)) ∧
    Monotone (fun n => ⨅ k, f (n+k)) ∧
    Tendsto (fun n => ⨅ k, f (n+k)) atTop (𝓝 v) := by
  have hbd (n) : BddBelow (range (fun k => f (n+k))) := ⟨a,by rintro _ ⟨k,rfl⟩; exact hb _⟩
  have hlo (n) : a ≤ ⨅ k, f (n+k) := le_ciInf (fun k => hb _)
  have hup (n k) : (⨅ j, f (n+j)) ≤ f (n+k) := ciInf_le (hbd n) k
  refine ⟨hlo,hup,?_,?_⟩
  · intro n m hnm
    apply le_ciInf
    intro k
    have h := hup n (m-n+k)
    simpa only [← Nat.add_assoc,Nat.add_sub_of_le hnm] using h
  · apply tendsto_order.2
    constructor
    · intro b hb
      obtain ⟨c,hbc,hcv⟩ := exists_between hb
      obtain ⟨K,hK⟩ := eventually_atTop.1 (hf.eventually (lt_mem_nhds hcv))
      exact eventually_atTop.2 ⟨K,fun m hm => hbc.trans_le
        (le_ciInf fun k => (hK _ (hm.trans (Nat.le_add_right _ _))).le)⟩
    · intro b hb
      filter_upwards [hf.eventually (gt_mem_nhds hb)] with n hn
      exact (by simpa using hup n 0 : (⨅ k, f (n+k)) ≤ f n).trans_lt hn


/-- Conditional Fatou in the event-integral form used in prop:fatou.
The proof constructs the tail infima and applies monotone convergence. -/
theorem conditional_fatou_set_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : MeasurableSpace Ω) (hle : F ≤ m)
    (f : ℕ → Ω → ℝ) (v z : Ω → ℝ)
    (hfi : ∀ n, Integrable (f n) P) (hvi : Integrable v P) (hzi : Integrable z P)
    (a : ℝ) (hb : ∀ᵐ ω ∂P, ∀ n, a ≤ f n ω)
    (hv : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (v ω)))
    (hz : ∀ᵐ ω ∂P, Tendsto (fun n => P[f n|F] ω) atTop (𝓝 (z ω)))
    (A : Set Ω) (hA : MeasurableSet[F] A) :
    (∫ ω in A, v ω ∂P) ≤ ∫ ω in A, z ω ∂P := by
  let u := fun n ω => ⨅ k, f (n+k) ω
  have hp : ∀ᵐ ω ∂P,
      (∀ n, a ≤ u n ω) ∧ (∀ n k, u n ω ≤ f (n+k) ω) ∧
      Monotone (fun n => u n ω) ∧ Tendsto (fun n => u n ω) atTop (𝓝 (v ω)) := by
    filter_upwards [hb,hv] with ω hω hvω
    exact real_tail_infimum_properties (fun n => f n ω) a (v ω) hω hvω
  have hui (n) : Integrable (u n) P := by
    apply ((integrable_const |a|).add (hfi n).abs).mono'
      ((AEMeasurable.iInf fun k => (hfi (n+k)).aemeasurable).aestronglyMeasurable)
    filter_upwards [hp] with ω hω
    change |u n ω| ≤ |a| + |f n ω|
    rw [abs_le]
    have hh := hω.2.1 n 0
    simp only [Nat.add_zero] at hh
    constructor
    · have ha := neg_abs_le a
      have hn := abs_nonneg (f n ω)
      linarith [hω.1 n]
    · linarith [le_abs_self (f n ω),abs_nonneg a]
  have hce (n) : P[u n|F] ≤ᵐ[P] z := by
    have hh (k) : P[u n|F] ≤ᵐ[P] P[f (n+k)|F] :=
      condExp_mono (hui n) (hfi _) (hp.mono fun ω hω => hω.2.1 n k)
    filter_upwards [ae_all_iff.2 hh,hz] with ω hω hzω
    apply ge_of_tendsto' (hzω.comp (tendsto_add_atTop_nat n))
    intro k
    simpa only [Function.comp_def,Nat.add_comm] using hω k
  have hInt (n) : (∫ ω in A, u n ω ∂P) ≤ ∫ ω in A, z ω ∂P := by
    rw [← setIntegral_condExp hle (hui n) hA]
    exact integral_mono_ae integrable_condExp.integrableOn hzi.integrableOn
      (ae_restrict_le (hce n))
  have hlim := integral_tendsto_of_tendsto_of_monotone (μ := P.restrict A)
    (fun n => (hui n).integrableOn) hvi.integrableOn
    (ae_restrict_le (hp.mono fun ω hω => hω.2.2.1))
    (ae_restrict_le (hp.mono fun ω hω => hω.2.2.2))
  exact le_of_tendsto' hlim hInt

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.real_tail_infimum_properties
#print axioms Asakura.Chapter2Complete.conditional_fatou_set_integral

