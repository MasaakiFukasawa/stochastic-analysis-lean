import Chapter2SemimartingaleAssociativity
import Chapter2VariationStoppingTimes
import Chapter2ItoStoppingTimes

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the stopped-interval integral in S from its two actual components.
The finite-variation component retains the original adapted A_loc membership. -/
theorem semimartingale_stochastic_interval_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A M Y Q : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (hQ : LocalCovarianceWitness P F M M Q)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hQm : ∀ n ω, MonotoneOn (fun r => Q (realTimeClamp r) ω) (Icc 0 (c n)))
    (hQc : ∀ n ω, ContinuousOn (fun r => Q (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => Q (realTimeClamp r) ω) (hQm n ω)
        (fun r hr => (hQc n ω r hr).mono inter_subset_left)).measure)
    (σ τ : Ω → ClosedTime T) (hσtop : ∀ ω, σ ω < ⊤) (hτtop : ∀ ω, τ ω < ⊤)
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hY : SemimartingaleIntegralFormula P F c (fun n => (hc n).le) A M H Y) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      SemimartingaleIntegralFormula P F c (fun n => (hc n).le) A M
        (fun z => (Ioc (σ z.1) (τ z.1)).indicator (fun _ => H z) (realTimeClamp z.2)) Z ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ →
        Z t ω = Y (min (τ ω) t) ω-Y (min (σ ω) t) ω) := by
  obtain ⟨I,J,hD,hI,hJ⟩ := hY
  obtain ⟨J0,L,hJ0,hL,hJ0f,hLf,heL⟩ := ito_stochastic_interval_for_stopping_times
    P hT F hF hle hnull M Q hX.martingale hQ c hc hcm hcT hct hcut hcc hQm hQc
    H hH hi σ τ hσtop hτtop hστ hσ hτ
  have heJ := hJ0f.unique P hT F hF hle hnull M J0 J H hX.martingale hJ0 hD.martingale hJ
  let K : ClosedTime T → Ω → ℝ := fun t ω => I (min (τ ω) t) ω-I (min (σ ω) t) ω
  have hK : AdaptedLocalVariationWitness F K := by
    simpa only [K,neg_one_mul,← sub_eq_add_neg] using
      (hD.variation.stopped hF τ hτ).add ((hD.variation.stopped hF σ hσ).smul (-1)) hF
  have hIc := hD.variation_continuous P F
  have hKc ω t (ht : t < ⊤) : ContinuousAt (fun s => K s ω) t :=
    ((hIc ω _ ((min_le_right _ _).trans_lt ht)).comp
      (continuous_const.min continuous_id).continuousAt).sub
    ((hIc ω _ ((min_le_right _ _).trans_lt ht)).comp
      (continuous_const.min continuous_id).continuousAt)
  refine ⟨fun t ω => K t ω+L t ω,⟨K,L,
    ⟨hK,hL,fun ω t ht => (hKc ω t ht).add (hL.path P F ω t ht),fun _ _ _ => rfl⟩,
    hI.stochastic_interval P c (fun n => (hc n).le) hcT A I H σ τ hσtop hτtop hστ,hLf⟩,?_⟩
  filter_upwards [heL,heJ] with ω hLω hJω
  intro t ht
  rw [hLω t ht,hJω _ ((min_le_right _ _).trans_lt ht),hJω _ ((min_le_right _ _).trans_lt ht),
    hD.decomposition _ ((min_le_right _ _).trans_lt ht) ω,
    hD.decomposition _ ((min_le_right _ _).trans_lt ht) ω]
  dsimp only [K]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.semimartingale_stochastic_interval_constructed
