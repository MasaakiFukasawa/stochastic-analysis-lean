import Chapter2LocalCovariance
import Chapter2M2Localization
import Chapter2AdaptedJordan

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A continuous member of the manuscript's A, with adapted increasing
parts. This is stronger than requiring right-continuous increasing parts. -/
def ContinuousAProcess {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (A : ClosedTime T → Ω → ℝ) : Prop :=
  ∃ U V : ClosedTime T → Ω → ℝ,
    (∀ t, Measurable[F t] (U t)) ∧ (∀ t, Measurable[F t] (V t)) ∧
    (∀ ω, Continuous (fun t => U t ω)) ∧ (∀ ω, Continuous (fun t => V t ω)) ∧
    (∀ ω, Monotone (fun t => U t ω)) ∧ (∀ ω, Monotone (fun t => V t ω)) ∧
    ∀ t ω, A t ω = U t ω - V t ω

/-- The existence construction with all essential conclusions joined:
C is locally in A with adapted increasing parts, and XY-C is in the
manuscript's bounded-localizer definition of M_loc, not just weakly M2-local. -/
theorem local_covariation_construction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (htop : ∀ n ω, τ n ω < ⊤)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (hX : ∀ n, (fun t ω => X (min (τ n ω) t) ω) ∈ boundedMProcess P F)
    (hY : ∀ n, (fun t ω => Y (min (τ n ω) t) ω) ∈ boundedMProcess P F) :
    ∃ C : ClosedTime T → Ω → ℝ,
      (∀ t, t < ⊤ → Measurable[F t] (C t)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t) ∧
      LocalMProcessWitness P F (fun t ω => X t ω * Y t ω-C t ω) ∧
      (∀ n, ContinuousAProcess F (fun t ω => C (min (τ n ω) t) ω)) := by
  obtain ⟨C,hm,hc,hbv,hM,he⟩ := local_covariation_exists_along_localizers P F hF hle hnull
    X Y τ hτ hmono htop hcofinal hX hY
  refine ⟨C,hm,hc,m2_localization_implies_local P F hF hle _ τ hτ hmono htop hcofinal hM,?_⟩
  intro n
  let Z := fun t ω => C (min (τ n ω) t) ω
  have hZm (t) : Measurable[F t] (Z t) := by
    have h := (((hX n).1.adapted t).mul ((hY n).1.adapted t)).sub ((hM n).adapted t)
    convert h using 1
    funext ω
    simp only [Pi.sub_apply,Pi.mul_apply,Z]
    ring
  have hZc (ω) : Continuous (fun t => Z t ω) := by
    have h := (((hX n).1.path ω).mul ((hY n).1.path ω)).sub ((hM n).path ω)
    convert h using 1
    funext t
    simp only [Z,Pi.sub_apply,Pi.mul_apply]
    ring
  have hZbv (ω) : BoundedVariationOn (fun t => Z t ω) univ := by
    obtain ⟨U,V,hU,hV,he⟩ := hbv n ω
    simpa only [Z,he] using increasing_difference_boundedVariation U V hU hV
  exact adapted_continuous_jordan_decomposition F hF Z hZm hZc hZbv

/-- Common bounded localizers exist for any two actual local martingales;
the construction above therefore applies directly to the written hypotheses. -/
theorem local_covariation_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y) :
    ∃ C : ClosedTime T → Ω → ℝ,
      (∀ t, t < ⊤ → Measurable[F t] (C t)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t) ∧
      LocalMProcessWitness P F (fun t ω => X t ω * Y t ω-C t ω) ∧
      ∃ ρ : ℕ → Ω → ClosedTime T,
        (∀ n t, MeasurableSet[F t] {ω | ρ n ω ≤ t}) ∧
        (∀ ω, Monotone (fun n => ρ n ω)) ∧ (∀ n ω, ρ n ω < ⊤) ∧
        (∀ ω t, t < ⊤ → ∃ n, t < ρ n ω) ∧
        (∀ n, ContinuousAProcess F (fun t ω => C (min (ρ n ω) t) ω)) := by
  obtain ⟨τ,ht,htm,htt,htc,hx⟩ := hX.localizers
  obtain ⟨σ,hs,hsm,hst,hsc,hy⟩ := hY.localizers
  let ρ := fun n ω => min (τ n ω) (σ n ω)
  have hr (n) := (written_stopping_min_max F (τ n) (σ n) (ht n) (hs n)).1
  have hrm (ω) : Monotone (fun n => ρ n ω) := (htm ω).min (hsm ω)
  have hrt (n ω) : ρ n ω < ⊤ := (min_le_left _ _).trans_lt (htt n ω)
  have hrc (ω) := (common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
    (htm ω) (hsm ω) (htc ω) (hsc ω)).2
  have hxρ (n) := bounded_at_minimum P F hF hle X (τ n) (σ n) (hs n) (hx n)
  have hyρ (n) : (fun t ω => Y (min (ρ n ω) t) ω) ∈ boundedMProcess P F := by
    simpa only [ρ,min_comm (σ n _) (τ n _)] using
      bounded_at_minimum P F hF hle Y (σ n) (τ n) (ht n) (hy n)
  obtain ⟨C,hm,hc,hM,hA⟩ := local_covariation_construction P F hF hle hnull
    X Y ρ hr hrm hrt hrc hxρ hyρ
  exact ⟨C,hm,hc,hM,ρ,hr,hrm,hrt,hrc,hA⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariation_construction
#print axioms Asakura.Chapter2Complete.local_covariation_exists
