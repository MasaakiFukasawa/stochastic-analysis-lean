import Chapter3QVDefectEstimate
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Turn the deterministic-time essential bounds defining the partition
into one common pathwise bound, including its stopped terminal value. -/
theorem stopped_increment_common_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ τ : Ω → ClosedTime T) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hτtop : ∀ ω, τ ω < ⊤) (δ : ℝ)
    (hb : ∀ t, t < ⊤ → ∀ᵐ ω ∂P,
      ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ) :
    ∀ᵐ ω ∂P, ∀ t, ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ := by
  let D := fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω
  have hc (ω) : Continuous (fun t => D t ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hX.path P F ω _ ((min_le_left _ _).trans_lt (hτtop ω))).comp
      (continuous_const.min continuous_id).continuousAt).sub
      ((hX.path P F ω _ ((min_le_left _ _).trans_lt ((hστ ω).trans_lt (hτtop ω)))).comp
        (continuous_const.min continuous_id).continuousAt)
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have he := continuous_process_common_time_equality P
    (fun t : Iio (⊤ : ClosedTime T) => fun ω => min ‖D t.val ω‖ δ)
    (fun t : Iio (⊤ : ClosedTime T) => fun ω => ‖D t.val ω‖)
    (fun ω => (((hc ω).comp continuous_subtype_val).norm).min continuous_const)
    (fun ω => ((hc ω).comp continuous_subtype_val).norm)
    (fun t => (hb t.val t.property).mono fun ω h => min_eq_left h)
  filter_upwards [he] with ω hω
  intro t
  have hh := hω ⟨min (τ ω) t,(min_le_left _ _).trans_lt (hτtop ω)⟩
  have hb' : ‖D (min (τ ω) t) ω‖ ≤ δ := by
    rw [← hh]
    exact min_le_right _ _
  simpa only [D,← min_assoc,min_self,min_eq_left (hστ ω)] using hb'

/-- All three assertions of lem:adiff, for a general oscillation bound δ.
The M2 assertion respects the manuscript's identification of processes equal
outside a common null set. The norm bound uses sqrt(E increment^2), i.e. L2. -/
theorem stopped_increment_lemma
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hστ : ∀ ω, σ ω ≤ τ ω) (hτtop : ∀ ω, τ ω < ⊤)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ) :
    let D := fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω
    let R := fun t ω => D t ω^2-(Q (min (τ ω) t) ω-Q (min (σ ω) t) ω)
    D ∈ boundedMProcess P F ∧
    (∃ Z, ContinuousM2Witness P F Z ∧ ∀ᵐ ω ∂P, ∀ t, Z t ω = R t ω) ∧
    ∀ t, t < ⊤ → eLpNorm (R t) 2 P ≤
      ENNReal.ofReal (2*δ*Real.sqrt (∫ ω, D t ω^2 ∂P)) := by
  dsimp only
  let D := fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω
  have hD := stopped_increment_bounded P F hF hle X hX σ τ hσ hτ hστ hτtop δ hb
  let DB : boundedMProcess P F := ⟨D,hD⟩
  let B := boundedQV P F hF hle hnull DB
  have hB := boundedQV_properties P F hF hle hnull DB
  obtain ⟨ρ,hr,hrm,hrt,hrc,hrb⟩ := hX.localizers
  have hlocal : LocalCovarianceWitness P F D D B := by
    refine ⟨?_,⟨ρ,hr,hrm,hrt,hrc,?_⟩⟩
    · have hM : LocalMProcessWitness P F (fun t ω => D t ω^2-B t ω) :=
        m2_localization_implies_local P F hF hle _ ρ hr hrm hrt hrc
          (fun n => continuous_m2_stopped P F hF hle _ hB.2.2.2 (ρ n) (hr n))
      simpa only [pow_two] using hM
    · intro n ω
      refine ⟨fun t => B (min (ρ n ω) t) ω,fun _ => 0,
        (hB.2.2.1 ω).comp (monotone_const.min monotone_id),monotone_const,?_⟩
      intro t
      simp only [sub_zero]
  have hid := stopped_increment_quadratic_variation P F hF hle hnull X Q B hX hQ σ τ
    hσ hτ hστ hlocal
  refine ⟨hD,?_,?_⟩
  · let Z := fun t ω => D (min (τ ω) t) ω^2-B (min (τ ω) t) ω
    refine ⟨Z,continuous_m2_stopped P F hF hle _ hB.2.2.2 τ hτ,?_⟩
    filter_upwards [hid] with ω hω
    intro t
    dsimp only [Z,D]
    rw [hω _ ((min_le_left _ _).trans_lt (hτtop ω))]
    simp only [← min_assoc,min_self,min_eq_left (hστ ω)]
  · intro t ht
    have he : (fun ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω) = D t := rfl
    have hr : (fun ω => (X (min (τ ω) t) ω-X (min (σ ω) t) ω)^2-
        (Q (min (τ ω) t) ω-Q (min (σ ω) t) ω)) =ᵐ[P]
        (fun ω => DB.val t ω^2-B t ω) := by
      filter_upwards [hid] with ω hω
      dsimp only [DB,D]
      rw [hω t ht]
    rw [eLpNorm_congr_ae hr]
    exact bounded_qv_defect_amplitude_bound P F hF hle hnull DB t δ hδ
      (hb.mono fun ω h => h t)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_increment_lemma

#print axioms Asakura.Chapter3Complete.stopped_increment_common_bound
