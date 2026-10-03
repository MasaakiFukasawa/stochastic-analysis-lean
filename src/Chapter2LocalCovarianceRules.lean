import Chapter2LocalVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

structure LocalCovarianceWitness {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω)
    (X Y C : ClosedTime T → Ω → ℝ) : Prop where
  defect : LocalMProcessWitness P F (fun t ω => X t ω*Y t ω-C t ω)
  variation : LocalVariationWitness F C

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)

include hF hle

theorem local_covariance_witness_exists
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y) :
    ∃ C, LocalCovarianceWitness P F X Y C := by
  obtain ⟨C,hm,hc,hM,τ,ht,htm,htt,htc,ha⟩ := local_covariation_exists P F hF hle hnull X Y hX hY
  refine ⟨C,hM,τ,ht,htm,htt,htc,?_⟩
  intro n ω
  obtain ⟨U,V,_,_,_,_,hU,hV,he⟩ := ha n
  exact ⟨fun t => U t ω,fun t => V t ω,hU ω,hV ω,fun t => he t ω⟩

theorem LocalCovarianceWitness.unique {X Y A B : ClosedTime T → Ω → ℝ}
    (hA : LocalCovarianceWitness P F X Y A) (hB : LocalCovarianceWitness P F X Y B) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → A t ω = B t ω := by
  obtain ⟨τ,ht,htm,htt,htc,ha⟩ := hA.variation.localizers
  obtain ⟨σ,hs,hsm,hst,hsc,hb⟩ := hB.variation.localizers
  exact local_covariation_unique P F hF hle X Y A B hA.defect hB.defect τ σ ht hs htm hsm htc hsc ha hb

omit hF hle in
theorem LocalCovarianceWitness.symm {X Y C : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Y C) : LocalCovarianceWitness P F Y X C := by
  refine ⟨?_,hC.variation⟩
  simpa only [mul_comm] using hC.defect

theorem LocalCovarianceWitness.bilinear
    {X Y Z C D : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Z C) (hD : LocalCovarianceWitness P F Y Z D) (c : ℝ) :
    LocalCovarianceWitness P F (fun t ω => c*X t ω+Y t ω) Z
      (fun t ω => c*C t ω+D t ω) := by
  refine ⟨?_,(hC.variation.smul F c).add F hD.variation⟩
  have h := (hC.defect.smul P F c).add P F hF hle hD.defect
  convert h using 1
  funext t ω
  ring

theorem LocalCovarianceWitness.stopped
    {X Y C : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Y C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) :
    LocalCovarianceWitness P F
      (fun t ω => X (min (σ ω) t) ω) (fun t ω => Y (min (σ ω) t) ω)
      (fun t ω => C (min (σ ω) t) ω) :=
  ⟨hC.defect.stopped P F hF hle σ hσ,hC.variation.stopped F σ⟩

/-- The local symmetry assertion is derived from existence/uniqueness. -/
theorem local_covariance_symmetry {X Y C D : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Y C) (hD : LocalCovarianceWitness P F Y X D) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = D t ω :=
  (hC.symm P F).unique P F hF hle hD

/-- The bilinearity assertion in the local-covariation exercise. -/
theorem local_covariance_bilinearity {X Y Z C D E : ClosedTime T → Ω → ℝ}
    (c : ℝ) (hC : LocalCovarianceWitness P F X Z C) (hD : LocalCovarianceWitness P F Y Z D)
    (hE : LocalCovarianceWitness P F (fun t ω => c*X t ω+Y t ω) Z E) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → E t ω = c*C t ω+D t ω :=
  hE.unique P F hF hle (hC.bilinear P F hF hle hD c)

/-- Stopping compatibility is proved for the constructed characterization. -/
theorem local_covariance_stopping {X Y C D : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Y C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hD : LocalCovarianceWitness P F (fun t ω => X (min (σ ω) t) ω)
      (fun t ω => Y (min (σ ω) t) ω) D) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = C (min (σ ω) t) ω :=
  hD.unique P F hF hle (hC.stopped P F hF hle σ hσ)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariance_witness_exists
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.unique
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.symm
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.bilinear
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.stopped
#print axioms Asakura.Chapter2Complete.local_covariance_symmetry
#print axioms Asakura.Chapter2Complete.local_covariance_bilinearity
#print axioms Asakura.Chapter2Complete.local_covariance_stopping
