import Chapter2SquareIntegrableStop
import Chapter2OneSidedStoppedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)

include hF hle

/-- First assertion of manuscript Lemma lem:adiff. The boundedness is exactly
that of an oscillation partition; no martingale or endpoint extension of the
increment is assumed. Both are derived from the original local process. -/
theorem stopped_increment_bounded
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hστ : ∀ ω, σ ω ≤ τ ω) (hτtop : ∀ ω, τ ω < ⊤)
    (δ : ℝ)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ) :
    (fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω) ∈ boundedMProcess P F := by
  let D := fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω
  have hD : LocalMProcessWitness P F D := by
    convert ((hX.stopped P F hF hle σ hσ).smul P F (-1)).add P F hF hle
      (hX.stopped P F hF hle τ hτ) using 1
    funext t ω
    simp [D]; ring
  have he : (fun t ω => D (min (τ ω) t) ω) = D := by
    funext t ω
    dsimp [D]
    rw [← min_assoc, min_self, ← min_assoc, min_eq_left (hστ ω)]
  have h := bounded_local_stop_is_bounded_martingale P F hF hle D hD τ hτ hτtop δ
    (by
      filter_upwards [hb] with ω hω
      intro t
      change ‖(fun t ω => D (min (τ ω) t) ω) t ω‖ ≤ δ
      rw [he]
      exact hω t)
  simpa only [he] using h

/-- Recover the norm estimate discarded by the canonical QV choice. It is
transferred by the proved uniqueness theorem, not attached as an extra axiom. -/
theorem bounded_qv_defect_terminal_bound
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : boundedMProcess P F) :
    eLpNorm (fun ω => X.val ⊤ ω^2-boundedQV P F hF hle hnull X ⊤ ω) 2 P ≤
      ENNReal.ofReal (2*(eLpNorm (X.val ⊤) ∞ P).toReal*
        Real.sqrt (∫ ω, X.val ⊤ ω^2 ∂P)) := by
  obtain ⟨A,_,_,hAo,hYA,hbound,hunique⟩ :=
    quadratic_variation_exists_unique_written P F hF hle hnull X.val
      X.property.1.adapted X.property.2 X.property.1.path
      X.property.1.martingale X.property.1.initial
  obtain ⟨_,_,hQo,hYQ⟩ := boundedQV_properties P F hF hle hnull X
  have he := hunique _ hQo hYQ
  have hd : (fun ω => X.val ⊤ ω^2-boundedQV P F hF hle hnull X ⊤ ω) =ᵐ[P]
      (fun ω => X.val ⊤ ω^2-A ⊤ ω) := he.mono fun ω h => by dsimp only; rw [h ⊤]
  rw [eLpNorm_congr_ae hd]
  exact hbound

/-- Quadratic variation of a stopped increment. The cross term is derived
from one-sided stopping and bilinearity, including the common exceptional set. -/
theorem stopped_increment_quadratic_variation
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q D : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (hD : LocalCovarianceWitness P F
      (fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω)
      (fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω) D) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = Q (min (τ ω) t) ω-Q (min (σ ω) t) ω := by
  let U := fun t ω => X (min (τ ω) t) ω
  let V := fun t ω => X (min (σ ω) t) ω
  obtain ⟨E,hE⟩ := local_covariance_witness_exists P F hF hle hnull V X
    (hX.stopped P F hF hle σ hσ) hX
  have he := local_covariance_one_sided_stopping P F hF hle hnull X X Q E hX hX hQ σ hσ hE
  have hVU : LocalCovarianceWitness P F V U (fun t ω => E (min (τ ω) t) ω) := by
    have h := hE.stopped P F hF hle τ hτ
    have hv : (fun t ω => V (min (τ ω) t) ω) = V := by
      funext t ω
      dsimp [V]
      rw [← min_assoc, min_eq_left (hστ ω)]
    simpa only [hv] using h
  have hUU := hQ.stopped P F hF hle τ hτ
  have hVV := hQ.stopped P F hF hle σ hσ
  have hDU := hVU.bilinear P F hF hle hUU (-1)
  have hDV := hVV.bilinear P F hF hle (hVU.symm P F) (-1)
  have hDD := (hDV.symm P F).bilinear P F hF hle (hDU.symm P F) (-1)
  have hform : LocalCovarianceWitness P F
      (fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω)
      (fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω)
      (fun t ω => Q (min (τ ω) t) ω+Q (min (σ ω) t) ω-2*E (min (τ ω) t) ω) := by
    convert hDD using 1 <;> (funext t ω; first | (dsimp [U,V]; ring) | ring)
  filter_upwards [hD.unique P F hF hle hform,he] with ω hd heω
  intro t ht
  rw [hd t ht,heω _ ((min_le_right _ _).trans_lt ht)]
  rw [← min_assoc, min_eq_left (hστ ω)]
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_increment_bounded
#print axioms Asakura.Chapter3Complete.bounded_qv_defect_terminal_bound

#print axioms Asakura.Chapter3Complete.stopped_increment_quadratic_variation
