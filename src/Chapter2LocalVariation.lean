import Chapter2LocalCovarianceUniqueness
import FullAuditCovarianceBilinear

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The pathwise variation consequence of A_loc. Adaptedness of the two
parts is not required here; this weaker premise suffices for uniqueness. -/
structure LocalVariationWitness {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (A : ClosedTime T → Ω → ℝ) : Prop where
  localizers : ∃ τ : ℕ → Ω → ClosedTime T,
    (∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t}) ∧
    (∀ ω, Monotone (fun n => τ n ω)) ∧ (∀ n ω, τ n ω < ⊤) ∧
    (∀ ω t, t < ⊤ → ∃ n, t < τ n ω) ∧
    (∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A (min (τ n ω) t) ω = U t-V t)

variable {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω)

/-- Addition allows distinct localizing sequences. -/
theorem LocalVariationWitness.add {A B : ClosedTime T → Ω → ℝ}
    (hA : LocalVariationWitness F A) (hB : LocalVariationWitness F B) :
    LocalVariationWitness F (fun t ω => A t ω+B t ω) := by
  obtain ⟨τ,ht,hm,htt,hc,ha⟩ := hA.localizers
  obtain ⟨σ,hs,hsm,hst,hsc,hb⟩ := hB.localizers
  refine ⟨fun n ω => min (τ n ω) (σ n ω),?_,?_,?_,?_,?_⟩
  · intro n
    exact (written_stopping_min_max F (τ n) (σ n) (ht n) (hs n)).1
  · intro ω
    exact (hm ω).min (hsm ω)
  · intro n ω
    exact (min_le_left _ _).trans_lt (htt n ω)
  · intro ω
    exact (common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
      (hm ω) (hsm ω) (hc ω) (hsc ω)).2
  · intro n ω
    obtain ⟨Ap,An,hAp,hAn,heA⟩ := ha n ω
    obtain ⟨Bp,Bn,hBp,hBn,heB⟩ := hb n ω
    refine ⟨fun t => Ap (min (σ n ω) t)+Bp (min (τ n ω) t),
      fun t => An (min (σ n ω) t)+Bn (min (τ n ω) t),
      (hAp.comp (monotone_const.min monotone_id)).add (hBp.comp (monotone_const.min monotone_id)),
      (hAn.comp (monotone_const.min monotone_id)).add (hBn.comp (monotone_const.min monotone_id)),?_⟩
    intro t
    have ha := heA (min (σ n ω) t)
    have hb := heB (min (τ n ω) t)
    simp only [← min_assoc,min_comm (σ n ω) (τ n ω)] at ha hb
    rw [ha,hb]
    ring

theorem LocalVariationWitness.smul {A : ClosedTime T → Ω → ℝ}
    (hA : LocalVariationWitness F A) (c : ℝ) :
    LocalVariationWitness F (fun t ω => c*A t ω) := by
  obtain ⟨τ,ht,hm,hb,hc,ha⟩ := hA.localizers
  refine ⟨τ,ht,hm,hb,hc,?_⟩
  intro n ω
  exact monotone_difference_smul _ (ha n ω) c

/-- Finite variation is preserved by stopping, pathwise. -/
theorem LocalVariationWitness.stopped {A : ClosedTime T → Ω → ℝ}
    (hA : LocalVariationWitness F A) (σ : Ω → ClosedTime T) :
    LocalVariationWitness F (fun t ω => A (min (σ ω) t) ω) := by
  obtain ⟨τ,ht,hm,hb,hc,ha⟩ := hA.localizers
  refine ⟨τ,ht,hm,hb,hc,?_⟩
  intro n ω
  obtain ⟨U,V,hU,hV,he⟩ := ha n ω
  refine ⟨fun t => U (min (σ ω) t),fun t => V (min (σ ω) t),
    hU.comp (monotone_const.min monotone_id),hV.comp (monotone_const.min monotone_id),?_⟩
  intro t
  simpa only [min_left_comm (σ ω) (τ n ω)] using he (min (σ ω) t)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalVariationWitness.add
#print axioms Asakura.Chapter2Complete.LocalVariationWitness.smul
#print axioms Asakura.Chapter2Complete.LocalVariationWitness.stopped
