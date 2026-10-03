import Chapter13CheyetteDriftVariation
import Chapter3SemimartingaleFiniteSums

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The state built by Cheyette's time integrals and matrix noise has the
required semimartingale decomposition; its martingale part is the original
matrix stochastic integral, so its covariance is unchanged. -/
theorem cheyette_state_semimartingale {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {n:ℕ}
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (R:ℝ) (hR:0≤R) (A:Fin n → Fin n → Ω × ℝ → ℝ)
    (hp:∀i k,@Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => A i k (z.1,z.2.val)))
    (hi:∀i k w,IntervalIntegrable (fun r => A i k (w,r)) volume 0 R)
    (g:Fin n → ℝ → ℝ) (hgm:∀k,Measurable (g k)) (hgi:∀k,IntervalIntegrable (g k) volume 0 R)
    (N:Fin n → HalfClosedTime → Ω → ℝ) (hN:∀i,LocalMProcessWitness P F (N i)) :
    ∃X D:Fin n → HalfClosedTime → Ω → ℝ,
      (∀i,SemimartingaleDecomposition P F (X i) (D i) (N i)) ∧
      ∀i t w,X i t w=(∑k,∫r in 0..(finitePrefixTime R hR t).val,(∫s in 0..r,A i k (w,s))*g k r)+N i t w := by
  have hex i k:=cheyette_double_primitive_variation F hF R hR (A i k) (hp i k) (hi i k) (g k) (hgm k) (hgi k)
  choose D hD hDc hDe using hex
  let Dsum:=fun i t w => ∑k,D i k t w
  have hDv i:AdaptedLocalVariationWitness F (Dsum i) :=
    adapted_variation_finset_sum (by simp : (0:EReal)<⊤) F hF Finset.univ (D i) (fun k _ => hD i k)
  have hDsc i w:Continuous (fun t => Dsum i t w) := by
    apply continuous_finset_sum
    intro k _
    exact hDc i k w
  refine ⟨(fun i t w => Dsum i t w+N i t w),Dsum,?_,?_⟩
  · intro i
    exact ⟨hDv i,hN i,fun w t ht => (hDsc i w).continuousAt.add ((hN i).path P F w t ht),fun _ _ _ => rfl⟩
  · intro i t w
    simp only [Dsum,hDe]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_state_semimartingale
