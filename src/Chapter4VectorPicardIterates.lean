import Chapter4VectorPicardImage

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct every Picard iterate with its actual stochastic integral.
The iteration is in adapted continuous paths with finite second moment. -/
theorem finite_picard_iterates
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    : ∃ (X : ℕ → Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
        (N : ℕ → Fin dim → Fin noise → ClosedTime T → Ω → ℝ),
      (∀ w r,X 0 w r=ξ w) ∧
      (∀ n,Measurable[m] (X n)) ∧ (∀ n,MemLp (X n) 2 P) ∧
      (∀ n r,Measurable[F (realTimeClamp r.val)] (fun w => X n w r)) ∧
      (∀ n i j,LocalMProcessWitness P F (N n i j)) ∧
      (∀ n i j,ItoCovarianceFormula P F (W j)
        (fun z => σ i j (X n z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N n i j)) ∧
      ∀ n w r i,X (n+1) w r i=ξ w i+
        (∫ s in 0..r.val,μ i (X n w (projIcc 0 R hR s)))+∑ j,N n i j (realTimeClamp r.val) w := by
  classical
  letI : MeasurableSpace Ω := m
  let S := {Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ) // Measurable[m] Y ∧ MemLp Y 2 P ∧
    ∀ r,Measurable[F (realTimeClamp (T := T) r.val)] (fun w => Y w r)}
  have hex (Y : S) := finite_picard_image P hT F hF hle hnull W C hW hC hclock
    R hR hRT L hL μ σ hμ hσ hμLip hσLip ξ hξ hξi Y.val Y.property.1 Y.property.2.1 Y.property.2.2
  choose V N hm hi ha hN hI he using hex
  let Φ : S → S := fun Y => ⟨V Y,hm Y,hi Y,ha Y⟩
  have hconstm : Measurable[m] (fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)) :=
    ContinuousMap.measurable_iff_eval.mpr (fun _ => hξ.mono (hle _) le_rfl)
  have hconsti : MemLp (fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)) 2 P := by
    apply hξi.of_le_mul (c := 1) hconstm.aestronglyMeasurable
    exact .of_forall (fun w => by simpa only [one_mul] using (ContinuousMap.norm_le _ (norm_nonneg (ξ w))).2 (fun _ => le_rfl))
  let X0 : S := ⟨fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w),hconstm,hconsti,
    fun _ => hξ.mono (hF bot_le) le_rfl⟩
  let Z : ℕ → S := fun n => (Φ^[n]) X0
  have hstep n : Z (n+1)=Φ (Z n) := Function.iterate_succ_apply' Φ n X0
  refine ⟨fun n => (Z n).val,fun n => N (Z n),?_,?_,?_,?_,?_,?_,?_⟩
  · intro w r; rfl
  · intro n; exact (Z n).property.1
  · intro n; exact (Z n).property.2.1
  · intro n; exact (Z n).property.2.2
  · intro n; exact hN (Z n)
  · intro n; exact hI (Z n)
  · intro n
    dsimp only
    rw [hstep]
    exact he (Z n)

end Asakura.Chapter4.Vector
