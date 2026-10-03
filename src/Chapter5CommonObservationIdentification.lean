import Chapter5ObservationGradientPrefix
import Chapter5StoppedPrefixIdentification
import Chapter5CommonHeatIntegrals

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- All current-coordinate integrals in a preterminal Ito formula are
identified with restrictions of the common terminal-horizon integrals. -/
theorem common_observation_integral_identification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (index : Fin k → Fin d) (active : Fin k → Prop) [DecidablePred active] (τ : Fin k → ℝ)
    (b S : ℝ) (hb : 0≤b) (hbS : b≤S) (hbT : (b:EReal)<T)
    (hcurrent : ∀ i,active i → τ i=b)
    (ν : Measure (Fin k → ℝ)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : Fin k → ℝ => z) ν)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C)
    (g : ((Fin k → ℝ) × ℝ) → ℝ) (hg : ContDiff ℝ 2 g)
    (he : ∀ p : (Fin k → ℝ) × ℝ,p.2≤b → g p=∫ z,f (p.1+Real.sqrt (S-p.2) • z) ∂ν)
    (J : Fin k → ClosedTime T → Ω → ℝ) (hJ : ∀ i,LocalMProcessWitness P F (J i))
    (N : Fin (k+1) → ClosedTime T → Ω → ℝ) (hN : ∀ i,LocalMProcessWitness P F (N i))
    (hNI : let X : Fin k → ClosedTime T → Ω → ℝ := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
      let clock := fun t (_ : Ω) => (finitePrefixTime (T := T) b hb t).val
      let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons clock X
      let M : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons (fun _ _ => (0:ℝ)) X
      ∀ i,ItoCovarianceFormula P F (M i)
        (fun z => fderiv ℝ (fun x => g (spaceTimeCoordinates k x))
          (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i))
    (hJI : ∀ i,ItoCovarianceFormula P F (W (index i))
      (fun z : Ω × ℝ => ∫ y,D ((fun j => W (index j)
          (min (realTimeClamp (if active j then S else τ j)) (realTimeClamp z.2)) z.1)+
        Real.sqrt (S-(finitePrefixTime (T := T) S (hb.trans hbS) (realTimeClamp z.2)).val) • y) (Pi.single i 1) ∂ν) (J i))
    (hGm : ∀ i w,Measurable (fun r => ∫ y,D ((fun j => W (index j)
          (min (realTimeClamp (if active j then S else τ j)) (realTimeClamp r)) w)+
        Real.sqrt (S-(finitePrefixTime (T := T) S (hb.trans hbS) (realTimeClamp r)).val) • y) (Pi.single i 1) ∂ν)) :
    ∀ᵐ w ∂P,∀ i,active i → ∀ t,t<⊤ → N i.succ t w=J i (min (realTimeClamp b) t) w := by
  classical
  apply ae_all_iff.mpr
  intro i
  by_cases hiA : active i
  · let X : Fin k → ClosedTime T → Ω → ℝ := fun j t w => W (index j) (min (realTimeClamp (τ j)) t) w
    let clock := fun t (_ : Ω) => (finitePrefixTime (T := T) b hb t).val
    let XX : Fin (k+1) → ClosedTime T → Ω → ℝ := Fin.cons clock X
    let H := fun z : Ω × ℝ => fderiv ℝ (fun x => g (spaceTimeCoordinates k x))
      (fun j => XX j (realTimeClamp z.2) z.1) (Pi.single i.succ 1)
    let G := fun z : Ω × ℝ => ∫ y,D ((fun j => W (index j)
          (min (realTimeClamp (if active j then S else τ j)) (realTimeClamp z.2)) z.1)+
        Real.sqrt (S-(finitePrefixTime (T := T) S (hb.trans hbS) (realTimeClamp z.2)).val) • y) (Pi.single i 1) ∂ν
    have hHm := (observation_integrand_regularity P hT F hF hle W hW index τ b hb
      (fun x => g (spaceTimeCoordinates k x)) (hg.comp (spaceTimeCoordinates k).contDiff) i.succ).1
    have hI : ItoCovarianceFormula P F (fun t w => W (index i) (min (realTimeClamp b) t) w) H (N i.succ) := by
      have hh := hNI i.succ
      change ItoCovarianceFormula P F (fun t w => W (index i) (min (realTimeClamp (τ i)) t) w) H (N i.succ) at hh
      simpa only [hcurrent i hiA] using hh
    have hp : ∀ w r,r∈Ioc 0 b → H (w,r)=G (w,r) := by
      intro w r hr
      have hx : (fun j => XX j (realTimeClamp r) w)=
          (Fin.cons (finitePrefixTime (T := T) b hb (realTimeClamp r)).val
            (fun j => W (index j) (min (realTimeClamp (τ j)) (realTimeClamp r)) w) : Fin (k+1) → ℝ) := by
        ext j
        exact Fin.cases rfl (fun _ => rfl) j
      dsimp only [H,G]
      rw [hx]
      exact observation_gradient_prefix W index active τ b S hb hbS hbT hcurrent ν hi f D hd hDc C hD g hg he w r hr i
    have hh := stopped_integral_prefix_identification P hT F hF hle hnull (W (index i)) (J i) (N i.succ)
      (hW (index i)) (hJ i) (hN i.succ) H G hHm (hGm i) b hb hI (hJI i) hp
    exact hh.mono fun w hw _ => hw
  · exact ae_of_all _ fun _ hi => False.elim (hiA hi)

end Asakura.Chapter5
