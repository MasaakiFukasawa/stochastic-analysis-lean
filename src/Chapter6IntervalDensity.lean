import Chapter6NovikovWritten
import Chapter6IncrementCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Each interval in the finite-partition Novikov criterion supplies a
mean-one conditional density, measurable at the right endpoint. -/
theorem novikov_interval_density
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (a b : ClosedTime T) (hab : a ≤ b) (γ : ℝ) (hγ : 1/2 < γ)
    (hi : Integrable (fun w => Real.exp (γ*(C (min b (τ w)) w-C (min a (τ w)) w))) P) :
    let d := fun w => Real.exp ((Z (min b (τ w)) w-Z (min a (τ w)) w)-
      (C (min b (τ w)) w-C (min a (τ w)) w)/2)
    Measurable[F b] d ∧ Integrable d P ∧ P[d|F a] =ᵐ[P] (fun _ => (1:ℝ)) := by
  have hs (v t : ClosedTime T) : MeasurableSet[F t] {w : Ω | v ≤ t} := by
    by_cases hv : v ≤ t <;> simp [hv]
  let Zb := fun t w => Z (min b t) w
  let Cb := fun t w => C (min b t) w
  have hZb := hZ.stopped P F hF hle (fun _ => b) (hs b)
  have hCb := hC.stopped P F hF hle (fun _ => b) (hs b)
  obtain ⟨hI,hK⟩ := after_stop_self_covariance P F hF hle hnull Zb Cb hZb hCb (fun _ => a) (hs a)
  let I := fun t w => Zb t w-Zb (min a t) w
  let K := fun t w => Cb t w-Cb (min a t) w
  have hmin (t : ClosedTime T) : min b (min a t) = min a t := by
    rw [← min_assoc,min_eq_right hab]
  have hki : Integrable (fun w => Real.exp (γ*K (τ w) w)) P := by
    simpa only [K,Cb,hmin] using hi
  have hnov := novikov_written P hT F hF hle hnull I K hI hK τ hτ hτt γ hγ hki
  let E := fun t w => Real.exp (I (min (τ w) t) w-K (min (τ w) t) w/2)
  have hIr := open_process_stopped_regular F hF I (hI.adapted P F) (hI.path P F) τ hτ hτt
  have hKr := hK.stopped_regular P F hF hle hI hI τ hτ hτt
  have hEa t : Measurable[F t] (E t) :=
    Real.continuous_exp.measurable.comp ((hIr.1 t).sub ((hKr.1 t).div_const 2))
  let d := fun w => Real.exp ((Z (min b (τ w)) w-Z (min a (τ w)) w)-
    (C (min b (τ w)) w-C (min a (τ w)) w)/2)
  have heb : E b = d := by
    funext w
    dsimp [E,I,K,Zb,Cb,d]
    simp only [hmin,← min_assoc]
    rw [min_eq_left (min_le_left b (τ w)),min_eq_left ((min_le_left a (τ w)).trans hab)]
  have hea : E a = fun _ => (1:ℝ) := by
    funext w
    dsimp [E,I,K,Zb,Cb]
    have h1 : min a (min (τ w) a) = min (τ w) a := min_eq_right (min_le_right _ _)
    rw [h1,sub_self,sub_self,zero_div,sub_self,Real.exp_zero]
  change Measurable[F b] d ∧ Integrable d P ∧ P[d|F a] =ᵐ[P] (fun _ => (1:ℝ))
  refine ⟨by rw [← heb]; exact hEa b,by rw [← heb]; exact hnov.1 b,?_⟩
  have hh := hnov.2.1 a b hab
  change P[E b|F a] =ᵐ[P] E a at hh
  rwa [heb,hea] at hh

end Asakura.Chapter6
