import Chapter4BracketHarmonic
import Chapter4LevyBracketCalculus
import Chapter4LevyConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic brackets yield Gaussian increments with their actual
variance increments, proved by the same bounded trigonometric Ito tests as
Levy's characterization. -/
theorem deterministic_bracket_conditional_characteristic
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (q : ClosedTime T → ℝ) (R s : ClosedTime T) (hR : R<⊤) (hs : s≤R)
    (hqm : MonotoneOn q (Iic R))
    (hq : ∀ᵐ w ∂P,∀ t,t≤R → A t w=q t) (u : ℝ) :
    P[(fun w => Complex.exp ((u:ℂ)*((X R w-X s w):ℂ)*Complex.I)) | F s]=ᵐ[P]
      fun _ => Complex.exp (-((q R-q s:ℝ):ℂ)*(u:ℂ)^2/2) := by
  let K := Real.exp (u^2*q R/2)
  have hcos := bracket_harmonic_conditional P hT F hF hle hnull X A hX hA
    (bracketCos u) (bracketCos_smooth u) (bracketCos_harmonic u) R s hR hs K (by
      filter_upwards [hq] with w hw
      intro t ht
      dsimp only [bracketCos,Matrix.cons_val_zero,Matrix.cons_val_one]
      rw [hw t ht]
      exact levyCos_bound u (q R) (q t) (X t w) (hqm ht (le_refl R) ht))
  have hsin := bracket_harmonic_conditional P hT F hF hle hnull X A hX hA
    (bracketSin u) (bracketSin_smooth u) (bracketSin_harmonic u) R s hR hs K (by
      filter_upwards [hq] with w hw
      intro t ht
      dsimp only [bracketSin,Matrix.cons_val_zero,Matrix.cons_val_one]
      rw [hw t ht]
      exact levySin_bound u (q R) (q t) (X t w) (hqm ht (le_refl R) ht))
  have hec t (ht : t≤R) : (fun w => bracketCos u ![X t w,A t w])=ᵐ[P]
      fun w => Real.exp (u^2*q t/2)*Real.cos (u*X t w) := by
    filter_upwards [hq] with w hw
    simp only [bracketCos,levyCos,Matrix.cons_val_zero,Matrix.cons_val_one,hw t ht]
  have hes t (ht : t≤R) : (fun w => bracketSin u ![X t w,A t w])=ᵐ[P]
      fun w => Real.exp (u^2*q t/2)*Real.sin (u*X t w) := by
    filter_upwards [hq] with w hw
    simp only [bracketSin,levySin,Matrix.cons_val_zero,Matrix.cons_val_one,hw t ht]
  have hc := conditional_remove_nonzero_weight P (F s)
    (fun w => Real.cos (u*X R w)) (fun w => Real.cos (u*X s w)) K (Real.exp (u^2*q s/2))
    (Real.exp_ne_zero _) (((condExp_congr_ae (hec R le_rfl)).symm.trans hcos).trans (hec s hs))
  have hi := conditional_remove_nonzero_weight P (F s)
    (fun w => Real.sin (u*X R w)) (fun w => Real.sin (u*X s w)) K (Real.exp (u^2*q s/2))
    (Real.exp_ne_zero _) (((condExp_congr_ae (hes R le_rfl)).symm.trans hsin).trans (hes s hs))
  have hXm := (hX.adapted P F s (hs.trans_lt hR)).const_mul u
  have hYm := ((hX.adapted P F R hR).mono (hle _) le_rfl).const_mul u
  have ht := conditional_trig_increment P (F s) (hle s)
    (fun w => u*X s w) (fun w => u*X R w) hXm hYm (Real.exp (u^2*q s/2)/K) hc hi
  have hz := conditional_characteristic_from_trig P (F s) (fun w => u*X R w-u*X s w)
    (hYm.sub (hXm.mono (hle _) le_rfl)) _ ht.1 ht.2
  have he : Real.exp (u^2*q s/2)/K=Real.exp (-(q R-q s)*u^2/2) := by
    dsimp only [K]
    rw [←Real.exp_sub]
    congr 1
    ring
  rw [he] at hz
  convert hz using 1
  · congr 1
    funext w
    congr 1
    push_cast
    ring
  · funext w
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

theorem deterministic_bracket_gaussian_increment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (q : ClosedTime T → ℝ) (R s : ClosedTime T) (hR : R<⊤) (hs : s≤R)
    (hqm : MonotoneOn q (Iic R)) (hq : ∀ᵐ w ∂P,∀ t,t≤R → A t w=q t) :
    HasLaw (fun w => X R w-X s w) (gaussianReal 0 ⟨q R-q s,sub_nonneg.mpr (hqm hs (le_refl R) hs)⟩) P ∧
    Indep (MeasurableSpace.comap (fun w => X R w-X s w) inferInstance) (F s) P := by
  apply gaussian_independent_of_conditional_characteristic P (F s) (hle s) _
    (((hX.adapted P F R hR).mono (hle _) le_rfl).sub ((hX.adapted P F s (hs.trans_lt hR)).mono (hle _) le_rfl))
    ⟨q R-q s,sub_nonneg.mpr (hqm hs (le_refl R) hs)⟩
  intro u
  convert deterministic_bracket_conditional_characteristic P hT F hF hle hnull X A hX hA q R s hR hs hqm hq u using 1
  all_goals simp only [Pi.sub_apply,Complex.ofReal_sub]
  funext w
  congr 2
  norm_cast

end Asakura.Chapter4
