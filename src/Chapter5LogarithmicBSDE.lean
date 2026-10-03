import Chapter5NonlinearFeynmanKacBrownian
import Chapter5LogExtension
import Chapter5ScalarLiftCalculus

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic BSDE is derived by applying the constructed Brownian Ito
formula to the logarithm of the represented positive martingale. -/
theorem logarithmic_brownian_bsde
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W A X M : ClosedTime T → Ω → ℝ) (U₀ : Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X (fun _ => U₀) M)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (G : Ω × ℝ → ℝ) (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b)
    (hpos : ∀ᵐ w ∂P,∀ r ∈ Icc 0 R,b ≤ X (realTimeClamp r) w)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hMG : ItoCovarianceFormula P F W G M) :
    let Z := fun z : Ω × ℝ => deriv (logExtension b a) (X (realTimeClamp z.2) z.1)*G z
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧ ItoCovarianceFormula P F W Z N ∧
      (∀ᵐ w ∂P,∀ r ∈ Icc 0 R,Z (w,r) = G (w,r)/(a*X (realTimeClamp r) w)) ∧
      ∀ t ∈ Icc 0 R,
        (fun w => Real.log (X (realTimeClamp R) w)/a) =ᵐ[P]
          fun w => Real.log (X (realTimeClamp t) w)/a-
            (∫ r in t..R,a/2*(Z (w,r))^2)+(N (realTimeClamp R) w-N (realTimeClamp t) w) := by
  dsimp only
  let ψ := logExtension b a
  let v : (Fin 2 → ℝ) → ℝ := fun x => ψ (x 1)
  have hψ := logExtension_contDiff b a hb 3
  have hv : ContDiff ℝ 2 v := (hψ.of_le (by norm_num)).comp (by fun_prop)
  have hd x := scalar_lift_derivatives ψ hψ x
  have hpde : ∀ᵐ w ∂P,∀ r,r ∈ Icc 0 R →
      fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ v) ![r,X (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*G (w,r)^2/2 +
      a/2*(fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r))^2 = 0 := by
    filter_upwards [hpos] with w hw
    intro r hr
    dsimp only [v]
    rw [(hd _).1,(hd _).2.1,(hd _).2.2]
    simp only [ψ,Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [(logExtension_derivatives b a _ hb (hw r hr)).2.1,
      (logExtension_derivatives b a _ hb (hw r hr)).2.2]
    have hxn : X (realTimeClamp r) w ≠ 0 := ne_of_gt (hb.trans_le (hw r hr))
    field_simp [ha,hxn]
    <;> ring
  obtain ⟨N,hN,hNI,he⟩ := nonlinear_feynman_kac_brownian P hT F hF hle hnull
    W A X M U₀ hX hW hA G hGm R hR hRT v hv (fun _ _ z => a/2*z^2) ψ
    (fun _ => rfl) hpde c hc hcm hcT hct hcut hcc hGi hclock hG hMG
  have hcoef (q x : ℝ) : fderiv ℝ v ![q,x] (Pi.single 1 1) = deriv ψ x := by
    simpa only [v,Matrix.cons_val_one,Matrix.cons_val_zero] using (hd ![q,x]).2.1
  refine ⟨N,hN,?_,?_,?_⟩
  · convert hNI using 1
    funext z
    rw [hcoef]
  · filter_upwards [hpos] with w hw
    intro r hr
    rw [(logExtension_derivatives b a _ hb (hw r hr)).2.1]
    ring
  intro t ht
  filter_upwards [he t ht,hpos] with w hw hp
  simp only [hcoef,v,Matrix.cons_val_one,Matrix.cons_val_zero] at hw
  dsimp only [ψ] at hw
  rw [(logExtension_derivatives b a _ hb (hp R ⟨hR,le_rfl⟩)).1,
    (logExtension_derivatives b a _ hb (hp t ht)).1] at hw
  exact hw

end Asakura.Chapter5
