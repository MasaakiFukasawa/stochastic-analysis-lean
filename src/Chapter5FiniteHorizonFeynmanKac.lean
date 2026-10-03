import Chapter5FiniteIntegralExtension
import Chapter5InitialPlusIntegral
import Chapter5NonlinearFeynmanKacOpen

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon diffusion and nonlinear Feynman--Kac: the integrand is
assumed integrable only through the manuscript's terminal time R.
Zero extension constructs the ambient semimartingale used by Ito's formula. -/
theorem finite_horizon_nonlinear_feynman_kac
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hGi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)^2) volume 0 R)
    (U : Ω → ℝ) (hU : Measurable[F ⊥] U) :
    ∃ M : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F M ∧
      ItoCovarianceFormula P F W (fun z => (Iic R).indicator (fun r => G (z.1,r)) z.2) M ∧
      ∀ (v : (Fin 2 → ℝ) → ℝ) (O : Set (Fin 2 → ℝ)),
        IsOpen O → {x : Fin 2 → ℝ | x 0∈Icc 0 R} ⊆ O → ContDiffOn ℝ 2 v O →
        ∀ (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ),
        (∀ x,v ![R,x]=g x) →
        (∀ w r,r∈Icc 0 R →
          fderiv ℝ v ![r,U w+M (realTimeClamp r) w] (Pi.single 0 1)+
          (fderiv ℝ (fderiv ℝ v) ![r,U w+M (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*G (w,r)^2/2+
          f r (v ![r,U w+M (realTimeClamp r) w])
            (fderiv ℝ v ![r,U w+M (realTimeClamp r) w] (Pi.single 1 1)*G (w,r))=0) →
        ∃ N : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F N ∧
          ItoCovarianceFormula P F W
            (fun z => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
              U z.1+M (realTimeClamp z.2) z.1] (Pi.single 1 1)*
              ((Iic R).indicator (fun r => G (z.1,r)) z.2)) N ∧
          (∀ t∈Icc 0 R,(fun w => g (U w+M (realTimeClamp R) w)) =ᵐ[P]
            fun w => v ![t,U w+M (realTimeClamp t) w]-
              (∫ r in t..R,f r (v ![r,U w+M (realTimeClamp r) w])
                (fderiv ℝ v ![r,U w+M (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)))+
              (N (realTimeClamp R) w-N (realTimeClamp t) w)) := by
  obtain ⟨M,hM,hMI,hHm,hHp,hHi,hHG⟩ := finite_path_energy_integral_extension P hT F hF hle hnull
    W A hW hA c hc hcm hcT hct hcut hcc hclock R hR G hGm hGp hGi
  let H := fun z : Ω × ℝ => (Iic R).indicator (fun r => G (z.1,r)) z.2
  let X := fun t w => U w+M t w
  have hX := initial_plus_local_integral_semimartingale P hT F hF U hU M hM
  refine ⟨M,hM,hMI,?_⟩
  intro v O hO hstrip hv f g hterm hpde
  have hp : ∀ w r,r∈Icc 0 R →
      fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 0 1)+
      (fderiv ℝ (fderiv ℝ v) ![r,X (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*H (w,r)^2/2+
      f r (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*H (w,r))=0 := by
    intro w r hr
    rw [show H (w,r)=G (w,r) from hHG w r hr]
    exact hpde w r hr
  obtain ⟨N,hN,hNI,he⟩ := nonlinear_feynman_kac_open_neighborhood P hT F hF hle hnull
    W A X M U hX hW hA H (fun w => hHm.comp measurable_prodMk_left) R hR hRT
    v O hO hstrip hv f g hterm hp c hc hcm hcT hct hcut hcc hHi hclock hHp hMI
  refine ⟨N,hN,hNI,?_⟩
  intro t ht
  filter_upwards [he t ht] with w hw
  have hi : (∫ r in t..R,f r (v ![r,X (realTimeClamp r) w])
      (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*H (w,r))) =
      ∫ r in t..R,f r (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.2] at hr
    dsimp only
    rw [show H (w,r)=G (w,r) from hHG w r ⟨ht.1.trans hr.1,hr.2⟩]
  rw [hi] at hw
  exact hw

end Asakura.Chapter5
