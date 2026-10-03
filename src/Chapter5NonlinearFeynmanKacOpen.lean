import Chapter5NonlinearFeynmanKacBrownian
import Chapter5SmoothExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's open-neighborhood C² assumption suffices. The smooth
extension and agreement of both derivatives on the entire time strip are
proved, rather than strengthening regularity to a global assumption. -/
theorem nonlinear_feynman_kac_open_neighborhood
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
    (v : (Fin 2 → ℝ) → ℝ)
    (O : Set (Fin 2 → ℝ)) (hO : IsOpen O)
    (hstrip : {x : Fin 2 → ℝ | x 0 ∈ Icc 0 R} ⊆ O)
    (hv : ContDiffOn ℝ 2 v O)
    (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hterminal : ∀ x, v ![R,x] = g x)
    (hpde : ∀ w r, r ∈ Icc 0 R →
      fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ v) ![r,X (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*G (w,r)^2/2 +
      f r (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)) = 0)
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
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
          X (realTimeClamp z.2) z.1] (Pi.single 1 1)*G z) N ∧
      ∀ t ∈ Icc 0 R,
        (fun w => g (X (realTimeClamp R) w)) =ᵐ[P]
          fun w => v ![t,X (realTimeClamp t) w] -
            (∫ r in t..R, f r (v ![r,X (realTimeClamp r) w])
              (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r))) +
            (N (realTimeClamp R) w - N (realTimeClamp t) w) := by
  obtain ⟨u,hu,heu⟩ := time_strip_C2_extension R O hO hstrip v hv
  have he (r x : ℝ) (hr : r ∈ Icc 0 R) := heu ![r,x] (by simpa using hr)
  have htermu x : u ![R,x] = g x := (he R x ⟨hR,le_rfl⟩).1.trans (hterminal x)
  have hpdeu w r (hr : r ∈ Icc 0 R) :
      fderiv ℝ u ![r,X (realTimeClamp r) w] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ u) ![r,X (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*G (w,r)^2/2 +
      f r (u ![r,X (realTimeClamp r) w])
        (fderiv ℝ u ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)) = 0 := by
    rw [(he r _ hr).1,(he r _ hr).2.1,(he r _ hr).2.2]
    exact hpde w r hr
  obtain ⟨N,hN,hNI,hEq⟩ := nonlinear_feynman_kac_brownian P hT F hF hle hnull
    W A X M U₀ hX hW hA G hGm R hR hRT u hu f g htermu (ae_of_all _ hpdeu)
    c hc hcm hcT hct hcut hcc hGi hclock hG hMG
  refine ⟨N,hN,?_,?_⟩
  · convert hNI using 1
    funext z
    rw [(he _ _ (finitePrefixTime (T := T) R hR (realTimeClamp z.2)).property).2.1]
  intro t ht
  filter_upwards [hEq t ht] with w hw
  rw [(he t _ ht).1] at hw
  have hint : (∫ r in t..R,f r (u ![r,X (realTimeClamp r) w])
      (fderiv ℝ u ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r))) =
      ∫ r in t..R,f r (v ![r,X (realTimeClamp r) w])
      (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.2] at hr
    have hrr : r ∈ Icc 0 R := ⟨ht.1.trans hr.1,hr.2⟩
    dsimp only
    rw [(he r _ hrr).1,(he r _ hrr).2.1]
  rw [hint] at hw
  exact hw

end Asakura.Chapter5
