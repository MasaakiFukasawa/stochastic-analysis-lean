import Chapter5NonlinearFeynmanKacUnit
import Chapter5SmoothExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Unit-diffusion Feynman--Kac with the same open-neighborhood
regularity supplied by the constructed Burgers formulas. -/
theorem nonlinear_feynman_kac_unit_open
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (v : (Fin 2 → ℝ) → ℝ) (O : Set (Fin 2 → ℝ)) (hO : IsOpen O)
    (hstrip : {p : Fin 2 → ℝ | p 0∈Icc 0 R} ⊆ O) (hv : ContDiffOn ℝ 2 v O)
    (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hterminal : ∀ x, v ![R,x] = g x)
    (hpde : ∀ r ∈ Icc 0 R, ∀ x,
      fderiv ℝ v ![r,x] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ v) ![r,x] (Pi.single 1 1) (Pi.single 1 1))/2 +
      f r (v ![r,x]) (fderiv ℝ v ![r,x] (Pi.single 1 1)) = 0)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → C (realTimeClamp r) w = r) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F X
        (fun z => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
          X (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ t ∈ Icc 0 R,
        (fun w => g (X (realTimeClamp R) w)) =ᵐ[P]
          fun w => v ![t,X (realTimeClamp t) w] -
            (∫ r in t..R, f r (v ![r,X (realTimeClamp r) w])
              (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1))) +
            (N (realTimeClamp R) w - N (realTimeClamp t) w) := by
  obtain ⟨u,hu,he⟩ := time_strip_C2_extension R O hO hstrip v hv
  have he' (r x : ℝ) (hr : r∈Icc 0 R) := he ![r,x] (by simpa using hr)
  have htu x : u ![R,x]=g x := (he' R x ⟨hR,le_rfl⟩).1.trans (hterminal x)
  have hpu : ∀ r∈Icc 0 R,∀ x,
      fderiv ℝ u ![r,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ u) ![r,x] (Pi.single 1 1) (Pi.single 1 1)/2+
      f r (u ![r,x]) (fderiv ℝ u ![r,x] (Pi.single 1 1))=0 := by
    intro r hr x
    rw [(he' r x hr).1,(he' r x hr).2.1,(he' r x hr).2.2]
    exact hpde r hr x
  obtain ⟨N,hN,hNI,hEq⟩ := nonlinear_feynman_kac_unit P hT F hF hle hnull X C hX hC
    R hR hRT u hu f g htu hpu c hc hcm hcT hcc hclock
  refine ⟨N,hN,?_,?_⟩
  · convert hNI using 1
    funext z
    rw [(he' _ _ (finitePrefixTime (T := T) R hR (realTimeClamp z.2)).property).2.1]
  · intro t ht
    filter_upwards [hEq t ht] with w hw
    rw [(he' t _ ht).1] at hw
    have hi : (∫ r in t..R,f r (u ![r,X (realTimeClamp r) w])
        (fderiv ℝ u ![r,X (realTimeClamp r) w] (Pi.single 1 1)))=
        ∫ r in t..R,f r (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.2] at hr
      have hrr : r∈Icc 0 R := ⟨ht.1.trans hr.1,hr.2⟩
      dsimp only
      rw [(he' r _ hrr).1,(he' r _ hrr).2.1]
    rwa [hi] at hw

end Asakura.Chapter5
