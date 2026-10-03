import Chapter10MatrixIntegralPath
import Chapter10StateCoordinate

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def pathInformation {Ω : Type*} {d r : ℕ} (T : ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (κ : Fin r → Fin d) (s : Icc (0:ℝ) T) :
    MeasurableSpace Ω := MeasurableSpace.comap
      (fun w (z : {u : Icc (0:ℝ) T // u.val≤s.val} × Fin r) => X w z.1.val (κ z.2)) inferInstance

theorem path_information_mono {Ω : Type*} {d r : ℕ} (T : ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (κ : Fin r → Fin d)
    (s t : Icc (0:ℝ) T) (hst : s.val≤t.val) : pathInformation T X κ s≤pathInformation T X κ t := by
  letI : MeasurableSpace Ω := pathInformation T X κ t
  apply Measurable.comap_le
  apply Measurable.of_eval
  intro z
  exact (measurable_pi_apply (⟨z.1.val,z.1.property.trans hst⟩,z.2)).comp
    (show Measurable (fun w (q : {u : Icc (0:ℝ) T // u.val≤t.val} × Fin r) => X w q.1.val (κ q.2)) from
      Measurable.of_comap_le le_rfl)

theorem path_information_current {Ω : Type*} {d r : ℕ} (T : ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (κ : Fin r → Fin d)
    (s : Icc (0:ℝ) T) (j : Fin r) : Measurable[pathInformation T X κ s] (fun w => X w s (κ j)) :=
  (measurable_pi_apply ((⟨s,le_rfl⟩ : {u : Icc (0:ℝ) T // u.val≤s.val}),j)).comp
    (show Measurable[pathInformation T X κ s]
      (fun w (z : {u : Icc (0:ℝ) T // u.val≤s.val} × Fin r) => X w z.1.val (κ z.2)) from
      Measurable.of_comap_le le_rfl)

theorem LinearStateWitness.path_information_le {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n r : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (G : Fin d → Fin n → ℝ → ℝ) (ξ : Ω → Fin d → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) (κ : Fin r → Fin d) (s : Icc (0:ℝ) T) :
    nullAugmentedInformation (m := m) P (pathInformation T X κ s)≤B.F (realTimeClamp s.val) := by
  letI : MeasurableSpace Ω := m
  have ha u i := h.coordinate_adapted P B A G ξ T hT N X u i
  have hraw : pathInformation T X κ s≤B.F (realTimeClamp s.val) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp s.val)
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro z
    exact (ha z.1.val (κ z.2)).mono
      (B.mono (real_time_clamp_mono z.1.property)) le_rfl
  apply MeasurableSpace.generateFrom_le
  intro Q hQ
  exact hQ.elim (hraw Q) (fun hq => B.null _ Q hq.1 hq.2)

end Asakura.Chapter10
