import IncrementGluing
import PowerMomentModification
import GluedGaussian

open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace Asakura

theorem half_line_power_modification {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hX0 : X 0 =ᵐ[P] (fun _ => 0)) (H : ℝ) (hH : 0 < H)
    (hbound : ∀ p : ℝ≥0, 1 ≤ p → ∃ c : ℝ, 0 ≤ c ∧ ∀ s t,
      eLpNorm (X s-X t) p P ≤ ENNReal.ofReal (c*(dist s t)^H)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by
  classical
  have hex (k : ℕ) : ∃ Z : UnitCube 1 → Ω → ℝ,
      (∀ s, Measurable (Z s)) ∧ (∀ ω, Continuous (fun s => Z s ω)) ∧
      (∀ ω, Z cubeZero ω = 0) ∧
      (∀ s, Z s =ᵐ[P] (fun ω => X (intervalTime k s) ω-X k ω)) := by
    let U : UnitCube 1 → Ω → ℝ := fun s ω => X (intervalTime k s) ω-X k ω
    have hU0 : U cubeZero = fun _ => 0 := by funext ω; simp [U,intervalTime_zero]
    have hUm (s : UnitCube 1) : Measurable (U s) := (hX _).sub (hX _)
    have hb : ∀ p : ℝ≥0, 1 ≤ p → ∃ c : ℝ, 0 ≤ c ∧ ∀ s t,
        eLpNorm (U s-U t) p P ≤ ENNReal.ofReal (c*(dist s t)^H) := by
      intro p hp
      obtain ⟨c,hc,hb⟩ := hbound p hp
      refine ⟨c,hc,?_⟩
      intro s t
      have he : U s-U t = X (intervalTime k s)-X (intervalTime k t) := by
        funext ω; dsimp [U]; ring
      rw [he]
      simpa only [intervalTime_distance] using hb (intervalTime k s) (intervalTime k t)
    obtain ⟨V,hVm,hVc,hVU⟩ := power_moment_cube_modification P U hUm H hH hb
    let Z : UnitCube 1 → Ω → ℝ := fun s ω => V s ω-V cubeZero ω
    refine ⟨Z,fun s => (hVm s).sub (hVm _),
      fun ω => (hVc ω).sub continuous_const,fun ω => sub_self _,?_⟩
    intro s
    filter_upwards [hVU s,hVU cubeZero] with ω hs h0
    change V s ω-V cubeZero ω = _
    rw [hs,h0,hU0]
    exact sub_zero _
  choose Z hZm hZc hZ0 hZX using hex
  let W : (ℕ × UnitCube 1) → Ω → ℝ := fun p => Z p.1 p.2
  let Y : ℝ≥0 → Ω → ℝ := fun t => gluedProcess W t
  refine ⟨Y,fun t => glued_process_measurable W (fun p => hZm p.1 p.2) hZ0 t,?_,?_⟩
  · intro ω
    exact (gluedPath_continuous (fun k s => Z k s ω) (fun k => hZ0 k ω)
      (fun k => hZc k ω)).comp continuous_subtype_val
  · intro t
    obtain ⟨N,hN⟩ := exists_nat_gt (t:ℝ)
    have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, Z k (unitTimeCube k t) ω =
        X (intervalTime k (unitTimeCube k t)) ω-X k ω :=
      ae_all_iff.mpr (fun k => hZX k (unitTimeCube k t))
    filter_upwards [hall,hX0] with ω hω h0
    change gluedPath (fun k s => Z k s ω) t = X t ω
    rw [gluedPath_eq_sum _ (fun k => hZ0 k ω) N t hN.le]
    simp_rw [hω]
    rw [clamped_increment_sum (fun t => X t ω) N t (by exact_mod_cast hN.le),h0,sub_zero]
end Asakura
