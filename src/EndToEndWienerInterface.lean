import EndToEndL2Restriction
import Chapter12VectorWienerExists
import Chapter12WienerCoordinates
import Chapter12SingleCoordinateIsometry

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.EndToEnd
open Asakura.Chapter12 Asakura.Chapter4

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Retain the actual maps when packaging their Gaussian and isometry laws. -/
theorem wiener_interface_from_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : PiLp 2 (fun _ : Fin 2 => Lp ℝ 2 (volume.restrict (Ioi (0 : ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ f, HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2, sq_nonneg _⟩) P) :
    ∃ I : Asakura.IndependentWienerIntegrals P,
      (∀ f, I.first f = W (singleCoordinateIsometry (0 : Fin 2)
        (L2Restriction volume (Ioi 0) f))) ∧
      (∀ f, I.second f = W (singleCoordinateIsometry (1 : Fin 2)
        (L2Restriction volume (Ioi 0) f))) := by
  classical
  let R := L2Restriction (volume : Measure ℝ) (Ioi 0)
  let J (i : Fin 2) := singleCoordinateIsometry
    (H := Lp ℝ 2 (volume.restrict (Ioi (0 : ℝ)))) i
  let A (i : Fin 2) := W.toContinuousLinearMap.comp ((J i).toContinuousLinearMap.comp R)
  have hm (i : Fin 2) (f : Lp ℝ 2 (volume : Measure ℝ)) :
      (∫ ω, A i f ω ∂P) = 0 := by
    change (∫ ω, W (J i (R f)) ω ∂P) = 0
    simpa only [integral_id_gaussianReal] using (hW (J i (R f))).integral_eq
  refine ⟨{
    first := A 0
    second := A 1
    mean_first := hm 0
    mean_second := hm 1
    inner_sum := ?_
    gaussian := ?_ }, ?_, ?_⟩
  · intro f g f' g' hf hg hf' hg'
    change inner ℝ (W (J 0 (R f)) + W (J 1 (R g)))
      (W (J 0 (R f')) + W (J 1 (R g'))) = _
    rw [← map_add, ← map_add, W.inner_map_map]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp only [J, singleCoordinateIsometry, PiLp.add_apply,
      LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_apply]
    norm_num
    exact congrArg₂ (· + ·) (positive_restriction_inner f f' hf hf')
      (positive_restriction_inner g g' hg hg')
  · constructor
    intro S
    let v (q : S) := Sum.elim (fun f => J 0 (R f)) (fun g => J 1 (R g)) q.val
    let e := Fintype.equivFin S
    have h := wiener_joint_gaussian P W hW (fun k => v (e.symm k))
    let L : (Fin (Fintype.card S) → ℝ) →L[ℝ] (S → ℝ) :=
      ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))
    convert h.map L using 1
    ext ω q
    change Sum.elim (fun f => (A 0 f : Ω → ℝ)) (fun g => (A 1 g : Ω → ℝ)) q.val ω =
      W (v (e.symm (e q))) ω
    rw [e.symm_apply_apply]
    dsimp only [v]
    cases q.val <;> rfl
  · intro f; rfl
  · intro f; rfl

/-- Construction on the probability space of the supplied Brownian system. -/
theorem independent_wiener_integrals_exist {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 2) :
    Nonempty (Asakura.IndependentWienerIntegrals P) := by
  obtain ⟨W, hW, _⟩ := vector_actual_wiener_isometry_exists P B
  obtain ⟨I, _, _⟩ := wiener_interface_from_isometry P W hW
  exact ⟨I⟩

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.independent_wiener_integrals_exist

#print axioms Asakura.EndToEnd.wiener_interface_from_isometry
