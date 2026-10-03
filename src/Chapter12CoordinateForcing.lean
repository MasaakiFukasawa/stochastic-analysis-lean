import Chapter12RectangularDensityPositive
import Chapter6MappedDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinateForcing {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e:E ≃L[ℝ] F) (T:ℝ)
    (S:C(Icc (0:ℝ) T,F) → C(Icc (0:ℝ) T,F)) : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E) :=
  fun a => e.symm.toContinuousLinearMap.compLeftContinuous ℝ _ (S (e.toContinuousLinearMap.compLeftContinuous ℝ _ a))

theorem coordinate_forcing_continuous {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e:E ≃L[ℝ] F) (T:ℝ)
    (S:C(Icc (0:ℝ) T,F) → C(Icc (0:ℝ) T,F)) (hS:Continuous S) :
    Continuous (coordinateForcing e T S) :=
  (e.symm.toContinuousLinearMap.compLeftContinuous ℝ _).continuous.comp
    (hS.comp (e.toContinuousLinearMap.compLeftContinuous ℝ _).continuous)

theorem coordinate_forcing_equation {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (e:E ≃L[ℝ] F) (T:ℝ) (hT:0≤T)
    (b:F → F) (hb:Continuous b) (S:C(Icc (0:ℝ) T,F) → C(Icc (0:ℝ) T,F))
    (hSeq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT s))) :
    ∀a t,coordinateForcing e T S a t=a t+∫s in 0..t.val,
      e.symm (b (e (coordinateForcing e T S a (projIcc 0 T hT s)))) := by
  intro a t
  let a' := e.toContinuousLinearMap.compLeftContinuous ℝ _ a
  change e.symm (S a' t)=a t+∫s in 0..t.val,e.symm (b (e (e.symm (S a' (projIcc 0 T hT s)))))
  simp only [e.apply_symm_apply]
  rw [hSeq,map_add]
  have hi:IntervalIntegrable (fun s => b (S a' (projIcc 0 T hT s))) volume 0 t.val :=
    (hb.comp ((S a').continuous.comp continuous_projIcc)).intervalIntegrable _ _
  rw [show e.symm (a' t)=a t from e.symm_apply_apply (a t)]
  change a t+e.symm.toContinuousLinearMap (∫s in 0..t.val,b (S a' (projIcc 0 T hT s)))=_
  congr 1
  exact (e.symm.toContinuousLinearMap.intervalIntegral_comp_comm hi).symm

theorem euclidean_density_ofLp {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω) {n:ℕ}
    (X:Ω → EuclideanSpace ℝ (Fin n)) (hX:Measurable X)
    (p:EuclideanSpace ℝ (Fin n) → ℝ) (hp:Measurable p)
    (hmap:P.map X=volume.withDensity (fun y => ENNReal.ofReal (p y))) :
    P.map (fun w => WithLp.ofLp (X w))=volume.withDensity (fun y => ENNReal.ofReal (p (WithLp.toLp 2 y))) := by
  let e := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  change P.map (e ∘ X)=_
  rw [←Measure.map_map e.measurable hX,hmap]
  trans (volume.map e).withDensity (fun y => ENNReal.ofReal (p (e.symm y)))
  · exact Asakura.Chapter6.measurable_equiv_map_density volume e (fun y => ENNReal.ofReal (p y)) (ENNReal.measurable_ofReal.comp hp)
  rw [show (volume:Measure (EuclideanSpace ℝ (Fin n))).map e=volume from (PiLp.volume_preserving_ofLp (Fin n)).map_eq]
  rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.coordinate_forcing_equation
#print axioms Asakura.Chapter12.euclidean_density_ofLp
