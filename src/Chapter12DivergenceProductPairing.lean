import Chapter12DivergenceRawPairing
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

/-- Expanding the derivative of FG in the adjoint identity gives the
product correction, with all split integrals justified by Holder. -/
theorem divergence_product_pairing {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (F G Z : Ω → ℝ) (DF DG U : Ω → H)
    (hF : MemLp F 2 P) (hDF : MemLp DF 2 P)
    (hGU : MemLp (fun w => G w • U w) 2 P)
    (hGZ : MemLp (fun w => G w*Z w) 2 P)
    (hDU : MemLp (fun w => inner ℝ (DG w) (U w)) 2 P)
    (hp : (∫ w,inner ℝ (G w • DF w+F w • DG w) (U w) ∂P)=
      ∫ w,(F w*G w)*Z w ∂P) :
    (∫ w,inner ℝ (DF w) (G w • U w) ∂P)=
      ∫ w,F w*(G w*Z w-inner ℝ (DG w) (U w)) ∂P := by
  let A := fun w => inner ℝ (DF w) (G w • U w)
  let B := fun w => F w*inner ℝ (DG w) (U w)
  let R := fun w => F w*(G w*Z w)
  have hA : Integrable A P := memLp_one_iff_integrable.mp
    ((innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).memLp_of_bilin 1 hDF hGU)
  have hB : Integrable B P := memLp_one_iff_integrable.mp (hF.mul hDU)
  have hR : Integrable R P := memLp_one_iff_integrable.mp (hF.mul hGZ)
  have he : (∫ w,A w+B w ∂P)=∫ w,R w ∂P := by
    calc
      _=(∫ w,inner ℝ (G w • DF w+F w • DG w) (U w) ∂P) := by
        apply integral_congr_ae
        exact ae_of_all P (fun w => by simp only [A,B,inner_add_left,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial])
      _=(∫ w,(F w*G w)*Z w ∂P) := hp
      _=_ := integral_congr_ae (ae_of_all P (fun w => by dsimp [R]; ring))
  rw [integral_add hA hB] at he
  calc
    _=(∫ w,R w ∂P)-(∫ w,B w ∂P) := by linarith
    _=∫ w,R w-B w ∂P := (integral_sub hR hB).symm
    _=_ := integral_congr_ae (ae_of_all P (fun w => by dsimp [R,B]; ring))

end Asakura.Chapter12
