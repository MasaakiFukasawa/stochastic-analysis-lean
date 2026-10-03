import Chapter12AsianMomentGraphs
import Chapter12CompactPrefixTimeKernel
import Chapter12BrownianDerivativeRealization

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The H-valued derivative of a stock-price time moment has precisely the
remaining-time kernel in the manuscript, for its actual Brownian coordinate. -/
theorem asian_moment_time_kernel {d : ℕ} (i : Fin (d+1))
    (T : ℝ) (hT : 0≤T) (x σ r : ℝ) (j : ℕ) (f : C(Icc (0:ℝ) T,ℝ)) :
    (finiteTimeToCompact T hT (brownianCoordinateProjection T i
      (asianMomentGradient T hT x σ r j (fun t => brownianTimeDirection (i,t)) f)) :
        Icc (0:ℝ) T → ℝ) =ᵐ[compactTimeMeasure T hT]
      (fun s => σ*∫ t in s.val..T,t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t)))) := by
  classical
  let a := fun t : ℝ => t^j*(x*Real.exp ((r-σ^2/2)*t+σ*f (projIcc 0 T hT t)))
  have ha : Continuous a := by unfold a;fun_prop
  have hav (t : Icc (0:ℝ) T) : a t.val=t.val^j*stockPathValue x σ r T f t := by
    simp only [a,stockPathValue,projIcc_val]
  have hgrad : asianMomentGradient T hT x σ r j (fun t => brownianTimeDirection (i,t)) f =
      singleCoordinateIsometry i
        (σ • ∫ t : Icc (0:ℝ) T,a t.val • finiteTimeIntervalVector T 0 t.val ∂compactTimeMeasure T hT) := by
    have hd (t : Icc (0:ℝ) T) : brownianTimeDirection (i,t)=
        singleCoordinateIsometry i (finiteTimeIntervalVector T 0 t.val) := rfl
    unfold asianMomentGradient
    simp only [hd]
    convert coordinate_integral_prefix i T hT a ha σ using 1
    congr 1
    funext t
    rw [hav]
  have hproj (v : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) :
      brownianCoordinateProjection T i (singleCoordinateIsometry i v)=v := by
    change (Pi.single (M := fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i v) i=v
    simp
  rw [hgrad,hproj,map_smul]
  have hk := compact_prefix_time_kernel T hT a ha
  filter_upwards [hk,Lp.coeFn_smul σ
    (finiteTimeToCompact T hT
      (∫ t : Icc (0:ℝ) T,a t.val • finiteTimeIntervalVector T 0 t.val ∂compactTimeMeasure T hT))]
    with s hs hc
  rw [hc,Pi.smul_apply,smul_eq_mul,hs]

end Asakura.Chapter12
