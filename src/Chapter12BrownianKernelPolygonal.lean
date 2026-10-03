import Chapter12BrownianDirectionPairing
import Chapter12PolygonalCellData

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianKernelPolygonal (d : ℕ) (T : ℝ) (i : Fin (d+1)) (h : ℝ) (n : ℕ) :
    C(Icc (0:ℝ) T,FiniteWienerHilbert d T) :=
  ⟨fun t => singleCoordinateIsometry i (polygonalPath (fun s => finiteTimeIntervalVector T 0 s) h n t.val),
    (singleCoordinateIsometry i).continuous.comp ((polygonalPath_continuous _ h n).comp continuous_subtype_val)⟩

theorem brownian_kernel_polygonal_bounds (d : ℕ) (T : ℝ) (i : Fin (d+1))
    (h : ℝ) (hh : 0<h) (n : ℕ) (hn : 0<n) (hT : (n:ℝ)*h=T) (t : Icc (0:ℝ) T) :
    ‖brownianKernelPolygonal d T i h n t‖≤Real.sqrt T ∧
    ‖brownianKernelPolygonal d T i h n t-brownianTimeDirection (i,t)‖≤Real.sqrt h := by
  let J := singleCoordinateIsometry (H:=Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i
  obtain ⟨l,r,a,ha,ha1,hlt,htr,hw,heq⟩ := polygonal_cell_data (fun s => finiteTimeIntervalVector T 0 s) T h hh n hn hT t
  constructor
  · change ‖J (polygonalPath (fun s => finiteTimeIntervalVector T 0 s) h n t.val)‖≤_
    rw [J.norm_map,heq]
    exact interpolation_kernel_norm T l r a ha ha1
  · change ‖J (polygonalPath (fun s => finiteTimeIntervalVector T 0 s) h n t.val)-J (finiteTimeIntervalVector T 0 t.val)‖≤_
    rw [←map_sub,J.norm_map,heq]
    exact (interpolation_kernel_error T l t r hlt htr a ha ha1).trans (Real.sqrt_le_sqrt hw)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_kernel_polygonal_bounds
