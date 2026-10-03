import Chapter12PrefixKernelIntegrable
import Chapter12BrownianHilbertForcing
import Chapter12BrownianDerivativeRealization

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem clamped_prefix_L2_kernel (T:ℝ) (hT:0≤T) (a:ℝ → ℝ) (ha:Continuous a) :
    ((∫s in 0..T,a s • finiteTimeIntervalVector T 0 (projIcc 0 T hT s).val : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))):ℝ → ℝ)=ᵐ[
      (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] (fun r => ∫s in r..T,a s) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc: IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn ha.continuousOn
  have hC0:0≤C := (norm_nonneg (a 0)).trans (hC 0 ⟨le_rfl,hT⟩)
  have he:(∫s in 0..T,a s • finiteTimeIntervalVector T 0 (projIcc 0 T hT s).val)=
      ∫s in Ioc (0:ℝ) T,a s • finiteTimeIntervalVector T 0 s := by
    rw [intervalIntegral.integral_of_le hT]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [projIcc_of_mem hT ⟨hs.1.le,hs.2⟩]
  rw [he]
  exact bounded_integrated_prefix_L2_kernel T a ha.measurable C hC0 (fun s hs => hC s ⟨hs.1.le,hs.2⟩)

theorem brownian_coordinate_weighted_prefix {d:ℕ} (T:ℝ) (t:Icc (0:ℝ) T)
    (c:Fin (d+1) → ℝ) (i:Fin (d+1)) :
    brownianCoordinateProjection T i (∑j,c j • brownianTimeDirection (j,t))=
      c i • finiteTimeIntervalVector T 0 t.val := by
  classical
  simp only [map_sum,map_smul,brownianCoordinateProjection,brownianTimeDirection,PiLp.proj_apply]
  change (∑j,c j • (Pi.single j (finiteTimeIntervalVector T 0 t.val):Fin (d+1) → _) i)=_
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne (Ne.symm hji),smul_zero]
  · simp

theorem brownian_integral_prefix_coordinate {d:ℕ} (T:ℝ) (hT:0≤T)
    (a:Fin (d+1) → ℝ → ℝ) (ha:∀j,Continuous (a j)) (i:Fin (d+1)) :
    brownianCoordinateProjection T i (∫s in 0..T,∑j,a j s • brownianTimeDirection (j,projIcc 0 T hT s))=
      ∫s in 0..T,a i s • finiteTimeIntervalVector T 0 (projIcc 0 T hT s).val := by
  let f := fun s => ∑j,a j s • brownianTimeDirection (j,projIcc 0 T hT s)
  have hc:Continuous f := continuous_finsetSum _ (fun j _ => (ha j).smul
    ((brownianKernelPath d T j).continuous.comp continuous_projIcc))
  have he := (brownianCoordinateProjection T i).intervalIntegral_comp_comm (hc.intervalIntegrable (μ:=volume) 0 T)
  change (∫s in 0..T,brownianCoordinateProjection T i (f s))=brownianCoordinateProjection T i (∫s in 0..T,f s) at he
  rw [←he]
  apply intervalIntegral.integral_congr
  intro s _
  exact brownian_coordinate_weighted_prefix T _ _ i
end Asakura.Chapter12
#print axioms Asakura.Chapter12.clamped_prefix_L2_kernel
#print axioms Asakura.Chapter12.brownian_integral_prefix_coordinate
