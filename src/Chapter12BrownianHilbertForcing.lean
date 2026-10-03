import Chapter12HilbertKernelForcing
import Chapter12BrownianKernelPolygonal

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def brownianKernelPath (d:ℕ) (T:ℝ) (i:Fin (d+1)) :
    C(Icc (0:ℝ) T,FiniteWienerHilbert d T) :=
  ⟨fun t => brownianTimeDirection (i,t),
    (brownian_time_direction_continuous d T).comp (continuous_const.prodMk continuous_id)⟩

theorem brownian_hilbert_forcing_error {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d:ℕ) (T:ℝ) (v:Fin (d+1) → E) (h:ℝ) (hh:0<h) (n:ℕ) (hn:0<n) (hnT:(n:ℝ)*h=T) :
    ‖hilbertKernelForcing (fun i => brownianKernelPolygonal d T i h n) v-
      hilbertKernelForcing (brownianKernelPath d T) v‖≤Real.sqrt h*(∑i,‖v i‖) := by
  apply hilbertKernelForcing_difference_bound _ _ v (Real.sqrt h) (Real.sqrt_nonneg _)
  intro i t
  exact (brownian_kernel_polygonal_bounds d T i h hh n hn hnT t).2

theorem brownian_hilbert_forcing_converges {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d:ℕ) (T:ℝ) (v:Fin (d+1) → E) (h:ℕ → ℝ) (n:ℕ → ℕ)
    (hh:∀m,0<h m) (hn:∀m,0<n m) (hnT:∀m,(n m:ℝ)*h m=T) (ht:Tendsto h atTop (𝓝 0)) :
    Tendsto (fun m => hilbertKernelForcing (fun i => brownianKernelPolygonal d T i (h m) (n m)) v)
      atTop (𝓝 (hilbertKernelForcing (brownianKernelPath d T) v)) := by
  have hnorm:Tendsto (fun m => ‖hilbertKernelForcing (fun i => brownianKernelPolygonal d T i (h m) (n m)) v-
      hilbertKernelForcing (brownianKernelPath d T) v‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => norm_nonneg (hilbertKernelForcing (fun i => brownianKernelPolygonal d T i (h m) (n m)) v-
      hilbertKernelForcing (brownianKernelPath d T) v))
      (fun m => brownian_hilbert_forcing_error d T v (h m) (hh m) (n m) (hn m) (hnT m))
    simpa using ((Real.continuous_sqrt.tendsto 0).comp ht).mul_const (∑i,‖v i‖)
  exact (tendsto_iff_norm_sub_tendsto_zero (E:=FiniteWienerHilbert d T →L[ℝ] C(Icc (0:ℝ) T,E))
    (f:=fun m => hilbertKernelForcing (fun i => brownianKernelPolygonal d T i (h m) (n m)) v)
    (b:=hilbertKernelForcing (brownianKernelPath d T) v)).mpr hnorm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_hilbert_forcing_converges
