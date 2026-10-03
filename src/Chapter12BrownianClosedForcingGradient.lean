import Chapter12ClosedForcingGradient
import Chapter12BrownianForcingHilbertFrames
import Chapter12BrownianHilbertForcing
import Chapter12BrownianForcingPathConvergence
import Chapter12BrownianForcingSolutionLp

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem brownian_closed_forcing_gradient {Ω:Type*} {E:Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] (d:ℕ) (T:ℝ) (hT:0<T)
    [Nontrivial (FiniteWienerHilbert d T)]
    (W:FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW:∀u,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B:BrownianTimeCoordinates d T → Ω → ℝ)
    (hB:∀z,B z=ᵐ[P] (W (brownianTimeDirection z):Ω → ℝ))
    (Y:Ω → C(Icc (0:ℝ) T,Fin (d+1) → ℝ)) (hYm:Measurable Y)
    (hY:∀w t i,Y w t i=B (i,t) w) (hY2:MemLp Y 2 P)
    (v:Fin (d+1) → E) (x:E) (b:E → E) (K:ℝ≥0) (hb:LipschitzWith K b)
    (S:C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS:ContDiff ℝ ∞ S)
    (hSeq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (hSB:∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀a,‖iteratedFDeriv ℝ k S a‖≤C)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W univ dense_univ (fun u _ => hW u) 2 (by simp))))
    (ell:E →L[ℝ] ℝ) (t:Icc (0:ℝ) T) :
    let a:Ω → C(Icc (0:ℝ) T,E) := fun w => ContinuousMap.const _ x+
      (columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w)
    let R := hilbertKernelForcing (brownianKernelPath d T) v
    ∃F:Lp ℝ 2 P,∃hU:MemLp (fun w => forcingGradient S (a w) R ell t) 2 P,
      (F:Ω → ℝ)=ᵐ[P] (fun w => ell (S (a w) t)) ∧ (F,hU.toLp _)∈D.graph := by
  intro a R
  let n := fun i:ℕ => i+1
  let h := fun i:ℕ => T/(i+1:ℕ)
  have hn i:0<n i := Nat.succ_pos i
  have hh i:0<h i := div_pos hT (by positivity)
  have hnT i:(n i:ℝ)*h i=T := by dsimp [n,h];field_simp
  have hl:Tendsto h atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat T)
  have hframe i := brownian_forcing_hilbert_frames P d T hT W B hB v (h i) (h i)
    (hh i) (hh i) (n i) (n i) (hnT i) (hnT i)
  choose N e he hfact hfact' hrep hrep' using hframe
  let L := fun i => kernelForcingPath (e i) (fun j => brownianKernelPolygonal d T j (h i) (n i)) v
  let Rn := fun i => hilbertKernelForcing (fun j => brownianKernelPolygonal d T j (h i) (n i)) v
  let a0 := ContinuousMap.const (Icc (0:ℝ) T) x
  have hj i := forcing_gaussian_jet T S hS hSB (N i+1) (L i) a0 ell t
  choose f hf using hj
  obtain ⟨V,Z,hV,hZ,hlim⟩ := brownian_forcing_solution_Lp P d T hT.le B Y hYm hY 2 (by simp) hY2
    v x b K hb S hSeq n h hn hh hnT hl
  let ev := ell.comp (ContinuousMap.evalCLM ℝ t)
  let F := ev.compLp Z
  have hcv i:((f i).toCylinder (e i)).valueLp P W univ dense_univ (fun u _ => hW u) 2 (by simp)=ev.compLp (V i) := by
    apply Lp.ext
    filter_upwards [((f i).toCylinder (e i)).value_memLp P W univ dense_univ (fun u _ => hW u) 2 (by simp) |>.coeFn_toLp,
      ev.coeFn_compLp (V i),hrep i,hV i] with w hc hev hr hv
    change ((f i).toCylinder (e i)).valueLp P W univ dense_univ (fun u _ => hW u) 2 (by simp) w=
      ((f i).toCylinder (e i)).value P W w at hc
    rw [hc,hev,hv]
    change (f i).f (fun j => W (e i j) w)=_
    rw [hf]
    change ell (S (a0+L i (fun j => W (e i j) w)) t)=_
    rw [show L i (fun j => W (e i j) w)=_ from hr]
    rfl
  have hFlim:Tendsto (fun i => ((f i).toCylinder (e i)).valueLp P W univ dense_univ (fun u _ => hW u) 2 (by simp)) atTop (𝓝 F) := by
    simp_rw [hcv]
    exact ((ev.compLpL 2 P).continuous.tendsto Z).comp hlim
  have ham:AEStronglyMeasurable a P :=
    (continuous_const.add ((columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T)).continuous).comp_aestronglyMeasurable hY2.aestronglyMeasurable
  have ha:∀ᵐw∂P,Tendsto (fun i => a0+L i (fun j => W (e i j) w)) atTop (𝓝 (a w)) := by
    filter_upwards [ae_all_iff.mpr hrep] with w hw
    have ht := (tendsto_const_nhds (x:=a0)).add
      (brownian_forcing_path_convergence d T hT.le B Y hY v n h hn hh hnT hl w)
    simpa only [L,hw] using ht
  obtain ⟨C,hC,hCb⟩ := hSB 1 le_rfl
  have hCb':∀a,‖fderiv ℝ S a‖≤C := by simpa only [norm_iteratedFDeriv_one] using hCb
  obtain ⟨hU,hFU⟩ := closed_forcing_gradient P W univ dense_univ (fun u _ => hW u) D hD hg
    S hS C hC hCb' ell t a0 (fun i => N i+1) e L Rn R hfact
    (brownian_hilbert_forcing_converges d T v h n hh hn hnT hl) a ham ha f hf F hFlim
  refine ⟨F,hU,?_,hFU⟩
  filter_upwards [ev.coeFn_compLp Z,hZ] with w hw hz
  change F w=ev (Z w) at hw
  rw [hw,hz]
  rfl
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_closed_forcing_gradient
