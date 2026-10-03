import Chapter12WienerQuadraticDivergence
import Chapter12DeterministicDivergenceClosedCore
import Chapter12DivergenceFiniteSumRaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The anticipating vector used in basket vega has precisely the printed
quadratic Wiener weight. All L2 integrability and domain membership follow
from the finite cylinder formulas. -/
theorem finite_wiener_vega_divergence {Ω H ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (e : ι → H) (k : H) (a : ℝ) :
    ∃ (hu : MemLp (fun w => a • (∑ i : ι,W (e i) w • e i)-k) 2 P)
      (hz : MemLp (fun w => a*(∑ i : ι, ((W (e i) w)^2-‖e i‖^2))-W k w) 2 P),
      IsDivergence D (hu.toLp _) (hz.toLp _) := by
  classical
  have hex (i : ι) := wiener_linear_direction_divergence P W S hS hcore D hg (e i) (e i)
  choose hi hzi hdi using hex
  have hzi' : ∀ i,MemLp (fun w => (W (e i) w)^2-‖e i‖^2) 2 P := by
    intro i
    simpa only [pow_two,real_inner_self_eq_norm_sq] using hzi i
  have hdi' : ∀ i,IsDivergence D ((hi i).toLp _) ((hzi' i).toLp _) := by
    intro i
    convert hdi i using 1
    apply Lp.ext
    filter_upwards [(hzi' i).coeFn_toLp,(hzi i).coeFn_toLp] with w h1 h2
    rw [h1,h2,real_inner_self_eq_norm_sq,pow_two]
  obtain ⟨hU,hZ,hD⟩ := divergence_finite_sum_raw P D _ _ hi hzi' hdi'
  obtain ⟨hUa,hZa,hDa⟩ := divergence_smul_raw P D _ _ hU hZ hD a
  let c : Lp H 2 P := (memLp_const k).toLp (fun _ => k)
  have hc := deterministic_divergence_closed_core P W S hS hcore D hg k
  let u : Lp H 2 P := hUa.toLp _-c
  let z : Lp ℝ 2 P := hZa.toLp _-W k
  have hu : (u : Ω → H)=ᵐ[P] (fun w => a • (∑ i : ι,W (e i) w • e i)-k) := by
    filter_upwards [Lp.coeFn_sub (hUa.toLp _) c,hUa.coeFn_toLp,
      (memLp_const k (μ := P) (p := 2)).coeFn_toLp] with w h1 h2 h3
    change (hUa.toLp _-c) w=_
    rw [h1]
    change hUa.toLp _ w-c w=_
    rw [h2,h3]
  have hz : (z : Ω → ℝ)=ᵐ[P] (fun w => a*(∑ i : ι, ((W (e i) w)^2-‖e i‖^2))-W k w) := by
    filter_upwards [Lp.coeFn_sub (hZa.toLp _) (W k),hZa.coeFn_toLp] with w h1 h2
    change (hZa.toLp _-W k) w=_
    rw [h1]
    change hZa.toLp _ w-W k w=_
    rw [h2]
  have huf := (Lp.memLp u).ae_eq hu
  have hzf := (Lp.memLp z).ae_eq hz
  refine ⟨huf,hzf,?_⟩
  have heu : huf.toLp _=u := Lp.ext (huf.coeFn_toLp.trans hu.symm)
  have hez : hzf.toLp _=z := Lp.ext (hzf.coeFn_toLp.trans hz.symm)
  rw [heu,hez]
  intro f
  change inner ℝ (D f) (hUa.toLp _-c)=inner ℝ (f : Lp ℝ 2 P) (hZa.toLp _-W k)
  rw [inner_sub_right,inner_sub_right,hDa f,hc f]

end Asakura.Chapter12
