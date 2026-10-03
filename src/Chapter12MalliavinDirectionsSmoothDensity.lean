import Chapter12AllSobolevIBPWeights
import Chapter12MalliavinCharacteristicStep
import Chapter12WeightedIBPDensity

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

theorem malliavin_directions_smooth_density {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hd:DenseRange (fun f:D.domain => (f:Lp ℝ 2 P)))
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (d:ℕ) (F:Fin (d+1) → Lp ℝ 2 P) (U:Fin (d+1) → Lp H 2 P)
    (hFU:∀j,(F j,U j)∈D.graph) (A:Fin (d+1) → Ω → H)
    (hA:∀i,HasAllVectorSobolevJets H P W S hS hcore (A i))
    (hdual:∀i j,∀ᵐw∂P,inner ℝ (U j w) (A i w)=if i=j then 1 else 0) :
    let f:Ω → EuclideanSpace ℝ (Fin (d+1)) := fun w => WithLp.toLp 2 (fun i => F i w)
    ∃p:EuclideanSpace ℝ (Fin (d+1)) → ℝ,ContDiff ℝ ∞ p ∧ (∀x,0≤p x) ∧
      P.map f=volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
  classical
  let f:Ω → EuclideanSpace ℝ (Fin (d+1)) := fun w => WithLp.toLp 2 (fun i => F i w)
  have hf:Measurable f := (PiLp.continuous_toLp 2 (fun _:Fin (d+1) => ℝ)).measurable.comp
    (measurable_pi_lambda (fun i => (Lp.stronglyMeasurable (F i)).measurable))
  have hw:∀i,∃Z:ℕ → Lp ℝ 2 P,
      (Z 0:Ω → ℝ)=ᵐ[P] (fun _ => 1) ∧
      (∀k,HasAllSobolevJets H P W S hS hcore (Z k)) ∧
      ∀k,∃B:Lp H 2 P,(B:Ω → H)=ᵐ[P] (fun w => Z k w • A i w) ∧ IsDivergence D B (Z (k+1)) :=
    fun i => all_sobolev_iterated_weights H P W S hS hcore D hg hd hdense (A i) (hA i)
  choose Z hZ0 hZ hstep using hw
  apply weighted_ibp_smooth_density P d f hf (fun k i w => Z i k w)
  intro k ξ i
  have hinner:∀w,inner ℝ ξ (f w)=∑j,ξ j*F j w := by
    intro w
    simp [f,PiLp.inner_apply,RCLike.inner_apply,mul_comm]
  simp only [hinner,Complex.ofReal_sum,Complex.ofReal_mul]
  induction k with
  | zero =>
    simp only [pow_zero,one_mul]
    apply integral_congr_ae
    filter_upwards [hZ0 i] with w hw
    rw [hw]
    simp
  | succ k ih =>
    obtain ⟨B,hB,hBZ⟩ := hstep i k
    have hh := malliavin_characteristic_step P W S hS hcore D hD hg F U hFU (A i) i (hdual i)
      (Z i k) (Z i (k+1)) B hB hBZ (fun j => ξ j)
    rw [hh,← ih,pow_succ]
    ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.malliavin_directions_smooth_density
