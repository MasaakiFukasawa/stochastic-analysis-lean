import Chapter12DivergenceSobolevExtension
import Chapter12SumJetExponentTransfer
import Chapter12EvenExponentChoice

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000

/-- All vector Sobolev orders use the actual completed finite-sum jets. -/
def HasAllVectorSobolevJets {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (U : Ω → H) : Prop :=
  ∀ (p : ℝ≥0∞) (hp1 : 1≤p) (hp : p≠⊤) (k : ℕ),
    letI : Fact (1≤p) := ⟨hp1⟩
    ∃ x : vectorSobolevJetSpace H P W S hS hcore p hp k,
      (x.val 0 : Ω → H)=ᵐ[P] U

/-- D-infinity is preserved by the actual closed divergence. Every
output Sobolev jet is constructed by the finite estimates and completion,
then identified with the same L2 adjoint by uniqueness. -/
theorem divergence_all_sobolev_orders {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D₀ : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D₀.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hd : DenseRange (fun f : D₀.domain => (f : Lp ℝ 2 P)))
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (U : Lp H 2 P) (hU : HasAllVectorSobolevJets H P W S hS hcore U) :
    ∃ Z : Lp ℝ 2 P,IsDivergence D₀ U Z ∧ HasAllSobolevJets H P W S hS hcore Z := by
  have hev (p : ℕ) (hp : 0<p) (k : ℕ) :
      letI : Fact (1≤((2*p:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*p by omega)⟩
      ∃ y : (Submodule.span ℝ (range (scalarSobolevSumCoreJet H P W S hS hcore
        (2*p:ℕ) (ENNReal.natCast_ne_top _) k))).topologicalClosure,
        IsDivergence D₀ U (probabilityLpInclusion P 2 (2*p:ℕ)
          (by exact_mod_cast (show 2≤2*p by omega)) (y.val 0)) := by
    letI : Fact (1≤((2*p:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*p by omega)⟩
    let q := ENNReal.conjExponent (2*p:ℕ)
    obtain ⟨hq1,hq⟩ := even_conjugate_properties p hp
    letI : Fact (1≤q) := ⟨hq1⟩
    have h2p : (2:ℝ≥0∞)≤(2*p:ℕ) := by exact_mod_cast (show 2≤2*p by omega)
    obtain ⟨x,hx⟩ := hU (2*p:ℕ) (Fact.out) (ENNReal.natCast_ne_top _) (k+2*p)
    obtain ⟨y,hy,_⟩ := divergence_sobolev_jet_extension H P W S hS hcore D₀ hgraph hd
      p hp h2p q hq (hdense q hq) k x
    have he : probabilityLpInclusion P 2 (2*p:ℕ) h2p (x.val 0)=U := by
      apply Lp.ext
      exact (probabilityLpInclusion_coe P 2 (2*p:ℕ) h2p (x.val 0)).trans hx
    exact ⟨y,(congrArg (fun v : Lp H 2 P => IsDivergence D₀ v
      (probabilityLpInclusion (E:=ℝ) P 2 (2*p:ℕ) h2p (y.val 0))) he).mp hy⟩
  letI : Fact (1≤((2*1:ℕ):ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨y₀,hy₀⟩ := hev 1 (by omega) 0
  let Z : Lp ℝ 2 P := probabilityLpInclusion P 2 (2*1:ℕ) (by norm_num) (y₀.val 0)
  refine ⟨Z,hy₀,?_⟩
  intro r hr1 hr k
  letI : Fact (1≤r) := ⟨hr1⟩
  obtain ⟨p,hp,hrp,h2p⟩ := even_exponent_dominates r hr
  letI : Fact (1≤((2*p:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*p by omega)⟩
  obtain ⟨y,hy⟩ := hev p hp k
  have hz : probabilityLpInclusion P 2 (2*p:ℕ) h2p (y.val 0)=Z :=
    divergence_unique D₀ hd hy hy₀
  have hraw : (y.val 0 : Ω → ℝ)=ᵐ[P] (Z : Ω → ℝ) := by
    have hh := probabilityLpInclusion_coe P 2 (2*p:ℕ) h2p (y.val 0)
    rw [hz] at hh
    exact hh.symm
  obtain ⟨z,hzraw⟩ := scalar_sum_jet_exponent_transfer H P W S hS hcore
    r (2*p:ℕ) hrp hr (ENNReal.natCast_ne_top _) k y
  exact ⟨z,hzraw.trans hraw⟩

end Asakura.Chapter12
