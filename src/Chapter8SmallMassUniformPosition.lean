import Chapter8SmallMassGronwallAssembly
import Chapter8RandomForceMoment
import Chapter8FinitePathForceIntegrability

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Uniform second moments are derived from the position-kernel formula,
not postulated. The input L2 path property is the finite-time SDE moment
bound; it need not be uniform in m. -/
theorem small_mass_uniform_position {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T)
    (g : E → E) (Lg : ℝ≥0) (hg : LipschitzWith Lg g)
    (Q : ℝ → Ω → C(Icc (0:ℝ) T,E))
    (hQm : ∀ m,0<m → m≤1 → Measurable (Q m))
    (hQ2 : ∀ m,0<m → m≤1 → MemLp (Q m) 2 P)
    (K : ℝ → ℝ → ℝ → E →L[ℝ] E) (L : ℝ) (hL : 0≤L)
    (hK : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,Continuous (K m t))
    (hKb : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ s∈Icc 0 t,‖K m t s‖≤L)
    (A N : ℝ → ℝ → Ω → E) (CA CN : ℝ) (hCA : 0≤CA) (hCN : 0≤CN)
    (hA : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,MemLp (A m t) 2 P)
    (hN : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,MemLp (N m t) 2 P)
    (hAb : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,(∫ w,‖A m t w‖^2 ∂P)≤CA)
    (hNb : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,(∫ w,‖N m t w‖^2 ∂P)≤CN)
    (he : ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,∀ᵐ w ∂P,
      Q m w (projIcc 0 T hT t)=A m t w+
        (∫ s in 0..t,K m t s (g (Q m w (projIcc 0 T hT s))))+N m t w) :
    ∃ C : ℝ,0≤C ∧ ∀ m,0<m → m≤1 → ∀ t∈Icc 0 T,
      (∫ w,‖Q m w (projIcc 0 T hT t)‖^2 ∂P)≤C := by
  obtain ⟨G,hG,hgG⟩ := random_lipschitz_force_moment P g Lg hg
  let u := fun m t => ∫ w,‖Q m w (projIcc 0 T hT t)‖^2 ∂P
  have hc m (hm : 0<m) (hm1 : m≤1) : Continuous (u m) :=
    (path_square_moment_continuous P (Q m) (hQm m hm hm1) (hQ2 m hm hm1)).comp continuous_projIcc
  have hi m (hm : 0<m) (hm1 : m≤1) t (ht : t∈Icc 0 T) :
      u m t≤3*(CA+CN)+3*t*L^2*G*(t+∫ s in 0..t,u m s) := by
    obtain ⟨hHm,hH2⟩ := finite_path_force_integrability P T hT (Q m) (hQm m hm hm1) (hQ2 m hm hm1) g Lg hg
    apply random_position_moment_inequality P t ht.1 (K m t) (hK m hm hm1 t ht)
      (fun z => g (Q m z.1 (projIcc 0 T hT z.2))) hHm (hH2 t ht)
      L hL (hKb m hm hm1 t ht) (A m t) (N m t) (fun w => Q m w (projIcc 0 T hT t))
      (hA m hm hm1 t ht) (hN m hm hm1 t ht) (he m hm hm1 t ht) (u m) (hc m hm hm1).continuousOn
      CA CN G hG (hAb m hm hm1 t ht) (hNb m hm hm1 t ht)
    intro s hs
    exact (hgG (fun w => Q m w (projIcc 0 T hT s))
      (Asakura.Chapter4.random_path_evaluation_memLp P (Q m) (hQm m hm hm1) (hQ2 m hm hm1) _)).2
  let C := (3*(CA+CN)+3*T^2*L^2*G)*Real.exp ((3*T*L^2*G+1)*T)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  exact small_mass_position_uniform_bound u T CA CN L G hT hCA hCN hG
    (fun m hm hm1 => (hc m hm hm1).continuousOn)
    (fun _ _ _ _ _ => integral_nonneg (fun _ => sq_nonneg _)) hi
end Asakura.Chapter8
