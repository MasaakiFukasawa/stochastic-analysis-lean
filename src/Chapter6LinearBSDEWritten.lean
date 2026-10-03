import Chapter6LinearBSDEConstruction
import Chapter6LinearBSDERepresentation
import Chapter6LinearBSDEBracket
import Chapter6FiniteCoefficientExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon bounded continuous adapted coefficients and an L2
terminal value produce the solution and both displayed formulas. The
constant extensions are constructed here, not imposed on the input. -/
theorem linear_bsde_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n)) (hco : ∀ r,∃ n,r≤c n)
    (R : ℝ) (hR : 0≤R)
    (hFnat : B.F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma (B.W 0) (realTimeClamp R)))
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[B.F (realTimeClamp R)] ξ)
    (α φ β : ℝ → Ω → ℝ)
    (hαc : ∀ w,ContinuousOn (fun r => α r w) (Icc 0 R))
    (hφc : ∀ w,ContinuousOn (fun r => φ r w) (Icc 0 R))
    (hβc : ∀ w,ContinuousOn (fun r => β r w) (Icc 0 R))
    (hαa : ∀ r∈Icc 0 R,Measurable[B.F (realTimeClamp r)] (α r))
    (hφa : ∀ r∈Icc 0 R,Measurable[B.F (realTimeClamp r)] (φ r))
    (hβa : ∀ r∈Icc 0 R,Measurable[B.F (realTimeClamp r)] (β r))
    (K : ℝ) (hK : 0≤K)
    (hαb : ∀ w r,r∈Icc 0 R → |α r w|≤K) (hφb : ∀ w r,r∈Icc 0 R → |φ r w|≤K)
    (hβb : ∀ w r,r∈Icc 0 R → |β r w|≤K) :
    ∃ u : BSDEFiniteEnergyData P B.F (B.W 0) c R,
      (u.Y (realTimeClamp R)=ᵐ[P] ξ) ∧
      (∀ w r,r∈Icc 0 R → u.B (w,r)= -(φ r w+α r w*u.Y (realTimeClamp r) w+β r w*u.Z (w,r))) ∧
      (∃ C,LocalCovarianceWitness P B.F u.M (B.W 0) C ∧
        ∀ b : ℝ,0≤b → C (realTimeClamp b)=ᵐ[P] fun w => ∫ r in 0..b,u.Z (w,r)) ∧
      ∃ (N : HalfClosedTime → Ω → ℝ) (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
        ItoCovarianceFormula P B.F (B.W 0) (fun z => finiteDriftExtension β R z.2 z.1) N ∧
        Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (N (realTimeClamp R) w-(∫ r in 0..R,β r w^2)/2))) ∧
        ∀ s∈Icc 0 R,Q[(fun w => ξ w*Real.exp (∫ r in s..R,α r w)+
          ∫ r in s..R,φ r w*Real.exp (∫ v in s..r,α v w))|B.F (realTimeClamp s)]=ᵐ[Q] u.Y (realTimeClamp s) := by
  have hT : (0:EReal)<⊤ := by simp
  let α' := finiteDriftExtension α R
  let φ' := finiteDriftExtension φ R
  let β' := finiteDriftExtension β R
  have ha := finite_drift_extension α R hR hαc
  have hf := finite_drift_extension φ R hR hφc
  have hb := finite_drift_extension β R hR hβc
  have hαreg := finite_coefficient_regularity B.F B.mono B.le α R hR hαa hαc
  have hφreg := finite_coefficient_regularity B.F B.mono B.le φ R hR hφa hφc
  have hβreg := finite_coefficient_regularity B.F B.mono B.le β R hR hβa hβc
  have hαbound (z : Ω × ℝ) : |α' z.2 z.1|≤K := hαb z.1 _ ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩
  have hφbound (z : Ω × ℝ) : |φ' z.2 z.1|≤K := hφb z.1 _ ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩
  have hβbound (z : Ω × ℝ) : |β' z.2 z.1|≤K := hβb z.1 _ ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩
  obtain ⟨u,hut,huB,hup⟩ := linear_bsde_solution_constructed P hT B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) (fun w r hr _ => by simpa using B.clock 0 0 w r hr)
    c hc hcm (fun n => EReal.coe_lt_top _) hct (fun n => changed_time_finite _ (hc n).le) hcc hco R hR (EReal.coe_lt_top R) hFnat
    ξ hξ hξm (fun z => φ' z.2 z.1) (fun z => α' z.2 z.1) (fun z => β' z.2 z.1)
    hφreg.1 hαreg.1 hβreg.1 hφreg.2 hαreg.2 hβreg.2 K hK hφbound hαbound hβbound
  have hβpr := (finite_coefficient_extension_progressive B.F B.mono B.le β R hR hβa hβc).2
  obtain ⟨N,C,Q,hQp,hNI,hCe,hQ,hPQ,hrep⟩ := linear_bsde_representation_written P B c hc hcm hct hcc hco R hR u α' φ' (fun z => β' z.2 z.1)
    ha.1 hf.1 (fun r hr => by
      change Measurable[B.F (realTimeClamp r)] (finiteDriftExtension α R r)
      rw [funext (ha.2 r hr)]
      exact hαa r hr)
    (fun r hr => by
      change Measurable[B.F (realTimeClamp r)] (finiteDriftExtension φ R r)
      rw [funext (hf.2 r hr)]
      exact hφa r hr)
    hβreg.1 hβpr K hK hβbound (fun w r _ => hαbound (w,r)) (fun w r _ => hφbound (w,r)) huB
  letI := hQp
  refine ⟨u,hut,?_,linear_bsde_bracket_written P B c (fun n => (hc n).le) hco R u,N,Q,hQp,hNI,?_,?_⟩
  · intro w r hr
    simpa only [α',φ',β',ha.2 r hr,hf.2 r hr,hb.2 r hr] using huB w r hr
  · rw [hQ]
    apply withDensity_congr_ae
    filter_upwards [hCe R hR] with w hw
    rw [hw]
    congr 4
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hR] at hr
    dsimp only
    exact congrArg (fun x : ℝ => x^2) (hb.2 r hr w)
  · intro s hs
    apply (condExp_congr_ae ?_).trans (hrep s hs)
    filter_upwards [(hPQ _).mp hut] with w hw
    rw [hw]
    have hαint t (ht : t∈Icc s R) : (∫ r in s..t,α r w)=∫ r in s..t,α' r w := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      exact (ha.2 r ⟨hs.1.trans hr.1,hr.2.trans ht.2⟩ w).symm
    rw [hαint R ⟨hs.2,le_rfl⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.2] at hr
    dsimp only
    rw [hαint r hr]
    rw [show φ' r w=φ r w from hf.2 r ⟨hs.1.trans hr.1,hr.2⟩ w]

end Asakura.Chapter6
