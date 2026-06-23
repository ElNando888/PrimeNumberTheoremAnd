import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.BorelCaratheodory
import PrimeNumberTheoremAnd.MediumPNT

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "ψ" => ChebyshevPsi

--open scoped ArithmeticFunction



lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall (by linarith)))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS



theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_setOf_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)






lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]



lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr



theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          DerivativeBound Mpos rpos (by linarith) (by linarith) analytic_f zeroAtZero realPartBounded hyp_z
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound






theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧ J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv



theorem LogOfAnalyticFunction' {r' r R : ℝ} {B : ℂ → ℂ}
    (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) r, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 r)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r', (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  have BanalyticOnNhdOfDr : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) r) := BanalyticOnNhdOfDR.mono (Metric.closedBall_subset_closedBall r_lt_R.le)
  exact LogOfAnalyticFunction r'_pos r'_lt_r BanalyticOnNhdOfDr Bnonzero



def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}



lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩






open Classical
noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0



lemma ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]



noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1



lemma analyticAt_finset_prod_sub_pow (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih



lemma CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    by_cases w_in_zeros : w ∈ SetOfZeros r f
    · obtain ⟨h_w, hh_w_analytic, hh_w_w_ne_zero, hh_w_eq⟩ := ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith))) hf_neq_zero_at_zero w_in_zeros;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ SetOfZeros r f then ZeroFactor f z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ finite_zeros_mono.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = h_w z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ hh_w_eq.2, hh_w_analytic.continuousAt.eventually_ne hh_w_w_ne_zero ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos w_in_zeros]
          congr 1
          exact hh_w_eq.1
        · have z_not_in : z ∉ SetOfZeros r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg z_not_in, hz]
          have hw_mem : w ∈ finite_zeros_mono.toFinset := finite_zeros_mono.mem_toFinset.mpr w_in_zeros
          rw [Finset.prod_eq_prod_diff_singleton_mul hw_mem (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply hh_w_analytic.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ finite_zeros_mono.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact analyticAt_finset_prod_sub_pow _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ h_ne_w
        exact fun h_eq_w => absurd (sub_eq_zero.mp h_eq_w).symm h_ne_w
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ finite_zeros_mono.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hfAnalytic w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact analyticAt_finset_prod_sub_pow _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h w_in_zeros
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr finite_zeros_mono.isClosed ) w_in_zeros ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticAt_const



noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1



lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const



lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]



lemma norm_fOfZero_le_norm_BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖f 0‖ ≤ ‖BlaschkeB r R f 0‖ := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  rw [BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf_neq_zero_at_zero, ← mul_one ‖f 0‖]
  refine mul_le_mul (by rw[mul_one]) ?_ (zero_le_one) (mul_nonneg (norm_nonneg (f 0)) zero_le_one)
  rw [← Finset.prod_const_one (s := (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset)]
  apply Finset.prod_le_prod
  · intro ρ hρ
    exact zero_le_one
  · intro ρ hρ
    simp only [SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ
    apply one_le_pow₀
    rw[one_le_div]
    · linarith
    · rw [norm_pos_iff]
      by_contra h
      rw [h] at hρ
      exact hf_neq_zero_at_zero hρ.2



lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)



lemma BlaschkeNonzero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r, BlaschkeB r R f z ≠ 0 := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  intro z hz
  have hz_norm_le_r : ‖z‖ ≤ r := by rwa [mem_closedBall_iff_norm, sub_zero] at hz
  have hz_norm_lt_R : ‖z‖ < R := by linarith
  let hFin := finiteSetOfZeros_mono r_lt_one finiteZeros
  have hBProd : ∏ ρ ∈ hFin.toFinset,
      (↑R - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    apply pow_ne_zero
    norm_num [ sub_eq_zero, Complex.ext_iff ];
    simp only [SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ
    rw [ eq_div_iff ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · rw [Real.sqrt_lt' (by linarith)] at hz_norm_lt_R
      rw [ Real.sqrt_le_iff ] at hρ
      exact fun h => absurd h ( by nlinarith [ sq_nonneg ( z.re - ρ.re ), sq_nonneg ( z.im - ρ.im ), mul_lt_mul_of_pos_left r_lt_R R_pos ] )
    · linarith
  unfold BlaschkeB Cf
  by_cases z_in_zeros : z ∈ SetOfZeros r f
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    obtain ⟨_, _, hne, heq⟩ :=
      ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith)))
        hf_neq_zero_at_zero z_in_zeros
    rw [heq.1]
    refine mul_ne_zero (div_ne_zero hne (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun h =>
        (Finset.mem_sdiff.mp hρ).2 (Finset.mem_singleton.mpr h.symm)))) hBProd
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    refine mul_ne_zero (div_ne_zero (fun hfz => z_in_zeros ⟨hz_norm_le_r, hfz⟩)
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
        pow_ne_zero _ (sub_ne_zero.mpr fun h => z_in_zeros (h ▸ hFin.mem_toFinset.mp hρ)))) hBProd



theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))



noncomputable def JBlaschke {r' r R : ℝ} {f : ℂ → ℂ}
  (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
  (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
  (finiteZeros : (SetOfZeros 1 f).Finite)
  (z : ℂ) : ℂ :=
  (LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R
    (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero))
    (BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero))).choose z



theorem JBlaschkeDerivBound {B r' r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (one_lt_B : 1 < B) (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) r') :
    ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖
      ≤ 16 * Real.log (B) * r ^ 2 / (r - r') ^ 3 := by
  have r_pos : 0 < r := lt_trans r'_pos r'_lt_r
  let blaschkeAnalytic := BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
  let blaschkeNonzero := BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
  let logOfAnalytic := LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R blaschkeAnalytic blaschkeNonzero
  set JB := logOfAnalytic.choose with JB_def
  obtain ⟨JB_Analytic, JB_0_eq_0, deriv_JB_eq, JB_re⟩ := logOfAnalytic.choose_spec
  rw [← JB_def] at JB_Analytic JB_0_eq_0 deriv_JB_eq JB_re
  have JB_def' : JB = (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) := by
    unfold JBlaschke
    rw [← JB_def]
  rw[← JB_def']
  refine BorelCaratheodoryDeriv (Real.log_pos one_lt_B) r'_pos r'_lt_r (JB_Analytic.analyticOn) JB_0_eq_0 ?_ hz
  intro w hw
  rw[← JB_re w hw]
  have hwr : w ∈ Metric.closedBall (0 : ℂ) r := by exact Metric.ball_subset_closedBall hw
  have hlog : 0 ≤ Real.log ‖BlaschkeB r R f 0‖ := by
    rw [← Real.log_one]
    apply Real.log_le_log zero_lt_one
    rw [← norm_one (α := ℂ), ← hf0_eq_one]
    exact norm_fOfZero_le_norm_BlaschkeOfZero r_pos r_lt_R R_lt_one finiteZeros (hf0_eq_one ▸ one_ne_zero)
  suffices h : Real.log ‖BlaschkeB r R f w‖ ≤ Real.log B by linarith
  exact Real.log_le_log (norm_pos_iff.mpr (blaschkeNonzero w hwr))
    (DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero) fz_bound (Metric.closedBall_subset_closedBall r_lt_R.le hwr))



theorem FinalBound {B r' r R' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (one_lt_B : 1 < B) (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_one : r < 1) (r_lt_R' : r < R') (R'_lt_R : R' < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f) :
    ‖(deriv f z / f z) - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ / (z - ρ)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
  have r'_lt_one : r' < 1 := lt_trans r'_lt_r r_lt_one
  have r_pos : 0 < r := lt_trans r'_pos r'_lt_r
  have R'_pos : 0 < R' := lt_trans r_pos r_lt_R'
  have R_pos : 0 < R := lt_trans R'_pos R'_lt_R
  have r_lt_R : r < R := lt_trans r_lt_R' R'_lt_R
  have r'_lt_R : r' < R := lt_trans r'_lt_r r_lt_R
  have rFiniteZeros: (SetOfZeros r f).Finite := finiteSetOfZeros_mono r_lt_one finiteZeros
  have zNotInZeros : ¬(z ∈ SetOfZeros r f) := (fun hmem => hz.2 ⟨hmem.1.trans r_lt_R'.le, hmem.2⟩)
  have z_norm : ‖z‖ ≤ r' := by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
  have ρ_mem : ∀ ρ ∈ rFiniteZeros.toFinset, ‖ρ‖ ≤ r ∧ f ρ = 0 := fun ρ hρ => rFiniteZeros.mem_toFinset.mp hρ
  have ρ_ne_zero : ∀ ρ ∈ rFiniteZeros.toFinset, ρ ≠ 0 := fun ρ hρ h => one_ne_zero (hf0_eq_one ▸ h ▸ (ρ_mem ρ hρ).2)
  have blaschke_sub_ne : ∀ ρ ∈ rFiniteZeros.toFinset, (↑R : ℂ) - z * (starRingEnd ℂ) ρ / ↑R ≠ 0 := by
    intro ρ hρ h
    have : ‖z * (starRingEnd ℂ) ρ / (↑R : ℂ)‖ < R := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos R_pos, div_lt_iff₀ R_pos, norm_mul, norm_conj]
      exact mul_lt_mul (z_norm.trans_lt r'_lt_R) ((ρ_mem ρ hρ).1.trans_lt r_lt_R).le
        (norm_pos_iff.mpr (ρ_ne_zero ρ hρ)) R_pos.le
    rw [← sub_eq_zero.mp h] at this
    simp [Complex.norm_real, abs_of_pos R_pos] at this
  have fz_ne : f z ≠ 0 := fun h => zNotInZeros ⟨z_norm.trans r'_lt_r.le, h⟩
  have blaschke_prod_ne : ∀ ρ ∈ rFiniteZeros.toFinset, ((↑R : ℂ) - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := fun ρ hρ => pow_ne_zero _ (blaschke_sub_ne ρ hρ)
  have hDiff_blaschke : ∀ ρ ∈ rFiniteZeros.toFinset, DifferentiableAt ℂ (fun w => ((↑R : ℂ) - w * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ) z := fun ρ _ => ((differentiableAt_const _).sub ((differentiableAt_id.mul_const _).div_const _)).pow _
  have hDiff_sub : ∀ ρ ∈ rFiniteZeros.toFinset, DifferentiableAt ℂ (fun w => (w - (ρ : ℂ)) ^ analyticOrderNatAt f ρ) z := fun ρ _ => (differentiableAt_id.sub (differentiableAt_const _)).pow _
  have hpos : 0 < R ^ 2 / R' - R' := by
    rw [sub_pos, lt_div_iff₀ R'_pos, ← sq]
    apply pow_lt_pow_left₀ R'_lt_R R'_pos.le two_ne_zero
  have LfBound := JBlaschkeDerivBound one_lt_B r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros fz_bound hz.1
  have zerosBound : ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) ≤ 1 / Real.log (R / R') * Real.log B := by
    apply (ZerosBound r_pos r_lt_one r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros fz_bound).trans
    refine mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ?_ ?_) (Real.log_nonneg (le_of_lt one_lt_B))
    · rw [← Real.log_one, Real.log_lt_log_iff zero_lt_one (div_pos R_pos R'_pos), one_lt_div R'_pos]
      exact R'_lt_R
    · rw [Real.log_le_log_iff (div_pos R_pos R'_pos) (div_pos R_pos r_pos)]
      exact div_le_div_of_nonneg_left (le_of_lt R_pos) r_pos (le_of_lt r_lt_R')
  suffices h1 : ‖deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ)‖ ≤ ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖ + 1 / (R ^ 2 / R' - R') * ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) by
    calc ‖deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ)‖
      ≤ ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖ + 1 / (R ^ 2 / R' - R') * ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) := h1
    _ ≤ 16 * Real.log B * r ^ 2 / (r - r') ^ 3 + 1 / (R ^ 2 / R' - R') * (1 / Real.log (R / R') * Real.log B) := by
      linarith [mul_le_mul_of_nonneg_left zerosBound (div_nonneg zero_le_one (le_of_lt hpos))]
    _ = (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
      field_simp
  suffices h2 : deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) =
    deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ) by
    rw [h2, sub_eq_add_neg]
    apply norm_add_le_of_le (le_rfl)
    simp only [norm_neg, cast_sum, Finset.mul_sum, one_div_mul_eq_div]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ρ hρ => ?_))
    rw [norm_div, RCLike.norm_natCast]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos
    simp only [mem_diff, Metric.mem_closedBall, dist_zero_right, SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ hz
    rw [norm_sub_rev]
    calc R ^ 2 / R' - R'
        ≤ ‖↑R ^ 2 / conj ρ‖ - ‖z‖ := by
          refine sub_le_sub ?_ (hz.1.trans (r'_lt_r.le.trans r_lt_R'.le))
          rw [norm_div, norm_pow, norm_real, norm_eq_abs, abs_of_nonneg (le_of_lt R_pos)]
          apply div_le_div_of_nonneg_left (sq_nonneg R) (norm_pos_iff.mpr (star_ne_zero.mpr (fun h => one_ne_zero (hf0_eq_one ▸ h ▸ hρ.2))))
          rw [norm_star]
          linarith [hρ.1]
      _ ≤ ‖↑R ^ 2 / conj ρ - z‖ := norm_sub_norm_le _ _
  suffices h3 : deriv (BlaschkeB r R f) z / BlaschkeB r R f z = deriv f z / f z
    + ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ)
    - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) by
    let blaschkeAnalytic := BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
    let blaschkeNonzero := BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
    let logOfAnalytic := LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R blaschkeAnalytic blaschkeNonzero
    set JB := logOfAnalytic.choose with JB_def
    obtain ⟨JB_Analytic, JB_0_eq_0, deriv_JB_eq, JB_re⟩ := logOfAnalytic.choose_spec
    rw [← JB_def] at JB_Analytic JB_0_eq_0 deriv_JB_eq JB_re
    have JB_def' : JB = (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) := by
      unfold JBlaschke
      rw [JB_def]
    rw [eq_sub_iff_add_eq, sub_add_eq_add_sub, ← h3, ← JB_def', eq_comm]
    exact deriv_JB_eq z hz.1
  suffices h4 : BlaschkeB r R f z = f z * ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ((R - z * conj ρ / R) / (z - ρ)) ^ (analyticOrderNatAt f ρ) by
    have sum1LD : ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, logDeriv (fun z ↦ (R - z * conj ρ / R) ^ ↑(analyticOrderNatAt f ρ)) z = ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ) := by
      refine Finset.sum_congr rfl (fun ρ hρ => ?_)
      rw [← logDeriv_pow, logDeriv_fun_pow, logDeriv_fun_pow, logDeriv_id', mul_eq_mul_left_iff]
      · left
        simp only [logDeriv, Pi.div_apply]
        rw [deriv_fun_sub (differentiableAt_const _) ?_, deriv_div_const, deriv_mul_const (differentiableAt_fun_id)]
        · simp only [deriv_const', deriv_id'', one_mul, zero_sub]
          rw [div_eq_div_iff (blaschke_sub_ne ρ hρ), one_mul, neg_mul, mul_sub, mul_div, neg_sub, mul_comm _ z, ← mul_div_assoc, sub_left_inj]
          · field_simp
            exact mul_div_cancel_left₀ _ (star_ne_zero.mpr (ρ_ne_zero ρ hρ))
          · intro h; apply blaschke_sub_ne ρ hρ
            have hconj : (starRingEnd ℂ) ρ ≠ 0 := star_ne_zero.mpr (ρ_ne_zero ρ hρ)
            have hR : (↑R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt R_pos)
            rw [sub_eq_zero.mp h, div_mul_cancel₀ _ hconj, sq, mul_div_cancel_right₀ _ hR, sub_self]
        · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_mul,
          DifferentiableAt.div_const]
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_const, DifferentiableAt.fun_sub_iff_right,
          differentiableAt_fun_id, DifferentiableAt.fun_mul, DifferentiableAt.div_const]
    have sum2LD : ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, logDeriv (fun z ↦ (z - ρ) ^ ↑(analyticOrderNatAt f ρ)) z =  ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      have : (fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ) =
        (fun x ↦ x ^ analyticOrderNatAt f ρ) ∘ (fun z ↦ z - ρ) := by rfl
      rw[← logDeriv_pow, this, logDeriv_comp]
      · simp only [logDeriv_pow, differentiableAt_fun_id, differentiableAt_const, deriv_fun_sub,
          deriv_id'', deriv_const', sub_zero, mul_one]
      · simp only [differentiableAt_fun_id, DifferentiableAt.fun_pow]
      · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_sub]
    unfold BlaschkeB Cf
    simp only [rFiniteZeros, ↓reduceDIte, dite_eq_ite, ite_mul, ← logDeriv_apply, ← sum1LD, ← sum2LD]
    rw [← logDeriv_prod blaschke_prod_ne hDiff_blaschke,
      ← logDeriv_prod ?_ hDiff_sub,
      ← logDeriv_mul _ fz_ne (Finset.prod_ne_zero_iff.mpr blaschke_prod_ne) ((hfAnalytic z (Metric.closedBall_subset_closedBall r'_lt_one.le hz.1)).differentiableAt) (DifferentiableAt.fun_finsetProd hDiff_blaschke),
      ← logDeriv_div _ ?_ ?_ ?_ (DifferentiableAt.fun_finsetProd hDiff_sub)]
    · have h_eq : ∀ᶠ w in nhds z, (if w ∈ SetOfZeros r f then (ZeroFactor f w / ∏ ρ ∈ rFiniteZeros.toFinset \ {w}, (w - ρ) ^ analyticOrderNatAt f ρ) * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ else (f w / ∏ ρ ∈ rFiniteZeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ) * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ) = (f w * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ) / ∏ ρ ∈ rFiniteZeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [(isOpen_compl_iff.mpr rFiniteZeros.isClosed).mem_nhds zNotInZeros] with w hw using by rw [if_neg hw]; ring
      simp only [logDeriv, Pi.div_apply]
      congr 1
      · apply Filter.EventuallyEq.deriv_eq h_eq
      · convert h_eq.self_of_nhds using 1
    · exact mul_ne_zero fz_ne (Finset.prod_ne_zero_iff.mpr blaschke_prod_ne)
    · simp only [ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
        sub_eq_zero, ↓existsAndEq, zNotInZeros, true_and, false_and, not_false_eq_true]
    · exact ((hfAnalytic z (Metric.closedBall_subset_closedBall r'_lt_one.le hz.1)).differentiableAt).mul (DifferentiableAt.fun_finsetProd hDiff_blaschke)
    · exact (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun h => zNotInZeros (h ▸ rFiniteZeros.mem_toFinset.mp hρ)))
  simp only [BlaschkeB, Cf, rFiniteZeros, ↓reduceDIte, zNotInZeros, div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib, div_pow]


















































theorem ZeroInequality : ∃ (E : ℝ) (EinIoo : E ∈ Ioo (0 : ℝ) 1),
    ∀ (ρ : ℂ) (σ t : ℝ),
    ζ ρ = 0 →
        σ = ρ.re →
            t = ρ.im →
                |t| ≥ 2 →
                    σ ≤ 1 - E / log |t| := by
    sorry



noncomputable def E : ℝ := ZeroInequality.choose
lemma EinIoo : E ∈ Ioo (0 : ℝ) 1 := ZeroInequality.choose_spec.1
theorem ZeroInequalitySpecialized : ∀ (ρ : ℂ) (σ t : ℝ),
    ζ ρ = 0 →
        σ = ρ.re →
            t = ρ.im →
                |t| ≥ 2 →
                    σ ≤ 1 - E / log |t| := ZeroInequality.choose_spec.2
noncomputable def DeltaT (t : ℝ) : ℝ := E / log |t|



lemma DeltaRange : ∀ (t : ℝ),
    |t| ≥ 2 →
        DeltaT t < (1 : ℝ) / 14 := by
    sorry











lemma LogDerivZetaUniformLogSquaredBoundStrip : ∃ (F : ℝ) (Fequ : F = E / 3) (C : ℝ)
    (Cnonneg : 0 ≤ C), ∀ (σ t : ℝ),
    3 ≤ |t| →
        σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 := by
    exact ⟨E / 3, rfl, sorry⟩



noncomputable def F : ℝ := LogDerivZetaUniformLogSquaredBoundStrip.choose
lemma Fequ : F = E / 3 := LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.1
lemma LogDerivZetaUniformLogSquaredBoundStripSpec : ∃ (C : ℝ) (_ : 0 ≤ C),
    ∀ (σ t : ℝ),
    3 ≤ |t| →
        σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 :=
    by exact LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2
lemma FLogTtoDeltaT : ∀ (t : ℝ),
    DeltaT t / 3 = F / Real.log |t| := fun _ ↦ by simp [DeltaT, Fequ]; ring

/-- The logarithmic derivative of the Riemann zeta function is bounded in the half-plane
`Re(s) >= 3/2`. -/
lemma LogDerivZetaBdd_of_Re_ge_three_halves :
    ∃ C, ∀ (s : ℂ), 3/2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  have h_sum_converges : Summable (fun n : ℕ ↦ vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    have h_summable : Summable (fun n : ℕ ↦ (Real.log n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) := by
      obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ (1/4 : ℝ) := by
        use 4, by grind, fun n hn ↦ by
          have := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ (1/4 : ℝ))
          rw [Real.log_rpow (by positivity)] at this
          nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) (1/4 : ℝ)]
      have hBound : ∀ n : ℕ, n ≥ 2 →
          (Real.log n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ C / (n : ℝ) ^ (5 / 4 : ℝ) := fun n hn ↦ by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        convert mul_le_mul_of_nonneg_right (hC n hn)
          (by positivity : 0 ≤ (n : ℝ) ^ (5 / 4 : ℝ)) using 1
        rw [mul_assoc, ← Real.rpow_add (by positivity)]
        grind
      rw [← summable_nat_add_iff 2]
      exact Summable.of_nonneg_of_le
        (fun n ↦ div_nonneg (Real.log_nonneg (by grind))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun n ↦ hBound _ (by grind))
        (Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <|
          Real.summable_one_div_nat_rpow.2 <| by grind)
    refine .of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) h_summable
    · exact div_nonneg (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg)
        (by positivity)
    · rcases eq_or_ne n 0 with (rfl | hn) <;>
        simp_all [ArithmeticFunction.vonMangoldt]
      field_simp
      split_ifs
      · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.minFac_pos _))
          (Nat.cast_le.mpr (Nat.minFac_le (Nat.pos_of_ne_zero hn)))
      · exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn))
  have h_log_deriv_sum : ∀ s : ℂ, 3 / 2 ≤ s.re →
      deriv riemannZeta s / riemannZeta s = -∑' n : ℕ, (vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
    intro s hs; have h := LogDerivativeDirichlet s (by grind); linear_combination -h
  have h_triangle : ∀ s : ℂ,
      ‖∑' n : ℕ, (vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤
        ∑' n : ℕ, ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ := fun s ↦ by
    by_cases h : Summable fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s
    · exact norm_tsum_le_tsum_norm h.norm
    · simp only [tsum_eq_zero_of_not_summable h, norm_zero]
      exact tsum_nonneg fun _ ↦ by positivity
  have h_norm_summand : ∀ s : ℂ, 3 / 2 ≤ s.re → ∀ n : ℕ,
      ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤ (vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro s hs n
    by_cases hn : n = 0 <;> simp_all [Complex.norm_cpow_of_ne_zero]
    ring_nf; norm_num
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs))
      ArithmeticFunction.vonMangoldt_nonneg
  refine ⟨∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ),
    fun s hs ↦ ?_⟩
  have hSum : Summable fun n ↦ ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity)
      (fun n ↦ h_norm_summand s hs n) h_sum_converges
  simpa [neg_div, h_log_deriv_sum s hs] using (h_triangle s).trans
    (hSum.tsum_le_tsum (fun n ↦ h_norm_summand s hs n) h_sum_converges)

theorem LogDerivZetaUniformLogSquaredBound : ∃ (C : ℝ) (_Cnonneg : 0 ≤ C),
    ∀ (σ t : ℝ), 3 < |t| → σ ∈ Set.Ici (1 - F / Real.log |t|) →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨C1, hC1⟩ := LogDerivZetaUniformLogSquaredBoundStripSpec
  obtain ⟨C2, hC2⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  use max C1 C2, le_max_of_le_left hC1.1
  intro σ t ht hσ
  by_cases hσ' : σ ≤ 3 / 2
  · exact (hC1.2 σ t (by grind) ⟨hσ, hσ'⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · refine (hC2 _ ?_).trans ?_
    · norm_num; linarith
    · have hC2pos := (norm_nonneg _).trans (hC2 2 (by norm_num))
      exact (le_max_right _ _).trans (le_mul_of_one_le_right
        (le_max_of_le_right (by grind))
        (one_le_pow₀ (by
          rw [Real.le_log_iff_exp_le (by grind)]
          exact Real.exp_one_lt_d9.le.trans (by grind))))

theorem LogDerivZetaLogSquaredBoundSmallt : ∃ (C : ℝ) (Cnonneg : C ≥ 0),
    ∀ (σ t T : ℝ) (Tpos: T > 0),
    |t| ≤ T →
        σ = 1 - F / Real.log T →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log (2 + T) ^ 2 := by
    sorry






noncomputable def I1New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))



noncomputable def I5New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

lemma IntegralLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
  ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C / Real.sqrt T := by
    have h_log_sq_le_t_fourth_pow :
        ∃ C > 0, ∀ t : ℝ, 3 ≤ t → (Real.log t)^2 / t^2 ≤ C / t^(3/2 : ℝ) := by
      have h_log_sq_le_sqrt :
          ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ^ 2 ≤ C * t ^ (1 / 2 : ℝ) := by
        have h_log_sq_le_sqrt : ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ≤ C * t ^ (1 / 4 : ℝ) := by
          use 4, by grind, fun t ht ↦ ?_
          have := Real.log_le_sub_one_of_pos (by positivity : 0 < t ^ (1 / 4 : ℝ))
          rw [Real.log_rpow (by positivity)] at this; linarith
        obtain ⟨C, hC₀, hC⟩ := h_log_sq_le_sqrt; use C^2
        exact ⟨sq_pos_of_pos hC₀, fun t ht ↦
          (pow_le_pow_left₀ (Real.log_nonneg <| by linarith) (hC t ht) 2).trans <| by
            rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            grind⟩
      obtain ⟨C, hC_pos, hC⟩ := h_log_sq_le_sqrt; use C
      refine ⟨hC_pos, fun t ht ↦ ?_⟩; rw [div_le_div_iff₀] <;> try positivity
      convert mul_le_mul_of_nonneg_right (hC t ht)
        (Real.rpow_nonneg (by linarith : 0 ≤ t) (3 / 2)) using 1
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; grind
    obtain ⟨C, hC_pos, hC_bound⟩ := h_log_sq_le_t_fourth_pow
    use C * 2
    have h_integral_bound :
        ∀ T : ℝ, 3 < T → ∫ t in Set.Ici T, C / t^(3/2 : ℝ) = C * 2 / Real.sqrt T := by
      have h_integral_eval :
          ∀ T : ℝ, 3 < T → ∫ t in Set.Ici T, t ^ (-3 / 2 : ℝ) = 2 / Real.sqrt T := by
        intro T hT
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt] <;> norm_num
        · rw [Real.sqrt_eq_rpow, Real.rpow_neg] <;> ring_nf; linarith
        · linarith
      intro T hT; convert congr_arg (fun x ↦ C * x) (h_integral_eval T hT) using 1 <;> ring_nf
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx ↦ ?_
      rw [← Real.rpow_neg (by linarith [Set.mem_Ici.mp hx])]; ring_nf
    refine ⟨by positivity, fun T hT ↦ (MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ici
        fun t ht ↦ hC_bound t <| by linarith [ht.out]).trans (h_integral_bound T hT |> le_of_eq)⟩
    · have hInteg : IntegrableOn (fun t ↦ C / t ^ (3 / 2 : ℝ)) (Set.Ici T) := by
        have := h_integral_bound T hT
        contrapose! this; rw [MeasureTheory.integral_undef this]; positivity
      have hMeas : AEStronglyMeasurable (fun t ↦ Real.log t ^ 2 / t ^ 2)
          (MeasureTheory.volume.restrict (Set.Ici T)) :=
        Measurable.aestronglyMeasurable <| Measurable.mul
          (Measurable.pow_const Real.measurable_log _)
          (Measurable.inv (measurable_id.pow_const _))
      have hBound : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ici T),
          ‖Real.log t ^ 2 / t ^ 2‖ ≤ C / t ^ (3 / 2 : ℝ) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_of_nonneg (by positivity)]
        exact hC_bound t (by linarith [ht.out])
      exact MeasureTheory.Integrable.mono' hInteg hMeas hBound
    · have := h_integral_bound T hT
      contrapose! this; rw [MeasureTheory.integral_undef this]; positivity

lemma NormXPowS {X : ℝ} (X_gt_one : 1 < X) {s : ℂ} (hs : s.re = 1 + (Real.log X)⁻¹) :
    ‖(X : ℂ) ^ s‖ = X * Real.exp 1 := by
  simp [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < X), hs,
    Real.rpow_add (by positivity : 0 < X), Real.rpow_inv_log (by positivity) X_gt_one.ne']

lemma LogDerivZetaBoundForI1 : ∃ C > 0, ∀ {X T : ℝ} (_Xgt3 : 3 < X) (_Tgt3 : 3 < T)
    (t : ℝ) (_ht : t ≤ -T),
    let σ := 1 + (Real.log X)⁻¹
    ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * (Real.log (-t))^2 := by
  obtain ⟨C, hC⟩ := LogDerivZetaUniformLogSquaredBound
  field_simp
  use C + 1
  refine ⟨by grind, fun {X T} hX hT t ht ↦ (hC.2 _ _ ?_ ?_).trans ?_⟩
  · cases abs_cases t <;> grind
  · apply Set.mem_Ici.mpr
    have hX' : 0 ≤ 1 / Real.log X := one_div_nonneg.mpr (Real.log_nonneg (by grind))
    have ht' : 0 ≤ F / Real.log |t| := by
      apply div_nonneg (Fequ ▸ div_nonneg (le_of_lt EinIoo.1) zero_le_three)
      exact Real.log_nonneg (by cases abs_cases t <;> grind)
    grind
  · simp only [abs_of_nonpos (by grind : t ≤ 0)]
    nlinarith [hC.1, sq_nonneg (Real.log (-t))]

lemma I1NewIntegrandBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C > 0, ∀ {ε X T : ℝ} (_εinIoo : ε ∈ Set.Ioo 0 1) (_Xgt3 : 3 < X) (_Tgt3 : 3 < T)
    (t : ℝ) (_ht : t ≤ -T),
    ‖SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
    C * (X / ε) * (Real.log (-t))^2 / (-t)^2 := by
  obtain ⟨C₁, hC₁₀, hC₁⟩ := @LogDerivZetaBoundForI1
  obtain ⟨C₂, hC₂₀, hC₂⟩ := @MellinOfSmooth1b SmoothingF ContDiffSmoothingF suppSmoothingF
  refine ⟨C₁ * C₂ * Real.exp 1, by positivity, fun {ε X T} hε hX hT t ht ↦ ?_⟩
  specialize hC₁ hX hT t ht
  specialize hC₂ 1 zero_lt_one (1 + (Real.log X)⁻¹ + t * Complex.I) ?_ ?_ ε hε.1 hε.2 <;> norm_num at *
  · exact Real.log_nonneg (by linarith)
  · linarith [inv_le_one_of_one_le₀ (show 1 ≤ Real.log X from by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by grind))]
  · refine (mul_le_mul_of_nonneg_right
        (mul_le_mul hC₁ hC₂ (by positivity) (by positivity)) (by positivity)).trans ?_
    rw [Complex.norm_cpow_of_ne_zero (by norm_cast; linarith)]
    norm_num [Complex.normSq, Complex.sq_norm]
    ring_nf
    norm_num
    rw [abs_of_pos (by positivity)]
    norm_num [Complex.arg]
    ring_nf
    norm_num
    rw [if_pos (by positivity)]
    norm_num [Real.rpow_add (by positivity : 0 < X), Real.rpow_one]
    ring_nf
    norm_num
    rw [show X ^ (Real.log X)⁻¹ = Real.exp 1 by
      rw [Real.rpow_def_of_pos (by positivity)]
      norm_num [Real.exp_ne_zero, ne_of_gt (Real.log_pos (by linarith : 1 < X))]]
    ring_nf
    norm_num
    field_simp
    gcongr
    · exact mul_pos (sq_pos_of_neg (by linarith)) hε.1
    · linarith
    · exact le_add_of_nonneg_left <| add_nonneg (add_nonneg zero_le_one
          (div_nonneg zero_le_two (Real.log_nonneg (by linarith))))
          (div_nonneg zero_le_one (sq_nonneg _))

lemma I1NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (_Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (_εinIoo : ε ∈ Ioo 0 1) (_Xgt3 : 3 < X) (_Tgt3 : 3 < T),
    ‖I1New SmoothingF ε X T‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    have h_I1New_bound : ∃ C > 0, ∀ {ε X T : ℝ} (εinIoo : ε ∈ Set.Ioo 0 1) (Xgt3 : 3 < X)
        (Tgt3 : 3 < T),
        ‖∫ t in Set.Iic (-T),
          SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
          C * (X / ε) * (1 / Real.sqrt T) := by
            obtain ⟨C₁, hC₁_pos, hC₁⟩ : ∃ C₁ > 0, ∀ {ε X T : ℝ} (εinIoo : ε ∈ Set.Ioo 0 1)
                (Xgt3 : 3 < X) (Tgt3 : 3 < T)
                (t : ℝ) (ht : t ≤ -T),
                ‖SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
                C₁ * (X / ε) * (Real.log (-t))^2 / (-t)^2 :=
              I1NewIntegrandBound suppSmoothingF ContDiffSmoothingF
            obtain ⟨C₂, hC₂_pos, hC₂⟩ : ∃ C₂ > 0, ∀ {T : ℝ} (Tgt3 : 3 < T),
                ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C₂ / Real.sqrt T :=
                  IntegralLogSqOverTSqBound
            refine ⟨C₁ * C₂, mul_pos hC₁_pos hC₂_pos,
              fun {ε X T} εinIoo Xgt3 Tgt3 ↦
                (MeasureTheory.norm_integral_le_integral_norm _).trans ?_⟩
            refine (MeasureTheory.integral_mono_of_nonneg
              (g := fun t ↦ C₁ * (X / ε) * Real.log (-t) ^ 2 / (-t) ^ 2) ?_ ?_ ?_).trans ?_
            · exact Filter.Eventually.of_forall fun x ↦ norm_nonneg _
            · have h_integrable :
                  MeasureTheory.IntegrableOn (fun t ↦ (Real.log t)^2 / t^2) (Set.Ici T) := by
                have h_integrable :
                    MeasureTheory.IntegrableOn
                      (fun t ↦ (Real.log t)^2 / t^2) (Set.Ioi T) := by
                  have h_bound : ∀ t, t > T → (Real.log t)^2 / t^2 ≤ 4 / t^(3/2 : ℝ) := by
                    intro t ht
                    have h_log_bound : Real.log t ≤ 2 * t^(1/4 : ℝ) := by
                      have := Real.log_le_sub_one_of_pos (show 0 < t ^ (1 / 4 : ℝ) / 2 by
                        exact div_pos (Real.rpow_pos_of_pos (by linarith) _) zero_lt_two)
                      rw [Real.log_div (by exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) _))
                        (by norm_num), Real.log_rpow (by linarith)] at this
                      have := Real.log_two_lt_d9; norm_num at *; linarith
                    rw [div_le_div_iff₀ (by nlinarith)
                      (Real.rpow_pos_of_pos (by linarith) (3 / 2))]
                    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
                      (Real.log_nonneg (by linarith)) h_log_bound 2)
                      (by exact Real.rpow_nonneg (by linarith) _)).trans ?_
                    ring_nf
                    norm_num
                    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
                      ← Real.rpow_add (by linarith)]
                    norm_num
                  have h_integrable :
                      MeasureTheory.IntegrableOn (fun t ↦ 4 / t^(3/2 : ℝ)) (Set.Ioi T) := by
                    have h_integrable :
                        MeasureTheory.IntegrableOn (fun t ↦ t ^ (-3 / 2 : ℝ)) (Set.Ioi T) :=
                      integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)
                    norm_num [div_eq_mul_inv] at *
                    exact MeasureTheory.Integrable.const_mul (h_integrable.congr_fun
                      (fun x hx ↦ by rw [Real.rpow_neg (by linarith [hx.out])])
                      measurableSet_Ioi) _
                  refine h_integrable.mono' ?_ ?_
                  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
                    have hne : ∀ t ∈ Set.Ioi T, t ≠ 0 := fun t ht ↦ by linarith [ht.out]
                    have hsq : ∀ t ∈ Set.Ioi T, t ^ 2 ≠ 0 := fun t ht ↦ pow_ne_zero 2 (hne t ht)
                    fun_prop (discharger := assumption)
                  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
                      with t ht using by
                        rw [Real.norm_of_nonneg (by positivity)]
                        exact h_bound t ht
                rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set
                  MeasureTheory.Ioi_ae_eq_Ici] at *
                simp_all only [one_div, mem_Ioo, ofReal_inv, Complex.norm_mul, Complex.norm_div,
                  norm_neg, log_neg_eq_log, even_two, Even.neg_pow]
              have h_integrable : MeasureTheory.IntegrableOn (fun t ↦
                  (Real.log (-t))^2 / (-t)^2) (Set.Iic (-T)) := by
                convert h_integrable.comp_neg using 1; norm_num [Set.indicator]
              simpa only [mul_div_assoc] using h_integrable.const_mul _
            · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
                using hC₁ εinIoo Xgt3 Tgt3 t ht
            · convert mul_le_mul_of_nonneg_left (hC₂ Tgt3) (show 0 ≤ C₁ * (X / ε) by
                exact mul_nonneg hC₁_pos.le
                  (div_nonneg (by positivity) (by linarith [εinIoo.1]))) using 1 <;> ring_nf
              rw [← MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
                ← neg_neg T, ← integral_comp_neg_Iic]
              norm_num
              ring_nf
    obtain ⟨C, hC₀, hC⟩ := h_I1New_bound; use C / (2 * Real.pi)
    refine ⟨by positivity, fun {ε X T} hε hX hT ↦ ?_⟩
    simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    ring_nf at *
    convert mul_le_mul_of_nonneg_right (hC hε.1 hε.2 hX hT)
      (show (0 : ℝ) ≤ Real.pi⁻¹ * (1 / 2) by positivity) using 1
    · simp only [I1New, SmoothedChebyshevIntegrand, norm_mul, norm_inv, Complex.norm_I,
        Complex.norm_two, mul_one, one_mul, one_div]
      rw [show ∀ a b : ℝ, (2 * a)⁻¹ * b = b * (a⁻¹ * 2⁻¹) by intro _ _; ring]
      congr 1
      · apply congr_arg
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun t _ ↦ by
          rw [show (↑t : ℂ) * I = I * ↑t by ring, div_eq_mul_inv, neg_mul,
              show (↑(Real.log X)⁻¹ : ℂ) = (↑(Real.log X))⁻¹ from Complex.ofReal_inv _]
          ring
      · rw [show ‖(↑π : ℂ)‖ = π from (RCLike.norm_ofReal π).trans (abs_of_pos Real.pi_pos)]
    · ring

set_option backward.isDefEq.respectTransparency false in
lemma I5NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 ≤ C),
      ∀ {ε X T : ℝ} (_ : ε ∈ Ioo 0 1) (_ : 3 < X) (_ : 3 < T),
        ‖I5New SmoothingF ε X T‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    obtain ⟨C, Cnonneg, hI1NewBound⟩ := I1NewBound suppSmoothingF ContDiffSmoothingF
    use C, Cnonneg
    intro ε X T εinIoo Xgt3 Tgt3
    have I1NewI5New : I5New SmoothingF ε X T = conj (I1New SmoothingF ε X T) := by
        unfold I1New I5New
        simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
        rw [neg_mul, mul_neg, ← neg_mul]
        congr
        · ring
        · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
          apply setIntegral_congr_fun <| measurableSet_Ioi
          intro x hx; simp only []
          rw [← smoothedChebyshevIntegrand_conj (by linarith)]
          simp [ofReal_inv, ofReal_neg, neg_mul, map_add, map_one, map_inv₀, conj_ofReal,
            map_neg, map_mul, conj_I, mul_neg, neg_neg]
    rw [I1NewI5New, RCLike.norm_conj]
    exact hI1NewBound εinIoo Xgt3 Tgt3



noncomputable def I2New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ - T * I)))



noncomputable def I4New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + T * I)))



lemma I2NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (εinIoo : ε ∈ Ioo 0 1) (Xgt3 : 3 < X) (Tgt3 : 3 < T),
    let σ' := 1 - F / Real.log T
    ‖I2New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    sorry



lemma I4NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 ≤ C),
      ∀ {ε X T : ℝ} (_ : ε ∈ Ioo 0 1) (_ : 3 < X) (_ : 3 < T),
        let σ' := 1 - F / Real.log T
        ‖I4New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    obtain ⟨C, Cnonneg, hI2NewBound⟩ := I2NewBound suppSmoothingF ContDiffSmoothingF
    use C, Cnonneg
    intro ε X T εinIoo Xgt3 Tgt3 σ'
    have I2NewI4New : I4New SmoothingF ε X T σ' = -conj (I2New SmoothingF ε X T σ') := by
        unfold I2New I4New
        simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
        rw [mul_neg, div_neg, neg_mul_comm, ← mul_neg]
        congr
        rw [← intervalIntegral_conj, neg_neg]
        exact intervalIntegral.integral_congr fun x hx ↦ by
          rw [← smoothedChebyshevIntegrand_conj (by linarith)]
          simp [map_sub, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    rw [I2NewI4New, norm_neg, RCLike.norm_conj]
    exact hI2NewBound εinIoo Xgt3 Tgt3



noncomputable def I3New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ' + t * I)))



lemma I3NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (εinIoo : ε ∈ Ioo 0 1) (Xgt3 : 3 < X) (Tgt3 : 3 < T),
    let σ' := 1 - F / Real.log T
    ‖I3New SmoothingF ε X T σ'‖ ≤ C * (X ^ (1 - F / Real.log T) * Real.sqrt T) / ε := by
    sorry



theorem SmoothedChebyshevPull3 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ' : ℝ}
    (σ'_pos : 0 < σ') (σ'_lt_one : σ' < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ' 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I1New SmoothingF ε X T -
      I2New SmoothingF ε T X σ' +
      I3New SmoothingF ε T X σ' +
      I4New SmoothingF ε T X σ' +
      I5New SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
    unfold SmoothedChebyshev VerticalIntegral'
    have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by nth_rewrite 1 [← add_zero 1]; bound
    have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
        rw [← one_add_one_eq_two]; gcongr; exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
    have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
    rw [verticalIntegral_split_three (a := -T) (b := T)]
    swap
    ·   exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
            X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
    ·   have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
        unfold I1New; simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc,
          add_left_cancel_iff]
        unfold I5New; nth_rewrite 6 [add_comm]; simp only [← add_assoc]
        rw [add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) *
            -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
            ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
        unfold VIntegral I2New I3New I4New
        simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
        let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
            SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
        let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
        have : ∫ (y : ℝ) in -T..T,
            SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
            ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by unfold fTempRR; simp [temp]
        rw [this]
        have : ∫ (σ₀ : ℝ) in σ'..1 + (Real.log X)⁻¹,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
            unfold fTempRR; simp [ofReal_neg, neg_mul, sub_eq_add_neg]
        rw [this]
        have : ∫ (t : ℝ) in -T..T,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ' + ↑t * I) =
            ∫ (y : ℝ) in -T..T, fTempRR σ' y := rfl
        rw [this]
        have : ∫ (σ₀ : ℝ) in σ'..1 + (Real.log X)⁻¹,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x T := rfl
        rw [this]
        have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
            -∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
            I * ∫ (y : ℝ) in -T..T, fTempRR σ' y) +
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x T =
            -(2 * ↑π * I) * RectangleIntegral' fTempC (σ' - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
            unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
            simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
              ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
              neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
              ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
              zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
            ring_nf
            simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
              mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
            ring_nf
        rw [this]
        field_simp
        rw [mul_comm, eq_comm, neg_add_eq_zero]
        have pInRectangleInterior : (Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
            refine rectangle_mem_nhds_iff.mpr <| mem_reProdIm.mpr ?_
            simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
                sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
            constructor
            · unfold uIoo; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
              exact mem_Ioo.mpr ⟨σ'_lt_one, by linarith⟩
            · unfold uIoo; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
              exact mem_Ioo.mpr ⟨by linarith, by linarith⟩
        apply ResidueTheoremOnRectangleWithSimplePole'
        · simp; linarith
        · simp; linarith
        · simp only [one_div]; exact pInRectangleInterior
        ·   apply DifferentiableOn.mul
            ·   apply DifferentiableOn.mul
                ·   simp only [re_add_im]
                    have : (fun z ↦ -ζ' z / ζ z) = -(ζ' / ζ) := by ext; simp; ring
                    rw [this]; apply DifferentiableOn.neg; apply holoOn.mono
                    apply diff_subset_diff_left; apply reProdIm_subset_iff'.mpr; left
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
                        div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
                        neg_zero, zero_div, zero_add]
                    constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
                ·   intro s hs; apply DifferentiableAt.differentiableWithinAt; simp only [re_add_im]
                    apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one
                    have := mem_reProdIm.mp hs.1 |>.1
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
                        div_self_mul_self', add_zero] at this
                    rw [uIcc_of_le (by linarith)] at this; linarith [this.1]
            ·   intro s hs; apply DifferentiableAt.differentiableWithinAt; simp only [re_add_im]
                apply DifferentiableAt.const_cpow (by fun_prop); left; norm_cast; linarith
        ·   let U : Set ℂ := Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
            let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
            let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
            unfold fTempC fTempRR SmoothedChebyshevIntegrand
            simp only [re_add_im]
            have g_holc : HolomorphicOn g U := by
                intro u uInU
                apply DifferentiableAt.differentiableWithinAt; simp only [g]
                apply DifferentiableAt.mul
                ·   apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one
                    simp only [ofReal_inv, U] at uInU; unfold Rectangle at uInU
                    rw[Complex.mem_reProdIm] at uInU; have := uInU.1
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
                    rw [uIcc_of_le (by linarith)] at this; linarith [this.1]
                ·   unfold HPow.hPow instHPow
                    apply DifferentiableAt.const_cpow differentiableAt_fun_id
                    left; norm_cast; linarith
            have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
                simp only [one_mul, f]; exact riemannZetaLogDerivResidueBigO
            convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
            ext; simp [f, g]; ring





-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`.
-- theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
--     (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
--  sorry
