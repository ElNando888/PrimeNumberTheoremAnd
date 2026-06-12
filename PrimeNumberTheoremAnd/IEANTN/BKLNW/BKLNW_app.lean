import PrimeNumberTheoremAnd.IEANTN.ZetaSummary
import PrimeNumberTheoremAnd.IEANTN.PrimaryDefinitions
import PrimeNumberTheoremAnd.IEANTN.FioriKadiriSwidinsky.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_app_tables
import PrimeNumberTheoremAnd.IEANTN.LogTables
import PrimeNumberTheoremAnd.IEANTN.Buthe


namespace BKLNW_app

open Real Chebyshev

structure Inputs where
  H : ℝ
  hH : riemannZeta.RH_up_to H
  R : ℝ
  hR : riemannZeta.classicalZeroFree R
  ZDB : zero_density_bound

noncomputable def Inputs.default : Inputs where
  H := 2445999556030
  hH := GW_theorem
  R := 5.5666305  -- a slightly more conservative value of 5.573412 was used in the paper
  hR := MT_theorem_1
  ZDB := FKS.corollary_2_9_merged -- stronger than the Kadiri-Lumley-Ng input used here

theorem bklnw_eq_A_7 (x T : ℝ) (hx : x ≥ exp 1000)
    (hT1 : 50 < T) (hT2 : T ≤ x) :
    ∃ E, (ψ x - x) / x =
      riemannZeta.zeroes_sum (Set.Icc 0 1)
        (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ) + E ∧
      ‖E‖ ≤ 2 * (log x) ^ 2 / T := by
  sorry

noncomputable def bklnw_eq_A_8 (b T : ℝ) : ℝ :=
  2 * b ^ 2 / T

noncomputable def Sigma₁ (x T δ : ℝ) : ℂ :=
  riemannZeta.zeroes_sum (Set.Ico 0 (1 - δ))
    (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ)

noncomputable def Sigma₂ (x T δ : ℝ) : ℂ :=
  riemannZeta.zeroes_sum (Set.Icc (1 - δ) 1)
    (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ)

theorem bklnw_eq_A_9 (x T δ : ℝ) (hδ1 : 0 ≤ δ) (hδ2 : δ ≤ 1) :
    riemannZeta.zeroes_sum (Set.Icc 0 1)
      (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ) =
    Sigma₁ x T δ + Sigma₂ x T δ := by
  set I₁ : Set ℝ := Set.Ico 0 (1 - δ)
  set I₂ : Set ℝ := Set.Icc (1 - δ) 1
  set J  : Set ℝ := Set.Ioo (-T) T
  set g  : ℂ → ℂ := fun ρ ↦ (x ^ (ρ - 1) / ρ) * (riemannZeta.order ρ)
  change ∑' ρ : riemannZeta.zeroes_rect (Set.Icc 0 1) J, g ρ = _
  have hI : Set.Icc 0 1 = I₁ ∪ I₂ := (Set.Ico_union_Icc_eq_Icc
    (sub_nonneg_of_le hδ2) (sub_le_self 1 hδ1)).symm
  have hdisj : Disjoint (riemannZeta.zeroes_rect I₁ J) (riemannZeta.zeroes_rect I₂ J) :=
    riemannZeta.zeroes_rect_disjoint₁ I₁ I₂ J
      (Set.disjoint_left.2 fun _ hx1 hx2 ↦ not_le.2 hx1.2 hx2.1)
  have hfin : (riemannZeta.zeroes_rect (Set.Icc 0 1) J).Finite := by
    rw [riemannZeta.zeroes_rect_eq]
    refine (riemannZeta.zeroes_on_Compact_finite' ?_).subset
      (Set.inter_subset_inter (Set.inter_subset_inter_right _
        (Set.preimage_mono Set.Ioo_subset_Icc_self)) le_rfl)
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  rw [hI, ← riemannZeta.zeroes_rect_union] at hfin ⊢
  refine Summable.tsum_union_disjoint hdisj ?_ ?_
  · exact (hfin.subset Set.subset_union_left).summable g
  · exact (hfin.subset Set.subset_union_right).summable g

theorem bklnw_eq_A_10 (x T δ : ℝ) (hδ : 0.001 ≤ δ) :
    ‖Sigma₁ x T δ‖ ≤
      exp (-δ * log x) *
        (1 / (2 * π) * (log (T / (2 * π))) ^ 2 +
          1.8642) := by
  sorry

noncomputable def s₁ (b δ T : ℝ) : ℝ :=
  exp (-δ * b) *
    (1 / (2 * π) * (log (T / (2 * π))) ^ 2 +
      1.8642)

theorem bklnw_eq_A_12 (I : Inputs)
    (x T δ lambda : ℝ) (hlambda : 1 < lambda)
    (hx : 1 < x) (hT : 0 < T) (hTH : I.H < T)
    (hσ : 1 - δ ∈ I.ZDB.σ_range) (hT₀ : I.ZDB.T₀ ≤ I.H) :
    let K := ⌊log (T / I.H) / log lambda⌋₊ + 1
    ‖Sigma₂ x T δ‖ ≤
      2 * ∑ k ∈ Finset.range K,
        (lambda ^ (k + 1) *
          x ^ (-(1 / (I.R * log (T / lambda ^ k)))) /
          T) *
        I.ZDB.N (1 - δ) (T / lambda ^ k) := by
  sorry

theorem bklnw_eq_A_13 (I : Inputs)
    (x T δ lambda : ℝ) (hlambda : 1 < lambda)
    (hx : 1 < x) (hT : 0 < T) (hTH : I.H < T)
    (hσ : 1 - δ ∈ I.ZDB.σ_range) (hT₀ : I.ZDB.T₀ ≤ I.H) :
    let K := ⌊log (T / I.H) / log lambda⌋₊ + 1
    ‖Sigma₂ x T δ‖ ≤ (2 * lambda / T) *
      ∑ k ∈ Finset.range K,
        exp (k * log lambda -
          (log x) / (I.R * (log T -
            k * log lambda))) *
        (I.ZDB.c₁ (1 - δ) *
          (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
          (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
        I.ZDB.c₂ (1 - δ) *
          (log (T / lambda ^ k)) ^ 2) := by
  have h4 (k : ℕ) : exp ((k : ℝ) * log lambda - (log x) / (I.R * (log T - (k : ℝ) * log lambda))) =
      lambda ^ k * x ^ (-(1 / (I.R * log (T / lambda ^ k)))) := by
    rw [Real.log_div hT.ne' (by positivity), Real.log_pow, sub_eq_add_neg,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
      Real.rpow_def_of_pos (by positivity), mul_neg, mul_one_div]
  refine (bklnw_eq_A_12 I x T δ lambda hlambda hx hT hTH hσ hT₀).trans (le_of_eq ?_)
  simp_rw [zero_density_bound.N, Finset.mul_sum, h4]; congr 1; ext k; ring

noncomputable def Inputs.s₂ (I : Inputs)
    (δ b : ℝ) (K : ℕ) (lambda T : ℝ) : ℝ :=
  (2 * lambda / T) *
    ∑ k ∈ Finset.range K,
      exp (k * log lambda -
        b / (I.R * (log T -
          k * log lambda))) *
      (I.ZDB.c₁ (1 - δ) *
        (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
        (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
      I.ZDB.c₂ (1 - δ) *
        (log (T / lambda ^ k)) ^ 2)

theorem bklnw_thm_15 (I : Inputs)
    (b₁ b₂ δ lambda T x : ℝ)
    (hb : 1000 ≤ b₁) (hb' : b₁ < b₂)
    (hδ : 0.001 ≤ δ) (hδ' : δ ≤ 0.025)
    (hlambda : 1 < lambda) (hR : 0 < I.R)
    (hσ : 1 - δ ∈ I.ZDB.σ_range)
    (hT₀ : I.ZDB.T₀ ≤ I.H) (hH : 50 ≤ I.H)
    (hT1 : I.H < T) (hT2 : T < exp b₁)
    (hx : x ∈ Set.Icc (exp b₁) (exp b₂)) :
    let K := ⌊log (T / I.H) / log lambda⌋₊ + 1
    ‖(ψ x - x) / x‖ ≤
      bklnw_eq_A_8 b₂ T + s₁ b₁ δ T +
        I.s₂ δ b₁ K lambda T := by
  intro K
  have hK : K = ⌊log (T / I.H) / log lambda⌋₊ + 1 := rfl
  -- with (hT50 : 50 < T) in place of hH this line becomes the hypothesis itself
  have hT50 : 50 < T := lt_of_le_of_lt hH hT1
  have hT : (0 : ℝ) < T := by linarith
  have hHpos : (0 : ℝ) < I.H := by linarith
  have hH1 : (1 : ℝ) < I.H := by linarith
  have hlam0 : (0 : ℝ) < lambda := by linarith
  have hloglam : (0 : ℝ) < log lambda := log_pos hlambda
  have hx1000 : x ≥ exp 1000 := le_trans (exp_le_exp.mpr hb) hx.1
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (exp_pos 1000) hx1000
  have hx1 : (1 : ℝ) < x := by
    have := add_one_le_exp (1000 : ℝ)
    linarith
  have hlogx₁ : b₁ ≤ log x := (le_log_iff_exp_le hxpos).mpr hx.1
  have hlogx₂ : log x ≤ b₂ := (log_le_iff_le_exp hxpos).mpr hx.2
  obtain ⟨E, hE, hEnorm⟩ := bklnw_eq_A_7 x T hx1000 hT50 (le_trans hT2.le hx.1)
  rw [bklnw_eq_A_9 x T δ (by linarith) (by linarith)] at hE
  have hcast : (((ψ x - x) / x : ℝ) : ℂ) = Sigma₁ x T δ + Sigma₂ x T δ + E := by
    push_cast
    exact hE
  have hnorm_eq : ‖(ψ x - x) / x‖ = ‖Sigma₁ x T δ + Sigma₂ x T δ + E‖ := by
    rw [← hcast]
    norm_cast
  have hE8 : ‖E‖ ≤ bklnw_eq_A_8 b₂ T := by
    refine hEnorm.trans ?_
    simp only [bklnw_eq_A_8]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hT.le)
    have h0 : (0 : ℝ) ≤ log x := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ b₂ - log x)
      (by linarith : (0 : ℝ) ≤ b₂ + log x)]
  have hS1 : ‖Sigma₁ x T δ‖ ≤ s₁ b₁ δ T := by
    refine (bklnw_eq_A_10 x T δ hδ).trans ?_
    simp only [s₁]
    refine mul_le_mul_of_nonneg_right (exp_le_exp.mpr ?_) (by positivity)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ)
      (by linarith : (0 : ℝ) ≤ log x - b₁)]
  have hS2 : ‖Sigma₂ x T δ‖ ≤ I.s₂ δ b₁ K lambda T := by
    have h13 : ‖Sigma₂ x T δ‖ ≤ (2 * lambda / T) *
        ∑ k ∈ Finset.range K,
          exp (k * log lambda -
            (log x) / (I.R * (log T -
              k * log lambda))) *
          (I.ZDB.c₁ (1 - δ) *
            (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
            (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
          I.ZDB.c₂ (1 - δ) *
            (log (T / lambda ^ k)) ^ 2) :=
      bklnw_eq_A_13 I x T δ lambda hlambda hx1 hT hT1 hσ hT₀
    refine h13.trans ?_
    simp only [Inputs.s₂]
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun k hk ↦ ?_) (div_nonneg (by linarith) hT.le)
    have hkK : k ≤ ⌊log (T / I.H) / log lambda⌋₊ := by
      have h := Finset.mem_range.mp hk
      rw [hK] at h
      omega
    have hHT : (1 : ℝ) ≤ T / I.H := by
      rw [div_eq_mul_inv, ← mul_inv_cancel₀ hHpos.ne']
      exact mul_le_mul_of_nonneg_right hT1.le (inv_nonneg.mpr hHpos.le)
    have hfloor : (k : ℝ) ≤ log (T / I.H) / log lambda :=
      le_trans (Nat.cast_le.mpr hkK)
        (Nat.floor_le (div_nonneg (log_nonneg hHT) hloglam.le))
    have hk' : (k : ℝ) * log lambda ≤ log (T / I.H) := by
      have h1 := mul_le_mul_of_nonneg_right hfloor hloglam.le
      rwa [div_mul_cancel₀ _ hloglam.ne'] at h1
    have hk'' : (k : ℝ) * log lambda ≤ log T - log I.H := by
      rwa [log_div hT.ne' hHpos.ne'] at hk'
    have hD : (0 : ℝ) < log T - (k : ℝ) * log lambda :=
      lt_of_lt_of_le (log_pos hH1) (by linarith)
    have hRD : (0 : ℝ) < I.R * (log T - (k : ℝ) * log lambda) := mul_pos hR hD
    have hTk : I.H ≤ T / lambda ^ k := by
      have h2 : exp (log I.H) ≤ exp (log T - (k : ℝ) * log lambda) :=
        exp_le_exp.mpr (by linarith)
      rwa [exp_log hHpos, exp_sub, exp_log hT, ← log_pow,
        exp_log (pow_pos hlam0 k)] at h2
    -- the density-bound bracket dominates N'(1-δ, T/λ^k), which is nonnegative
    have hN' : (0 : ℝ) ≤ riemannZeta.N' (1 - δ) (T / lambda ^ k) := by
      simp only [riemannZeta.N', riemannZeta.zeroes_sum, Pi.one_apply, one_mul]
      refine tsum_nonneg fun ρ ↦ ?_
      suffices h : (0 : ℤ) ≤ riemannZeta.order ↑ρ by exact_mod_cast h
      have hmem := ρ.2
      simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq,
        Set.mem_Ioo] at hmem
      have hne : (↑ρ : ℂ) ≠ 1 := by
        intro h1
        have h2 := hmem.1.2
        rw [h1, Complex.one_re] at h2
        exact lt_irrefl 1 h2
      have hana : AnalyticAt ℂ riemannZeta (↑ρ : ℂ) :=
        riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr hne)
      have hord := hana.meromorphicOrderAt_nonneg
      simp only [riemannZeta.order]
      cases horder : meromorphicOrderAt riemannZeta (↑ρ : ℂ) with
      | top => exact le_rfl
      | coe n =>
        rw [horder] at hord
        change (0 : ℤ) ≤ n
        exact_mod_cast hord
    have hBk : (0 : ℝ) ≤ I.ZDB.c₁ (1 - δ) *
        (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
        (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
        I.ZDB.c₂ (1 - δ) * (log (T / lambda ^ k)) ^ 2 :=
      le_trans hN' (I.ZDB.bound (T / lambda ^ k) (le_trans hT₀ hTk) (1 - δ) hσ)
    refine mul_le_mul_of_nonneg_right (exp_le_exp.mpr ?_) hBk
    have hdiv : b₁ / (I.R * (log T - (k : ℝ) * log lambda)) ≤
        log x / (I.R * (log T - (k : ℝ) * log lambda)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hlogx₁ (inv_nonneg.mpr hRD.le)
    linarith
  rw [hnorm_eq]
  calc ‖Sigma₁ x T δ + Sigma₂ x T δ + E‖
      ≤ ‖Sigma₁ x T δ‖ + ‖Sigma₂ x T δ‖ + ‖E‖ :=
        le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ bklnw_eq_A_8 b₂ T + s₁ b₁ δ T + I.s₂ δ b₁ K lambda T := by linarith

noncomputable def Inputs.k (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  (exp ((10 - 16 * σ) / 3 *
      (log x₀ / I.R) ^ (1 / 2 : ℝ)) *
    sqrt (log x₀ / I.R) ^ (5 - 2 * σ)) ^ (-1 : ℝ)

noncomputable def Inputs.c3 (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  2 * exp (-2 * (log x₀ / I.R) ^ (1 / 2 : ℝ)) *
    (log x₀) ^ 2 * I.k σ x₀

noncomputable def Inputs.c4 (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  x₀ ^ (σ - 1 : ℝ) *
    (2 * log x₀ / π / I.R + 1.8642) *
    I.k σ x₀

noncomputable def Inputs.c5 (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  8.01 * I.ZDB.c₂ σ *
    exp (-2 * (log x₀ / I.R) ^ (1 / 2 : ℝ)) *
    (log x₀ / I.R) * I.k σ x₀

noncomputable def Inputs.A (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  2.0025 * 2 ^ (5 - 2 * σ) * I.ZDB.c₁ σ +
    I.c3 σ x₀ + I.c4 σ x₀ + I.c5 σ x₀

noncomputable def Inputs.B (_ : Inputs)
    (σ : ℝ) : ℝ :=
  5 / 2 - σ

noncomputable def Inputs.C (_ : Inputs)
    (σ : ℝ) : ℝ :=
  16 * σ / 3 - 10 / 3

theorem thm_14 (I : Inputs) {x₀ σ x : ℝ}
    (hx₀ : x₀ ≥ 1000)
    (hσ : 0.75 ≤ σ ∧ σ < 1)
    (hx : x ≥ exp x₀) :
    Eψ x ≤ I.A σ x₀ *
      (log x / I.R) ^ (I.B σ) *
      exp (-I.C σ *
        (log x / I.R) ^ (1 / 2 : ℝ)) := by
  sorry

theorem bklnw_eq_A_26 (x : ℝ)
    (hx1 : 100 ≤ x) (hx2 : x ≤ 1e19) :
    Eψ x ≤ 0.94 / sqrt x :=
  Buthe.theorem_2a (by linarith) (by linarith)

theorem bklnw_lemma_15 (c B₀ B : ℝ)
    (hbound : ∀ x ∈ Set.Ioc B₀ B,
      Eψ x ≤ c / sqrt x)
    (ε : ℝ → ℝ)
    (hε : ∀ b₀ > 0, ∀ x ≥ exp b₀, Eψ x ≤ ε b₀)
    (b : ℝ)
    (hb : exp b ∈ Set.Ioc B₀ B)
    (hbpos : b > 0)
    (hcpos : c > 0)
    (hBpos : B > 0) :
    ∀ x ≥ exp b,
      Eψ x ≤ max (c / exp (b / 2))
        (ε (log B)) := by
  intro x hx
  by_cases! hcases : x ≤ B
  · have hlb : B₀ < x := by linarith [hx, hb.1]
    simp only [Set.Ioc, Set.mem_setOf_eq, and_imp] at hbound
    have hb : Eψ x ≤ c / sqrt x :=
      hbound x hlb hcases
    have hsqrtcomp : sqrt (exp b) ≤ sqrt x :=
      Real.sqrt_monotone hx
    have hidentity1 : exp (2 * (b / 2)) = exp (b / 2) ^ 2 := Real.exp_nat_mul (b / 2) 2
    have hidentity2 : 2 * (b / 2) = b := by ring
    simp only [hidentity2] at hidentity1
    have hnonneg : 0 ≤ exp (b / 2) := by
      positivity
    have hidentity3 : sqrt (exp b) = sqrt (exp (b / 2) ^ 2) := by
      simpa using congrArg Real.sqrt hidentity1
    simp only [Real.sqrt_sq hnonneg] at hidentity3
    have hsqrtcomp2 : exp (b / 2) ≤ sqrt x := by
      linarith
    have hsqrtpos : sqrt x > 0 := by
      linarith [exp_pos (b / 2)]
    have hsqrtcomp3 : c / sqrt x ≤ c / exp (b / 2) := by gcongr
    have hubcomp : c / exp (b / 2) ≤ max (c / exp (b / 2)) (ε (log B)) := le_max_left ..
    linarith
  · have hidentity : exp (log B) = B :=
      Real.exp_log hBpos
    have hBone : 1 < B := by
      linarith [hb.2, Real.one_lt_exp_iff.2 hbpos]
    have hlogBpos : 0 < log B :=
      Real.log_pos hBone
    specialize hε (log B) hlogBpos
    have hlb : x ≥ exp (log B) := by linarith
    specialize hε x hlb
    have hubcomp : ε (log B) ≤ max (c / exp (b / 2)) (ε (log B)) := le_max_right ..
    linarith

theorem bklnw_cor_15_1 (b : ℝ)
    (hb1 : log 11 < b)
    (hb2 : b ≤ 19 * log 10)
    (ε : ℝ → ℝ)
    (hε : ∀ b₀ > 0, ∀ x ≥ exp b₀,
      Eψ x ≤ ε b₀) :
    ∀ x ≥ exp b,
      Eψ x ≤ max (0.94 / exp (b / 2))
        (ε (19 * log 10)) := by
  have hlog11_pos : (0 : ℝ) < log 11 := by
    positivity
  have hbpos : b > 0 := by linarith
  have h10_19 : (10 : ℝ) ^ (19 : ℕ) > 0 := by
    positivity
  have hlog_eq : log ((10 : ℝ) ^ (19 : ℕ)) = 19 * log 10 := by
    rw [Real.log_pow]
    ring
  rw [← hlog_eq]
  apply bklnw_lemma_15 0.94 11
    ((10 : ℝ) ^ (19 : ℕ))
  · intro x hx
    exact Buthe.theorem_2a hx.1 hx.2
  · exact hε
  · constructor
    · have : Real.exp (Real.log 11) < Real.exp b := Real.exp_lt_exp.mpr hb1
      rwa [Real.exp_log (by norm_num : (11 : ℝ) > 0)] at this
    · rw [← hlog_eq] at hb2
      rw [← Real.exp_log (by positivity : (10 : ℝ) ^ (19 : ℕ) > 0)]
      exact Real.exp_le_exp.mpr hb2
  · exact hbpos
  · norm_num
  · exact h10_19

noncomputable def ℓ (c ε ξ : ℝ) : ℝ :=
  (c / sinh c) *
    sin (sqrt ((ξ * ε) ^ 2 - c ^ 2)) /
    sqrt ((ξ * ε) ^ 2 - c ^ 2)

/-- The modified Bessel function of the first kind of order zero,
$I_0(x) = \sum_{m \geq 0} (x/2)^{2m}/(m!)^2$, introduced for the closed form of the
Logan kernel transform below (not yet in Mathlib). -/
noncomputable def besselI0 (x : ℝ) : ℝ :=
  ∑' m : ℕ, (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2

noncomputable def η (c ε ξ : ℝ) : ℝ :=
  if |ξ| ≤ ε then
    c / (2 * ε * sinh c) * besselI0 (c * sqrt (1 - (ξ / ε) ^ 2))
  else 0

noncomputable def pre_μ (c ε t : ℝ) : ℝ :=
  -∫ τ in Set.Iic t, η c ε τ

noncomputable def μ (c ε t : ℝ) : ℝ :=
  if t < 0 then pre_μ c ε t
  else if t > 0 then -pre_μ c ε (-t)
  else 0

noncomputable def ν (c ε t : ℝ) : ℝ :=
  ∫ τ in Set.Iic t, μ c ε τ

theorem bklnw_thm_16 (ε c x₀ α : ℝ)
    (hε : 0 < ε ∧ ε < 1e-3)
    (hc : 3 ≤ c)
    (hx₀ : 100 ≤ x₀)
    (hα : 0 ≤ α ∧ α < 1)
    (hB0 : 2 * max (μ c 1 α) 0 <
      ε * rexp (-ε) * x₀ * |ν c 1 α|)
    (hRH : riemannZeta.RH_up_to (c / ε))
    (x : ℝ)
    (hx : x ≥ rexp (ε * α) * x₀) :
    let E₁ :=
      rexp (2 * ε) * log (rexp ε * x₀) *
        (2 * ε * |ν c 1 α| /
          log ((ε * rexp (-ε) * x₀ *
            |ν c 1 α|) / (2 * max (μ c 1 α) 0)) +
        2.01 * ε / sqrt x₀ +
        log (log (2 * x₀ ^ 2)) /
          (2 * x₀)) +
      exp (ε * α) - 1
    let E₂ :=
      0.16 * (1 + x₀ ^ (-1 : ℝ)) / sinh c *
        exp (0.71 * sqrt (c * ε)) *
        log (c / ε)
    let E₃ :=
      2 / sqrt x₀ *
        riemannZeta.zeroes_sum (Set.Icc 0 1)
          (Set.Ioo 0 (c / ε))
          (fun ρ ↦ ℓ c ε ρ.im / ρ.im) +
      2 / x₀
    Eψ x ≤ exp (ε * α) * (E₁ + E₂ + E₃) := by
  sorry


theorem theorem_2 : ∀ b ≥ 0, ∀ x ≥ exp b,
    |ψ x - x| ≤ table_8_ε b * x := by
  sorry

theorem bklnw_cor_15_1' (b : ℝ)
    (hb1 : log 11 < b)
    (hb2 : b ≤ 19 * log 10) :
    ∀ x ≥ exp b,
      Eψ x ≤
        max (0.94 / exp (b / 2))
          (1.93378e-8 * table_8_margin) := by
  intro x hx
  grw [bklnw_cor_15_1 b hb1 hb2 table_8_ε
    (fun b₀ hb₀ x hx ↦ by
      grw [Eψ,
        div_le_iff₀
          (lt_of_lt_of_le (by positivity) hx),
        theorem_2 b₀ hb₀.le x hx]) x hx]
  apply max_le_max_left
  suffices 43 < 19 * Real.log 10 ∧
      19 * Real.log 10 < 44 by
    grw [table_8_ε.le_simp (19 * log 10)
      (by grind)]
    grind [table_8_ε']
  constructor <;>
    nlinarith [LogTables.log_10_gt,
      LogTables.log_10_lt]

end BKLNW_app
