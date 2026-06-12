import PrimeNumberTheoremAnd.IEANTN.SecondaryDefinitions


namespace Buthe

open MeasureTheory Real Chebyshev

noncomputable def pi_star (x : ℝ) : ℝ := ∑' (k : ℕ), pi (x ^ (1 / (k : ℝ))) / (k : ℝ)

theorem theorem_2a {x : ℝ} (hx1 : 11 < x) (hx2 : x ≤ 10 ^ 19) :
    Eψ x ≤ 0.94 / sqrt x := by sorry

theorem theorem_2b {x : ℝ} (hx1 : 1423 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    x - θ x ≤ 1.95 * sqrt x := by sorry

theorem theorem_2c {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    x - θ x > 0.05 * sqrt x := by sorry

theorem theorem_2d {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    abs (li x - pi_star x) < sqrt x / log x := by sorry

theorem theorem_2e {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    li x - pi x ≤ (sqrt x / log x) * (1.95 + 3.9 / log x + 19.5 / (log x) ^ 2) := by sorry

theorem theorem_2f {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) : li x - pi x > 0 := by sorry

/- Table1.UpperandlowerboundsM± ψ(x)for t−ψ(t) √t in[x,2x] x M− ψ(x) M+ ψ(x) x M− ψ(x) M+ ψ(x) 1010 −.77 .85 1012 −.80 .81 2×1010 −.75 .64 2×1012 −.79 .76 4×1010 −.73 .80 4×1012 −.73 .73 8×1010 −.80 .86 8×1012 −.80 .76 16×1010 −.88 .68 16×1012 −.80 .68 32×1010 −.88 .78 32×1012 −.67 .93 64×1010 −.66 .74 64×1012 −.78 .77 x M− ψ(x) M+ ψ(x) x M− ψ(x) M+ ψ(x) 1014 −.79 .72 1016 −.88 .74 2×1014 −.60 .76 2×1016 −.87 .70 4×1014 −.65 .73 4×1016 −.65 .73 8×1014 −.81 .88 8×1016 −.82 .77 16×1014 −.66 .86 16×1016 −.71 .92 32×1014 −.74 .86 32×1016 −.78 .71 64×1014 −.73 .66 64×1016 −.94 .82 128×1016 −.94 .75 256×1016 −.82 .86 512×1016 −.83 .94 -/

def table_1 : List (ℝ × ℝ × ℝ) := [
  (10 ^ 10, -0.77, 0.85),
  (2 * 10 ^ 10, -0.75, 0.64),
  (4 * 10 ^ 10, -0.73, 0.80),
  (8 * 10 ^ 10, -0.80, 0.86),
  (16 * 10 ^ 10, -0.88, 0.68),
  (32 * 10 ^ 10, -0.88, 0.78),
  (64 * 10 ^ 10, -0.66, 0.74),
  (10 ^ 12, -0.80, 0.81),
  (2 * 10 ^ 12, -0.79, 0.76),
  (4 * 10 ^ 12, -0.73, 0.73),
  (8 * 10 ^ 12, -0.80, 0.76),
  (16 * 10 ^ 12, -0.80, 0.68),
  (32 * 10 ^ 12, -0.67, 0.93),
  (64 * 10 ^ 12, -0.78, 0.77),
  (10 ^ 14, -0.79, 0.72),
  (2 * 10 ^ 14, -0.60, 0.76),
  (4 * 10 ^ 14, -0.65, 0.73),
  (8 * 10 ^ 14, -0.81, 0.88),
  (16 * 10 ^ 14, -0.66, 0.86),
  (32 * 10 ^ 14, -0.74, 0.86),
  (64 * 10 ^ 14, -0.73, 0.66),
  (10 ^ 16, -0.88, 0.74),
  (2 * 10 ^ 16, -0.87, 0.70),
  (4 * 10 ^ 16, -0.65, 0.73),
  (8 * 10 ^ 16, -0.82, 0.77),
  (16 * 10 ^ 16, -0.71, 0.92),
  (32 * 10 ^ 16, -0.78, 0.71),
  (64 * 10 ^ 16, -0.94, 0.82),
  (128 * 10 ^ 16, -0.94, 0.75),
  (256 * 10 ^ 16, -0.82, 0.86),
  (512 * 10 ^ 16, -0.83, 0.94)
]

theorem sieve_bound :
    ∀ t ∈ Set.Icc (100 : ℝ) (5 * 10 ^ 10),
      -(0.8 : ℝ) ≤ (t - ψ t) / sqrt t ∧
        (t - ψ t) / sqrt t ≤ (0.81 : ℝ) := by
  sorry

theorem eq_6_2 (x Mψ_minus Mψ_plus : ℝ) (h : (x, Mψ_minus, Mψ_plus) ∈ table_1) :
    ∀ t ∈ Set.Icc x (2 * x), Mψ_minus ≤ (t - ψ t) / sqrt t ∧ (t - ψ t) / sqrt t ≤ Mψ_plus := by
    sorry

theorem table_1_to_32e12 :
    ∀ t ∈ Set.Icc (100 : ℝ) (32 * 10 ^ 12),
      -(0.88 : ℝ) ≤ (t - ψ t) / sqrt t ∧
        (t - ψ t) / sqrt t ≤ (0.86 : ℝ) := by
  intro t ht
  by_cases h5 : t ≤ 5 * 10 ^ 10
  · have h := sieve_bound t ⟨ht.1, h5⟩
    constructor <;> linarith
  · by_cases h8 : t ≤ 8 * 10 ^ 10
    · have h := eq_6_2 (4 * 10 ^ 10) (-0.73) 0.80
        (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h8]⟩
      constructor <;> linarith
    · by_cases h16 : t ≤ 16 * 10 ^ 10
      · have h := eq_6_2 (8 * 10 ^ 10) (-0.80) 0.86
          (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h16]⟩
        constructor <;> linarith
      · by_cases h32 : t ≤ 32 * 10 ^ 10
        · have h := eq_6_2 (16 * 10 ^ 10) (-0.88) 0.68
            (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h32]⟩
          constructor <;> linarith
        · by_cases h64 : t ≤ 64 * 10 ^ 10
          · have h := eq_6_2 (32 * 10 ^ 10) (-0.88) 0.78
              (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h64]⟩
            constructor <;> linarith
          · by_cases h128 : t ≤ 128 * 10 ^ 10
            · have h := eq_6_2 (64 * 10 ^ 10) (-0.66) 0.74
                (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h128]⟩
              constructor <;> linarith
            · by_cases h2e12 : t ≤ 2 * 10 ^ 12
              · have h := eq_6_2 (10 ^ 12) (-0.80) 0.81
                  (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h2e12]⟩
                constructor <;> linarith
              · by_cases h4e12 : t ≤ 4 * 10 ^ 12
                · have h := eq_6_2 (2 * 10 ^ 12) (-0.79) 0.76
                    (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h4e12]⟩
                  constructor <;> linarith
                · by_cases h8e12 : t ≤ 8 * 10 ^ 12
                  · have h := eq_6_2 (4 * 10 ^ 12) (-0.73) 0.73
                      (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h8e12]⟩
                    constructor <;> linarith
                  · by_cases h16e12 : t ≤ 16 * 10 ^ 12
                    · have h := eq_6_2 (8 * 10 ^ 12) (-0.80) 0.76
                        (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [h16e12]⟩
                      constructor <;> linarith
                    · have h := eq_6_2 (16 * 10 ^ 12) (-0.80) 0.68
                        (by norm_num [table_1]) t ⟨by nlinarith, by nlinarith [ht.2]⟩
                      constructor <;> linarith

private lemma normalized_bounds_of_Eψ {t K : ℝ} (ht : 0 < t)
    (h : Eψ t ≤ K / sqrt t) :
    -K ≤ (t - ψ t) / sqrt t ∧ (t - ψ t) / sqrt t ≤ K := by
  have hsqrt_pos : 0 < sqrt t := Real.sqrt_pos.mpr ht
  have hdiv_sqrt : t / sqrt t = sqrt t := by
    rw [div_eq_iff hsqrt_pos.ne']
    rw [← sq, Real.sq_sqrt ht.le]
  have h_abs : |ψ t - t| ≤ K * sqrt t := by
    change |ψ t - t| / t ≤ K / sqrt t at h
    have hmul := (div_le_iff₀ ht).mp h
    calc
      |ψ t - t| ≤ (K / sqrt t) * t := hmul
      _ = K * sqrt t := by
        calc
          (K / sqrt t) * t = K * (t / sqrt t) := by ring
          _ = K * sqrt t := by rw [hdiv_sqrt]
  have h_abs' : |t - ψ t| ≤ K * sqrt t := by
    simpa [abs_sub_comm] using h_abs
  constructor
  · rw [le_div_iff₀ hsqrt_pos]
    nlinarith [(abs_le.mp h_abs').1]
  · rw [div_le_iff₀ hsqrt_pos]
    nlinarith [(abs_le.mp h_abs').2]

theorem theorem_2a_normalized :
    ∀ t ∈ Set.Icc (100 : ℝ) (10 ^ 19),
      -(0.94 : ℝ) ≤ (t - ψ t) / sqrt t ∧
        (t - ψ t) / sqrt t ≤ (0.94 : ℝ) := by
  intro t ht
  exact normalized_bounds_of_Eψ (by linarith [ht.1])
    (theorem_2a (by linarith [ht.1]) ht.2)

end Buthe
