import PrimeNumberTheoremAnd.IEANTN.SecondarySummary
import PrimeNumberTheoremAnd.IEANTN.PrimeTables


namespace Goldbach

def even_conjecture (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 4 H, Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

lemma even_conjecture_mono (H H' : ℕ) (h : even_conjecture H) (hh : H' ≤ H) :
    even_conjecture H' := by
  intro n hn
  apply h
  grind

theorem even_goldbach_test : even_conjecture 30 := by
  intro n hn he
  fin_cases hn
  all_goals try grind
  · exact ⟨2, 2, by decide⟩
  · exact ⟨3, 3, by decide⟩
  · exact ⟨3, 5, by decide⟩
  · exact ⟨5, 5, by decide⟩
  · exact ⟨5, 7, by decide⟩
  · exact ⟨7, 7, by decide⟩
  · exact ⟨5, 11, by decide⟩
  · exact ⟨7, 11, by decide⟩
  · exact ⟨7, 13, by decide⟩
  · exact ⟨11, 11, by decide⟩
  · exact ⟨11, 13, by decide⟩
  · exact ⟨13, 13, by decide⟩
  · exact ⟨11, 17, by decide⟩
  · exact ⟨13, 17, by decide⟩

def odd_conjecture (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 7 H, Odd n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

lemma odd_conjecture_mono (H H' : ℕ) (h : odd_conjecture H) (hh : H' ≤ H) :
    odd_conjecture H' := by
  intro n hn
  apply h
  grind

theorem even_to_odd_goldbach_triv (H : ℕ) (h : even_conjecture H) : odd_conjecture (H + 3) := by
  intro n hn ⟨k, hk⟩
  simp only [Finset.mem_Icc] at hn
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3)
    (by simp only [Finset.mem_Icc]; omega) ⟨k - 1, by omega⟩
  exact ⟨p, q, 3, hp, hq, by norm_num, by omega⟩

theorem odd_goldbach_test : odd_conjecture 33 := even_to_odd_goldbach_triv 30 even_goldbach_test

theorem even_to_odd_goldbach (x₀ H Δ : ℕ)
    (hprime : ∀ x ≥ x₀, HasPrimeInInterval (x * (1 - 1 / Δ)) (x / Δ))
    (heven : even_conjecture H) (hodd : odd_conjecture (x₀ + 4)) :
    odd_conjecture ((H - 4) * Δ + 4) := by
  by_cases! hH : H < 4
  · simp_all [tsub_eq_zero_of_le hH.le, odd_conjecture]
  by_cases! Δ ≤ 1
  · interval_cases Δ
    · simp_all [odd_conjecture]
    · simp_all [odd_conjecture_mono (H + 3) H (even_to_odd_goldbach_triv H heven) (by linarith)]
  · intro n h ho
    by_cases! hn33 : n ≤ 8
    · exact odd_goldbach_test n (by grind : n ∈ Finset.Icc 7 33) ho
    by_cases! hn : n ≤ x₀ + 4
    · exact hodd n (by grind : n ∈ Finset.Icc 7 (x₀ + 4)) ho
    · obtain ⟨p, hp⟩ := hprime (n - 4) (by grind : n - 4 ≥ x₀)
      have hnpe : Even (n - p) :=
        have h2p : 2 < p := by
          rw [← Nat.cast_lt (α := ℝ)]
          calc
          _ = (8 - 4) * (1 - 1 / 2 : ℝ) := by norm_num
          _ < (n - 4) * (1 -  1 / 2 : ℝ) := by gcongr; norm_cast
          _ ≤ ↑(n - 4) * (1 -  1 / Δ : ℝ) := by gcongr <;> norm_cast; grind
          _ < p := hp.2.1
        ho.tsub_odd (hp.1.odd_of_ne_two h2p.ne')
      have hnp : (n - p) ∈ Finset.Icc 4 H := by
        have hpn4 : p ≤ n - 4 := by simpa [field] using hp.2.2
        have hpn : p ≤ n := hpn4.trans tsub_le_self
        refine Finset.mem_Icc.2 ⟨?_, ?_⟩
        · exact (le_tsub_iff_le_tsub (by grind) hpn).2 hpn4
        · have := hp.2.1
          rw [← Nat.cast_le (α := ℝ), Nat.cast_sub hpn]
          rw [Nat.cast_sub (by grind), mul_sub, mul_one, ← sub_add_eq_sub_sub,
            sub_lt_comm] at this
          refine this.le.trans ?_
          calc
          _ ≤ 4 + ((↑(H - 4) * Δ + 4) - 4) * (1 / Δ : ℝ) := by gcongr <;> norm_cast; grind
          _ ≤ _ := by simp [field, Nat.cast_sub hH]
      obtain ⟨q, r, hqr⟩ := heven (n - p) hnp hnpe
      refine ⟨p, q, r, hp.1, hqr.1, hqr.2.1, ?_⟩
      grind

theorem richstein_goldbach : even_conjecture (4 * 10 ^ 14) := by sorry

theorem ramare_saouter_odd_goldbach : odd_conjecture 11325599999999886744004 := by
  have h1 := even_to_odd_goldbach 10726905042 (4 * 10 ^ 14) 28314000
    (fun x hx => RamareSaouter2003.has_prime_in_interval x (by norm_cast : (x : ℝ) > 10726905041))
    richstein_goldbach
  have h2 := odd_conjecture_mono (4 * 10 ^ 14 + 3) 10726905046
    (even_to_odd_goldbach_triv _ richstein_goldbach)
  norm_num at *
  exact h1 h2

theorem e_silva_herzog_piranian_goldbach : even_conjecture (4 * 10 ^ 18) := by sorry

theorem helfgott_odd_goldbach_finite : odd_conjecture (11325 * 10 ^ 22) := by
  have h1 := even_to_odd_goldbach 10726905042 (4 * 10 ^ 18) 28314000
    (fun x hx => RamareSaouter2003.has_prime_in_interval x (by norm_cast : (x : ℝ) > 10726905041))
    e_silva_herzog_piranian_goldbach
  have h2 := odd_conjecture_mono (4 * 10 ^ 18 + 3) 10726905046
    (even_to_odd_goldbach_triv _ e_silva_herzog_piranian_goldbach)
  norm_num at *
  exact odd_conjecture_mono _ _ (h1 h2) (by grind)


theorem e_silva_herzog_piranian_goldbach_ext : even_conjecture (4 * 10 ^ 18 + 4) := by
  intro n hn he
  simp only [Finset.mem_Icc] at hn
  by_cases! h1 : n ≤ 4 * 10 ^ 18
  · exact e_silva_herzog_piranian_goldbach n (Finset.mem_Icc.mpr ⟨hn.1, h1⟩) he
  · obtain ⟨k, hk⟩ := he
    have : n = 4000000000000000002 ∨ n = 4000000000000000004 := by omega
    rcases this with rfl | rfl
    · exact ⟨211, 3999999999999999791, prime_211, prime_3999999999999999791, by norm_num⟩
    · exact ⟨313, 3999999999999999691, prime_313, prime_3999999999999999691, by norm_num⟩

theorem kadiri_lumley_odd_goldbach_finite : odd_conjecture (1966196911 * 4 * 10 ^ 18) := by
  have h1 (x) (hx : x ≥ Real.exp 59) := KadiriLumley.has_prime_in_interval (Real.exp 59) x
    61 4.589e-9 20499925573 0.93 0.4522 1946282821 hx
  simp only [ge_iff_le, KadiriLumley.Table_2, Real.log_exp, List.mem_cons, Prod.mk.injEq,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, and_false, and_self, Nat.succ_ne_self, List.not_mem_nil,
    or_self, or_false, or_true, forall_const] at h1
  have h2 := even_to_odd_goldbach (⌈Real.exp 59⌉₊) (4 * 10 ^ 18 + 4) 1946282821
    (fun x hx => h1 x (Nat.le_of_ceil_le hx)) e_silva_herzog_piranian_goldbach_ext
  have h3 : ⌈Real.exp 59⌉₊ + 4 ≤ 11325 * 10 ^ 22 := by
    have : Real.exp 59 + 4 + 1 ≤ 11325 * 10 ^ 22 := by interval_decide
    grw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.ceil_lt_add_one (Real.exp_nonneg _)]
    grind
  have h4 := h2 (odd_conjecture_mono _ (⌈Real.exp 59⌉₊ + 4) helfgott_odd_goldbach_finite h3)
  have p1 (x) (hx : x ≥ Real.exp 60) := KadiriLumley.has_prime_in_interval (Real.exp 60) x
    61 4.588e-9 20504393735 0.93 0.4527 1966196911 hx
  simp only [ge_iff_le, KadiriLumley.Table_2, Real.log_exp, List.mem_cons, Prod.mk.injEq,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, and_false, and_self, Nat.succ_ne_self, List.not_mem_nil,
    or_self, or_false, or_true, forall_const] at p1
  have p2 := even_to_odd_goldbach (⌈Real.exp 60⌉₊) (4 * 10 ^ 18 + 4) 1966196911
    (fun x hx => p1 x (Nat.le_of_ceil_le hx)) e_silva_herzog_piranian_goldbach_ext
  norm_num at *
  have p3 : ⌈Real.exp 60⌉₊ + 4 ≤ 7785131284000000000000000004 := by
    have : Real.exp 60 + 4 + 1 ≤ 7785131284000000000000000004 := by interval_decide
    grw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.ceil_lt_add_one (Real.exp_nonneg _)]
    grind
  exact odd_conjecture_mono _ _
    (p2 (odd_conjecture_mono _ (⌈Real.exp 60⌉₊ + 4) h4 p3)) (by grind)

end Goldbach
