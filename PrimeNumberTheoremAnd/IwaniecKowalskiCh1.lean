import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

open scoped ArithmeticFunction.Moebius

open scoped LSeries.notation

namespace ArithmeticFunction



/-- `τ` (tau) is the divisor count function, equal to `σ 0`. -/
abbrev tau : ArithmeticFunction ℕ := σ 0

@[inherit_doc tau]
scoped notation "τ" => tau

variable {R : Type*}

/--
An arithmetic function `IsAdditive` if it satisfies the property that for any two coprime natural numbers `m` and `n`, the function evaluated at their product equals the sum of the function evaluated at each number individually.
-/
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Coprime m n → f (m * n) = f m + f n

def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

lemma IsCompletelyAdditive.isAdditive [AddZeroClass R] {f : ArithmeticFunction R}
    (hf : IsCompletelyAdditive f) : IsAdditive f :=
  fun hm hn _ ↦ hf hm hn

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

lemma unique_divisor_decomposition {a b d : ℕ} (hab : Coprime a b) (hd : d ∣ a * b) :
    ∃! p : ℕ × ℕ, p.1 ∣ a ∧ p.2 ∣ b ∧ p.1 * p.2 = d := by
  sorry -- UPSTREAMED TO MATHLIB #36495

/-- If `f` is a multiplicative arithmetic function, then for coprime `a` and `b`, we have $\sum_{d | ab} f(d) = (\sum_{d | a} f(d)) \cdot (\sum_{d | b} f(d))$. -/
theorem sum_divisors_mul_of_coprime {R : Type*} [CommRing R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {a b : ℕ} (hab : Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ d ∈ (a * b).divisors, f d = (∑ d ∈ a.divisors, f d) * (∑ d ∈ b.divisors, f d) := by
  sorry -- UPSTREAMED TO MATHLIB #36495

/-- If `g` is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p | n} (1 - g(p))$. -/
theorem sum_moebius_pmul_eq_prod_one_sub {R : Type*} [CommRing R]
    {g : ArithmeticFunction R} (hg : g.IsMultiplicative) (n : ℕ) : n ≠ 0 →
    ∑ d ∈ n.divisors, (moebius d : R) * g d = ∏ p ∈ n.primeFactors, (1 - g p) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one => exact fun _ ↦ by simp [hg.map_one]
  | prime_pow p k hp hk =>
    refine fun _ ↦ ?_
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, sum_divisors_prime_pow hp,
      Finset.sum_range_succ']
    simp only [pow_zero, moebius_apply_one, Int.cast_one, hg.map_one, mul_one]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hk)]
    · simp only [zero_add, pow_one, moebius_apply_prime hp, Int.reduceNeg, Int.cast_neg,
        Int.cast_one, neg_mul, one_mul]; ring
    · intro i _ hi
      have hnsq : ¬Squarefree (p ^ (i + 1)) := by
        rw [Nat.squarefree_pow_iff hp.ne_one (by omega : i + 1 ≠ 0)]
        omega
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simp
  | coprime a b ha hb hab iha ihb =>
    intro hn
    rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors,
        ← iha (by omega), ← ihb (by omega)]
    let h : ArithmeticFunction R := ⟨fun n ↦ ↑(moebius n) * g n, by simp⟩
    have h_mul : h.IsMultiplicative := by
      refine ⟨?_, ?_⟩
      · simp [h, ArithmeticFunction.coe_mk, hg.left]
      · intro m n hmn
        simp only [h, ArithmeticFunction.coe_mk]
        rw [ArithmeticFunction.isMultiplicative_moebius.right hmn, hg.right hmn]
        push_cast
        ring
    exact sum_divisors_mul_of_coprime h_mul hab (by omega) (by omega)

/-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/
theorem zeta_mul_zeta : (ζ : ArithmeticFunction ℕ) * ζ = τ := by
  ext n; unfold zeta tau sigma
  simp only [mul_apply, coe_mk, mul_ite, mul_zero, mul_one, pow_zero, sum_const, smul_eq_mul]
  have key : ∀ x ∈ n.divisorsAntidiagonal, (if x.2 = 0 then 0 else if x.1 = 0 then 0 else 1) = 1 := by
    intro ⟨a, b⟩ hx
    have := Nat.mem_divisorsAntidiagonal.mp hx
    simp [mul_ne_zero_iff.mp (this.1 ▸ this.2)]
  simp_rw [Finset.sum_congr rfl key, Finset.card_eq_sum_ones, Finset.sum_const]
  simp only [smul_eq_mul, mul_one, ← Nat.map_div_right_divisors]
  exact card_map { toFun := fun d ↦ (d, n / d), inj' := fun x x_1 ↦ congr_arg Prod.fst }

/-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/
theorem LSeries_tau_eq_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗τ) s = riemannZeta s ^ 2 := by
  have h1 : LSeries (↗(ζ * ζ)) s = LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := by
    congr 1; ext n; simp only [← natCoe_mul, natCoe_apply]
  have h2 : LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s = LSeries (↗ζ) s * LSeries (↗ζ) s :=
    LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs) (LSeriesSummable_zeta_iff.mpr hs)
  rw [← zeta_mul_zeta, h1, h2, LSeries_zeta_eq_riemannZeta hs, pow_two]

/-- `d k` is the k-fold divisor function: the number of ways to write n as an ordered
    product of k natural numbers. Equivalently, the Dirichlet convolution of ζ with
    itself k times. We have `d 0 = 1` (identity), `d 1 = ζ`, `d 2 = σ 0`. -/
def d (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

/-- `d 0` is the multiplicative identity (indicator at 1). -/
theorem d_zero : d 0 = 1 := pow_zero zeta

/-- `d 1` is `ζ`. -/
theorem d_one : d 1 = zeta := pow_one zeta

/-- `d 2` is the classical divisor count function `τ`. -/
theorem d_two : d 2 = τ := by simp [d, sq, zeta_mul_zeta]

/-- Recurrence: `d_(k+1) = d_k * ζ`. -/
theorem d_succ (k : ℕ) : d (k + 1) = d k * zeta := pow_succ zeta k

/-- The L-series for `d k` is summable -/
theorem LSeries_d_summable (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
      LSeriesSummable (↗(d k : ArithmeticFunction ℂ)) s := by
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, one_eq_delta]
    exact (hasSum_single 1 fun n hn => by simp [LSeries.term_delta, hn]).summable
  | succ k ih =>
    rw [(LSeriesSummable_congr s (fun {n} _ => show (d (k + 1) : ArithmeticFunction ℂ) n =
      ((d k : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]))]
    exact LSeriesSummable_mul ih (LSeriesSummable_zeta_iff.mpr hs)

/-- The L-series of `d k` equals `ζ(s)^k` for `Re(s) > 1`. -/
theorem LSeries_d_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(d k)) s = riemannZeta s ^ k := by
  change LSeries (↗(d k : ArithmeticFunction ℂ)) s = riemannZeta s ^ k
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, pow_zero, one_eq_delta]
    exact congr_fun LSeries_delta s
  | succ j ih =>
    have hζ : LSeriesSummable (↗(ζ : ArithmeticFunction ℂ)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    rw [pow_succ, LSeries_congr (fun {n} _ => show (d (j + 1) : ArithmeticFunction ℂ) n =
        ((d j : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]) s,
        LSeries_mul' (LSeries_d_summable j hs) hζ, ih]
    congr 1
    exact LSeries_zeta_eq_riemannZeta hs


/-- `d k` is multiplicative for all `k`. -/
theorem d_isMultiplicative (k : ℕ) : (d k).IsMultiplicative := by
  induction k with
  | zero => rw [d_zero]; exact isMultiplicative_one
  | succ k ih =>
      rw [d_succ]
      exact ih.mul isMultiplicative_zeta

/- MOVE HELPER LEMMA ESLEWHERE?? Not used in this file, but seems potentially useful? -/
theorem Nat.sum_divisorsAntidiagonal_prime_pow {α : Type u_1} [AddCommMonoid α] [HMul α α α] {k p : ℕ} {f : ℕ × ℕ → α} (h : Nat.Prime p) :
∑ x ∈ (p ^ k).divisorsAntidiagonal, f x = ∑ n ∈ Finset.range (k + 1), f (p ^ n, p ^ (k - n)) := by
  sorry

/-- Explicit formula: `d k (p^a) = (a + k - 1).choose (k - 1) for prime p` for `k ≥ 1`. -/
theorem d_apply_prime_pow {k : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    d k (p ^ a) = (a + k - 1).choose (k - 1) := by
  obtain ⟨k', rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction k' generalizing a with
  | zero => simp [d_one, hp.ne_zero]
  | succ k' ih =>
      rw [d_succ, mul_zeta_apply, sum_divisors_prime_pow hp]
      simp_rw [fun i ↦ ih i (succ_pos _)]
      simpa [add_assoc, add_left_comm, add_comm] using sum_range_add_choose a k'

/-- (1.25) in Iwaniec-Kowalski: a formula for `d_k` for all `n`. -/
lemma d_apply {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    d k n = ∏ p ∈ n.primeFactors, (n.factorization p + k - 1).choose (k - 1) := by
  have hmult : (d k).IsMultiplicative := d_isMultiplicative k
  rw [hmult.multiplicative_factorization (d k) hn, prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl (fun p hp => ?_)
  simpa using d_apply_prime_pow hk (prime_of_mem_primeFactors hp) _

/-- Divisor power sum with exponents in an arbitrary semiring `R`. -/
noncomputable def sigmaR {R : Type*} [Semiring R] [HPow R R R] (s : R) : ArithmeticFunction R where
  toFun := fun n ↦ ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

@[inherit_doc]
scoped[ArithmeticFunction] notation "σᴿ" => ArithmeticFunction.sigmaR

/-- For natural exponents, sigmaR agrees with sigma. -/
lemma sigmaR_natCast (k n : ℕ) :
    σᴿ k n = σ k n := by
  unfold sigmaR sigma
  simp only [cast_id, coe_mk]

lemma sigmaR_apply {n : ℕ} {s : ℂ} : σᴿ s n = ∑ d ∈ divisors n, (d : ℂ) ^ s := by
  rfl

lemma sigmaR_natCast' (k n : ℕ) :
    σᴿ (k : ℂ) n = σᴿ k n := by
  simp only [sigmaR_apply, Complex.cpow_natCast, sigmaR_natCast, sigma_apply, cast_sum, cast_pow]

lemma sigmaR_apply_prime_pow {p i : ℕ} {s : ℂ} (hp : p.Prime) :
    σᴿ s (p ^ i) = ∑ j ∈ .range (i + 1), (p : ℂ) ^ (j * s) := by
  simp only [sigmaR_apply, divisors_prime_pow hp, sum_map, Function.Embedding.coeFn_mk, cast_pow]
  congr 1
  funext x
  exact Eq.symm (Complex.natCast_cpow_natCast_mul p x s)

lemma sigmaR_one_apply (n : ℕ) : σᴿ (1 : ℂ) n = ∑ d ∈ divisors n, d := by
  simp only [sigmaR_apply, Complex.cpow_one, cast_sum]

lemma sigmaR_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (1 : ℂ) (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp only [sigmaR_apply_prime_pow hp, mul_one, Complex.cpow_natCast, cast_sum, cast_pow]

lemma sigmaR_eq_sum_div {n : ℕ} {s : ℂ} :
    σᴿ s n = ∑ d ∈ divisors n, ((n / d) : ℂ) ^ s := by
  rw[sigmaR_apply, ← sum_div_divisors]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw[Nat.cast_div (dvd_of_mem_divisors hd) (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]

lemma sigmaR_zero_apply (n : ℕ) :
    σᴿ (0 : ℂ) n = #n.divisors := by
  simp only [sigmaR_apply, Complex.cpow_zero, sum_const, nsmul_eq_mul, mul_one]

lemma sigmaR_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (0 : ℂ) (p ^ i) = i + 1 := by
  simp only [sigmaR_apply_prime_pow hp, mul_zero, Complex.cpow_zero, sum_const, card_range,
    nsmul_eq_mul, cast_add, cast_one, mul_one]

lemma sigmaR_one (s : ℂ) :
    σᴿ s 1 = 1 := by
  simp only [sigmaR_apply, divisors_one, sum_singleton, cast_one, Complex.one_cpow]

noncomputable def powR (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by grind⟩

theorem isMultiplicative_powR {ν : ℂ} : IsMultiplicative (powR ν) := by
  refine ⟨by simp [powR], fun {m n : ℕ} mCn => ?_⟩
  simp only [powR, ArithmeticFunction.coe_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, ↓reduceIte, mul_ite, mul_zero, ite_self]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, ↓reduceIte]
  have hmn_pos : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  simp only [hm.ne', hn.ne', hmn_pos, if_false]
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n ν

lemma sigmaR_eq_zeta_mul_powR (ν : ℂ) : sigmaR ν = (zeta : ArithmeticFunction ℂ) * powR ν := by
  ext n;
  by_cases hn : n = 0 <;> simp only [ hn, ArithmeticFunction.sigmaR, ArithmeticFunction.powR,
  ArithmeticFunction.zeta, map_zero, coe_mk, mul_apply, natCoe_apply, cast_ite, CharP.cast_eq_zero,
  cast_one, mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if x = 0 then 0 else ( y : ℂ ) ^ ν, ← Nat.sum_div_divisors ];
  exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ), if_neg ( Nat.ne_of_gt ( Nat.pos_of_mem_divisors hx ) ) ] ;

lemma isMultiplicative_sigmaR {s : ℂ} :
    IsMultiplicative (σᴿ s) := by
  rw [sigmaR_eq_zeta_mul_powR]
  exact isMultiplicative_zeta.natCast.mul  isMultiplicative_powR

lemma sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul {n : ℕ} {s : ℂ} (hn : n ≠ 0) :
    σᴿ s n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), (p : ℂ) ^ (i * s) := by
  rw [isMultiplicative_sigmaR.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigmaR_apply_prime_pow <| prime_of_mem_primeFactors h

lemma LSeries_powR_eq (ν : ℂ) {s : ℂ} (hs : 1 < (s - ν).re) :
    LSeries (powR ν) s = riemannZeta (s - ν) := by
  convert ( LSeries_congr _ _ ) using 1;
  · rw [ zeta_eq_tsum_one_div_nat_cpow hs ];
    · refine tsum_congr fun n => ?_;
      by_cases hn : n = 0
      · simp only [LSeries.term, hn, one_div, CharP.cast_eq_zero, ↓reduceIte, inv_eq_zero, Complex.cpow_eq_zero_iff,
          ne_eq, true_and]
        exact sub_ne_zero_of_ne (by rintro rfl; norm_num at hs)
      · simp only [one_div];
        rw [← Complex.cpow_neg, neg_sub, Complex.cpow_sub];
        · exact Eq.symm (LSeries.term_of_ne_zero hn (fun n ↦ ↑n ^ ν) s)
        · exact cast_ne_zero.mpr hn
  · unfold ArithmeticFunction.powR; aesop;

lemma abscissa_powR_le (ν : ℂ) : LSeries.abscissaOfAbsConv (powR ν) ≤ ν.re + 1 := by
  have h_abs_le : ∀ n : ℕ, n ≠ 0 → ‖(powR ν n : ℂ)‖ ≤ (n : ℝ) ^ ν.re := by
    intros n hn_nonzero
    simp only [ArithmeticFunction.powR, hn_nonzero, coe_mk, ↓reduceIte];
    rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn_nonzero ) ]
  apply_rules [ LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow ];
  exact ⟨ 1, fun n hn => by simpa using h_abs_le n hn ⟩

/-- `ζ(s)ζ(s - ν) = Σ σ_ν(n) n^(-s)` for `Re(s) > 1` and `Re(s - ν) > 1`. -/
theorem LSeries_sigma_eq_riemannZeta_mul (ν : ℂ) {s : ℂ} (hs : 1 < s.re) (hsν : 1 < (s - ν).re) :
    LSeries (↗(σᴿ ν)) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← LSeries_powR_eq ν hsν, sigmaR_eq_zeta_mul_powR];
  apply ArithmeticFunction.LSeries_mul
  · apply (ArithmeticFunction.abscissaOfAbsConv_zeta.trans_lt _)
    exact_mod_cast hs
  · apply lt_of_le_of_lt (abscissa_powR_le ν)
    rw[Complex.sub_re] at hsν
    exact_mod_cast (by linarith)

/--
Ramanujan formula:
`ζ(s)ζ(s-α)ζ(s-β)ζ(s-α-β)=ζ(2s-α-β) ∑ σ_α(n)σ_β(n)n^(-s)`. -/
theorem zeta_mul_zeta_mul_zeta_mul_zeta_eq (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    riemannZeta s * riemannZeta (s - α) * riemannZeta (s - β) * riemannZeta (s - α - β) =
      riemannZeta (2 * s - α - β) *
      LSeries (fun n ↦ σᴿ α n * σᴿ β n) s := by
  sorry

/-- Corollary:  `ζ(s)^4=ζ(2s) ∑ τ(n)^2 n^(-s)` -/
theorem zeta_pow_four_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 4 = riemannZeta (2 * s) * LSeries (fun n ↦ (τ n) ^ 2) s := by
  convert (zeta_mul_zeta_mul_zeta_mul_zeta_eq 0 0 s hs (by simpa using hs) (by simpa using hs)
      (by simpa using hs)) using 1
  · ring_nf
  · congr
    · ring_nf
    · simp [tau, sigma, sigmaR, pow_two]

/--
Baby Rankin-Selberg:
`ζ(s)∑τ(n^2)n^-s = ∑τ(n)^2 n^-s`. -/
lemma zeta_mul_tau_square_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s * LSeries (fun n ↦ τ (n ^ 2)) s = LSeries (fun n ↦ (τ n) ^ 2) s := by
  sorry

/--
Zeta cubed:
`ζ(s)^3 = ζ(2s) ∑ τ(n^2) n^(-s)`. -/
lemma zeta_pow_three_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 = riemannZeta (2 * s) * LSeries (fun n ↦ τ (n ^ 2)) s := by
  apply mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)
  linear_combination (zeta_pow_four_eq s hs) - riemannZeta (2 * s) * (zeta_mul_tau_square_eq s hs)

/--
Zeta cubed alt:
`ζ(s)^3 =  ∑_n (∑ d^2 m = n, τ (m^2)) n^(-s)`. -/
lemma zeta_pow_three_eq_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 =
    LSeries (fun n ↦
      ∑ dm ∈ n.divisors ×ˢ n.divisors with dm.1 ^ 2 * dm.2 = n, τ (dm.2 ^ 2)) s := by
  sorry

lemma two_pow_omega_le_sigma_zero {n : ℕ} (hn : n ≠ 0) :
    2 ^ (ω n) ≤ σ 0 n := by
  rw [show ω n = (Nat.primeFactors n).card from rfl, ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn, ← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  simpa [two_mul] using
  (Nat.Prime.dvd_iff_one_le_factorization (prime_of_mem_primeFactors hp) hn).mp
    (dvd_of_mem_primeFactors hp)

lemma LSeriesSummable.of_norm_le_norm {f g : ℕ → ℂ} {s : ℂ}
  (hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ g n) s n‖ ≤ ‖LSeries.term (fun n ↦ f n) s n‖)
  (hf : Summable (fun n ↦ ‖LSeries.term (fun n ↦ f n) s n‖)) : LSeriesSummable (fun n ↦ g n) s := by
  have h_fSummable : LSeriesSummable (fun n => f n) s := by
    rw [LSeriesSummable, ← summable_norm_iff]
    exact hf
  rw [LSeriesSummable, ← summable_norm_iff] at *
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => _) h_fSummable
  exact hgf

lemma LSeriesSummable_two_pow_omega {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ 2 ^ (ω n)) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ 2 ^ ω n) s n‖ ≤ ‖LSeries.term (fun n ↦ σ 0 n) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow, Complex.norm_ofNat,
        RCLike.norm_natCast]
      exact div_le_div_of_nonneg_right (by exact_mod_cast two_pow_omega_le_sigma_zero hn) (norm_nonneg _)
  apply LSeriesSummable.of_norm_le_norm hgf
  rw [summable_norm_iff, ← LSeriesSummable]
  convert LSeries_d_summable 2 hs using 1;
  exact funext fun n => by rw [d_two]; rfl

lemma LSeries.term_isMultiplicative_if_fun_isMultiplicative {f : ℕ → ℂ} (hf : (toArithmeticFunction f).IsMultiplicative) (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term f s (m * n) = LSeries.term f s m * LSeries.term f s n := by
  simp only [LSeries.term, _root_.mul_eq_zero, cast_mul, mul_ite, mul_zero, ite_mul, zero_mul]
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  rw[← mul_div_mul_comm, Complex.natCast_mul_natCast_cpow]
  simp only [or_self, ↓reduceIte]
  congr 1
  simpa [toArithmeticFunction, m_eq_zero, n_eq_zero] using hf.2 mCn

lemma powOfAdditive_isMultiplicative
    {R : Type u_1} [CommMonoidWithZero R] (k : R)
    {f : ArithmeticFunction ℕ} (hf : f.IsAdditive) :
    (toArithmeticFunction (fun n ↦ k ^ (f n))).IsMultiplicative := by
  simp only [IsAdditive, ne_eq] at hf
  have := hf one_ne_zero one_ne_zero (coprime_one_right 1)
  rw [mul_one, left_eq_add] at this
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, this,
    pow_zero, mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf m_eq_zero n_eq_zero mCn, pow_add]

lemma two_pow_omega_isMultiplicative :
    (toArithmeticFunction (fun n ↦ (2 : ℂ) ^ ω n)).IsMultiplicative := by
  exact powOfAdditive_isMultiplicative 2 (fun hm hn h => ArithmeticFunction.cardDistinctFactors_mul h)

lemma two_pow_omega_LSeries.term_isMultiplicative (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term (fun n ↦ 2 ^ (ω n)) s (m * n) =
  LSeries.term (fun n ↦ 2 ^ (ω n)) s m * LSeries.term (fun n ↦ 2 ^ (ω n)) s n := by
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative two_pow_omega_isMultiplicative s mCn

noncomputable def sumOnPrimePows (f : ℕ → ℂ) (p : Primes) : ℂ := ∑' e, f (p ^ e)

lemma sumOnPrimePows_apply (f : ℕ → ℂ) (p : Primes) :
  sumOnPrimePows f p = ∑' e, f (p ^ e) := by rfl

lemma two_pow_omega_tsum_prime_pow {s : ℂ} (hs : 1 < s.re)
    (p : Primes) : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  have h_rw : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = 1 + ∑' e : ℕ, LSeries.term (fun n : ℕ => 2 ^ (ω n)) s (p.val ^ (e + 1)) := by
    rw [sumOnPrimePows_apply, Summable.tsum_eq_zero_add];
    · unfold LSeries.term
      simp [Nat.Prime.ne_zero p.prop]
    · have := LSeriesSummable_two_pow_omega hs;
      convert this.comp_injective (show Function.Injective (fun e : ℕ => p.val ^ e) from fun a b h => Nat.pow_right_injective p.prop.one_lt h) using 1
  have h_term_eval : ∀ e : ℕ, LSeries.term (fun n : ℕ => 2 ^ ω n) s (p.val ^ (e + 1)) = 2 * (p.val : ℂ) ^ (-(e + 1) * s) := by
    intro e
    simp only [neg_mul, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte]
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow p.prop, pow_one]
    · simp only [Complex.cpow_neg, div_eq_mul_inv, ← Complex.natCast_cpow_natCast_mul, cast_add, cast_one]
    · linarith
  have geo_series_rw : ∑' e : ℕ, (p.val : ℂ) ^ (-(e + 1) * s) = (p.val : ℂ) ^ (-s) / (1 - (p.val : ℂ) ^ (-s)) := by
    rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one]
    · rw [← tsum_mul_left]; congr; ext n; rw [← Complex.cpow_nat_mul]; ring_nf
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]; ring_nf
    · rw [Complex.norm_cpow_of_ne_zero] <;> norm_num [p.2.ne_zero]
      exact lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt (mod_cast p.2.one_lt) (neg_lt_zero.mpr (by linarith))) (by norm_num)
  simp only [h_rw, h_term_eval, geo_series_rw, tsum_mul_left]
  rw [eq_div_iff, add_mul, one_mul, ← mul_div_assoc, div_mul_cancel₀]
  · ring_nf
  all_goals (exact Complex.one_sub_prime_cpow_ne_zero p.2 hs)

lemma Complex.one_add_prime_cpow_ne_zero {p : ℕ} (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    1 + (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have one_add_prime_cpow_h : ‖(p : ℂ) ^ (-s)‖ = 1 := by
    have := congr_arg norm (neg_eq_of_add_eq_zero_left h)
    simp only [norm_neg, one_mem, CStarRing.norm_of_mem_unitary] at this
    exact this
  linarith [Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs]

lemma two_pow_omega_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ 2 ^ (ω n)) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  convert HasProd.tprod_eq ( EulerProduct.eulerProduct_hasProd (R := ℂ) ?_ ?_ _ _ ) |> Eq.symm using 1
  · apply tprod_congr
    simp only [← two_pow_omega_tsum_prime_pow hs, sumOnPrimePows_apply, implies_true]
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro m n mCn; exact two_pow_omega_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_two_pow_omega hs).norm using 1
  · unfold LSeries.term; simp only [↓reduceIte]

lemma two_pow_omega_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s)) / (1 - ↑↑p ^ (-s))) (L (fun n ↦ (2 ^ ω n)) s) := by
  convert EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (2 ^ ω n)) s) using 1;
  · funext p; exact Eq.symm (two_pow_omega_tsum_prime_pow hs p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact two_pow_omega_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_two_pow_omega hs).norm using 1

/--
  Zeta squared:
  `ζ(s)^2 = ζ(2*s) * ∑_n (2^omega(n)) n^(-s)`,
  where omega is the number of distinct prime factors.
-/
lemma zeta_pow_two (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
    riemannZeta (2 * s) * LSeries (fun n ↦ 2 ^ (ω n)) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [sq, ← riemannZeta_eulerProduct_tprod hs, ← Multipliable.tprod_mul mulable mulable,
    mul_comm, ← riemannZeta_eulerProduct_tprod hs',
    two_pow_omega_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨LSeries (fun n ↦ 2 ^ (ω n)) s, two_pow_omega_LSeries_eulerProduct_hasProd s hs⟩
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩

lemma LSeriesSummable_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (μ n) ^ 2) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ (μ n) ^ 2) s n‖ ≤ ‖LSeries.term (fun n ↦ 1) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Complex.norm_intCast, sq_abs, one_mem, CStarRing.norm_of_mem_unitary,
        sq_le_one_iff_abs_le_one]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have zetaSummable : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  rw [LSeriesSummable, ← summable_norm_iff] at zetaSummable;
  apply LSeriesSummable.of_norm_le_norm hgf zetaSummable

lemma powOfMultiplicative_isMultiplicative {R : Type u_1} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (k : ℕ) :
    (toArithmeticFunction (fun n ↦ (f n) ^ k)).IsMultiplicative := by
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, _root_.mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, hf.1, one_pow, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf.2 mCn, mul_pow]

lemma moebius_sq_LSeries.term_isMultiplicative (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term (fun n ↦ (μ n) ^ 2) s (m * n) =
  LSeries.term (fun n ↦ (μ n) ^ 2) s m * LSeries.term (fun n ↦ (μ n) ^ 2) s n := by
  simp only [← intCoe_apply]
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative (powOfMultiplicative_isMultiplicative (ArithmeticFunction.IsMultiplicative.intCast isMultiplicative_moebius) 2) s mCn

lemma moebius_sq_tsum_prime_pow {s : ℂ} (p : Nat.Primes) :
    sumOnPrimePows (LSeries.term (fun n ↦ (μ n) ^ 2) s) p = (1 + (p : ℂ) ^ (-s)) := by
  have h_rw : 1 + ↑↑p ^ (-s) = ∑' (e : ℕ), (if e ≤ 1 then 1 else 0) / ((p : ℂ) ^ e) ^ s := by
    rw [tsum_eq_sum (s := {0, 1})]
    · simp only [mem_singleton, zero_ne_one, not_false_eq_true, sum_insert, _root_.zero_le,
        ↓reduceIte, pow_zero, Complex.one_cpow, ne_eq, one_ne_zero, div_self, sum_singleton,
        le_refl, pow_one, one_div, Complex.cpow_neg]
    · intro e he; simp at he
      simp [show ¬e ≤ 1 by omega]
  simp only [sumOnPrimePows_apply, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte, ← Int.cast_pow, moebius_sq, h_rw]
  apply tsum_congr
  intro e
  congr 1
  by_cases h : (e ≤ 1) <;> simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, h, ↓reduceIte, ite_eq_left_iff,
    zero_ne_one, imp_false, Decidable.not_not, ite_eq_right_iff, one_ne_zero, imp_false]
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    interval_cases e
    · simp only [zero_mul, zero_le, implies_true]
    · simp only [one_mul, ← Nat.squarefree_iff_factorization_le_one (Nat.Prime.ne_zero p.prop)]
      exact (Nat.squarefree_and_prime_pow_iff_prime.mpr p.prop).1
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, not_forall, not_le]
    use p
    simp only [Nat.Prime.factorization_self p.prop, mul_one]
    exact Nat.lt_of_not_le h

lemma moebius_sq_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ (μ n) ^ 2) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) := by
  convert (EulerProduct.eulerProduct_hasProd (R := ℂ) ?_ ?_ _ _).tprod_eq.symm using 1
  · apply tprod_congr
    simp only [← moebius_sq_tsum_prime_pow, sumOnPrimePows_apply, implies_true]
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro m n mCn; exact moebius_sq_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_moebius_sq hs).norm using 1
  · unfold LSeries.term; simp only [↓reduceIte]

lemma moebius_sq_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s))) (L (fun n ↦ (μ n) ^ 2) s) := by
  convert EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (μ n) ^ 2) s) using 1;
  · funext p; exact Eq.symm (moebius_sq_tsum_prime_pow p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact moebius_sq_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_moebius_sq hs).norm using 1

-- **Zulip question** Do we want `|μ n| = μ^2 (n)` to be a standalone function? It is the indicator
-- of `n` being squarefree.

/--
Zeta alt:
`ζ(s) = ζ(2*s) * ∑_n (|μ(n)|) n^(-s)`,
where omega is the number of distinct prime factors. -/
lemma zeta_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s =
    riemannZeta (2 * s) * LSeries (fun (n : ℕ) ↦ (μ n : ℂ) ^ 2) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [← riemannZeta_eulerProduct_tprod hs, ← riemannZeta_eulerProduct_tprod hs',
    moebius_sq_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩
  · exact ⟨LSeries (fun n ↦ (μ n) ^ 2) s, moebius_sq_LSeries_eulerProduct_hasProd s hs⟩

lemma pow_divisors_mul {m n k : ℕ} (hmn : Nat.Coprime m n) :
    (m * n).divisors.filter (fun x => x ^ k ∣ m * n) =
    (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)).image
      (fun p => p.1 * p.2) := by
  ext x
  simp only [mem_image, mem_product, mem_filter, mem_divisors, ne_eq, Prod.exists]
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ a * b = x := Nat.dvd_mul.mp hx.1.1
    simp only [mul_eq_zero, not_or, ← hab, mul_pow] at hx
    exact ⟨a, b, ⟨⟨⟨⟨ha, hx.1.2.1⟩, (hmn.coprime_dvd_left ha).pow_left k |>.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx.2)⟩,
      ⟨⟨hb, hx.1.2.2⟩, (hmn.symm.coprime_dvd_left hb).pow_left k |>.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx.2)⟩⟩, hab⟩⟩
  · intro ⟨a, b, hab⟩
    rw[← hab.2, mul_pow]
    exact ⟨⟨Nat.mul_dvd_mul hab.1.1.1.1 hab.1.2.1.1, Nat.mul_ne_zero_iff.mpr ⟨hab.1.1.1.2, hab.1.2.1.2⟩⟩, mul_dvd_mul hab.1.1.2 hab.1.2.2⟩

lemma divisors_mul_injective {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (m.divisors ×ˢ n.divisors) := by
  /- comes from mathlib PR #36495 -/
  sorry

lemma pow_divisors_mul_injective {m n k : ℕ} (hmn : Nat.Coprime m n) :
    Set.InjOn (fun (p : ℕ × ℕ) => p.1 * p.2) (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)) := by
  apply Set.InjOn.mono _ (divisors_mul_injective hmn)
  intro ⟨_, _⟩ hab
  simp only [Finset.coe_filter, Set.mem_prod, Set.mem_setOf_eq, Finset.mem_coe] at hab ⊢
  exact ⟨hab.1.1, hab.2.1⟩

noncomputable def sum_moebius_sq_divisors : ArithmeticFunction ℤ where
  toFun := fun n ↦ ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d
  map_zero' := by simp

lemma sum_moebius_sq_divisors_apply (n : ℕ) :
  sum_moebius_sq_divisors n = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by rfl

lemma sum_moebius_sq_divisors_IsMultiplicative : sum_moebius_sq_divisors.IsMultiplicative := by
  unfold sum_moebius_sq_divisors
  refine ⟨by simp only [sum_filter, coe_mk, divisors_one, dvd_one, pow_eq_one_iff,
    OfNat.ofNat_ne_zero, or_false, sum_ite_eq', mem_singleton, ↓reduceIte, isUnit_iff_eq_one,
    IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero], ?_⟩
  intro m n mCn
  simp only [coe_mk, pow_divisors_mul mCn, Finset.sum_product,
    Finset.sum_image (fun x hx y hy => pow_divisors_mul_injective (k := 2) mCn
      (Finset.coe_product _ _ ▸ Finset.mem_coe.mpr hx)
      (Finset.coe_product _ _ ▸ Finset.mem_coe.mpr hy))]
  trans (∑ i ∈ m.divisors.filter (fun x => x ^ 2 ∣ m), ∑ j ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ i * μ j)
  · apply Finset.sum_congr rfl
    intro _ hi
    apply Finset.sum_congr rfl
    intro _ hj
    exact isMultiplicative_moebius.map_mul_of_coprime
      (mCn.coprime_dvd_left (Nat.dvd_of_mem_divisors (Finset.filter_subset _ _ hi))
        |>.coprime_dvd_right (Nat.dvd_of_mem_divisors (Finset.filter_subset _ _ hj)))
  · rw [← Finset.sum_mul_sum]

lemma sum_moebius_sq_divisors_apply_prime_pow {p k : ℕ} (hp : Nat.Prime p) :
  sum_moebius_sq_divisors (p ^ k) = (μ (p ^ k)) ^ 2 := by
  have h_filter : ((Nat.divisors (p ^ k)).filter (fun x => x ^ 2 ∣ p ^ k)) = Finset.image (fun j => p ^ j) (Finset.range (k / 2 + 1)) := by
    ext; simp only [Nat.divisors_prime_pow hp, mem_filter, mem_map, mem_range, Order.lt_add_one_iff, Function.Embedding.coeFn_mk, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨a, Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by
        rw [← pow_mul] at h
        exact Nat.le_of_not_lt fun ha' => absurd (Nat.le_of_dvd (pow_pos hp.pos _) h)
          (not_le_of_gt (pow_lt_pow_right₀ hp.one_lt ha')), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by omega, rfl⟩, by rw [← pow_mul]; exact pow_dvd_pow _ (by omega)⟩
  simp only [moebius_sq, sum_moebius_sq_divisors_apply, h_filter]
  rw [Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective hp.two_le hab, Finset.sum_range_succ']
  split_ifs with h
  · have hk : k / 2 = 0 := by
      rw [Nat.div_eq_zero_iff, or_iff_right (two_ne_zero)]
      by_contra hk
      exact absurd h (by rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; exact not_and_of_not_right _ (by linarith))
    simp [hk]
  · simp only [pow_zero, isUnit_iff_eq_one, IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one]
    rcases k with _ | _ | _
    · simp at ⊢ h
    · simp [hp.squarefree] at ⊢ h
    · simp_all +decide [ArithmeticFunction.moebius_apply_prime_pow]

/-- I-K (1.33): `μ^2(n) = ∑ d^2|n μ(d)`. -/
lemma moebius_sq_eq (n : ℕ) : (μ n) ^ 2 = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by
  by_cases n_zero : n = 0
  · simp [n_zero]
  · rw[← sum_moebius_sq_divisors_apply, IsMultiplicative.multiplicative_factorization sum_moebius_sq_divisors sum_moebius_sq_divisors_IsMultiplicative n_zero]
    have hpf : ∀ p ∈ n.factorization.support, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    simp only [Finset.prod_pow, Finsupp.prod, Nat.support_factorization, Finset.prod_congr rfl (fun x hx =>
      sum_moebius_sq_divisors_apply_prime_pow ((Nat.support_factorization n ▸ hpf) x hx))]
    congr; exact IsMultiplicative.multiplicative_factorization μ isMultiplicative_moebius n_zero

/--
Liouville function:
`λ(n) = (-1)^Ω(n)`. -/
def liouville : ArithmeticFunction ℤ :=
  toArithmeticFunction (fun n => (-1 : ℤ) ^ Ω n)

-- **NOTE:** `def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
--  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b` exists in the `SelbergBound` file.

/--
Define Complete Multiplicativity for an arithmetic function. -/
def IsCompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

/-- A function that is completely multiplicative is also multiplicative. -/
lemma IsCompletelyMultiplicative.isMultiplicative {f : ArithmeticFunction ℝ} (hf : IsCompletelyMultiplicative f) : f.IsMultiplicative := by
  exact ⟨hf.1, fun {m n} _ => hf.2 m n⟩

/--
The Liouville function is completely multiplicative. -/
lemma isCompletelyMultiplicative_liouville : IsCompletelyMultiplicative (liouville : ArithmeticFunction ℤ) := by
  sorry

/--
The Dirichlet series of the Liouville function is `ζ(2s)/ζ(s)`. -/
lemma LSeries_liouville_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(liouville : ArithmeticFunction ℤ)) s = riemannZeta (2 * s) / riemannZeta s := by
  sorry

/-- `liouville` agrees with `moebius` on square-free numbers -/
lemma liouville_eq_moebius_on_squarefree (n : ℕ) (hn : Squarefree n) : liouville n = μ n := by
  sorry

/-- Euler totient series: `∑ φ(n) n^-s = ζ(s-1)/ζ(s)`. -/
lemma LSeries_totient_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗totient) s = riemannZeta (s - 1) / riemannZeta s := by
  sorry


end ArithmeticFunction
