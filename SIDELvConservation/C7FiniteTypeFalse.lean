import SIDELvConservation.C7OrderBounds

/-!
# The countermodel bracket: `C7_finite_type_false`

The retired **finite-type** form of the C₇-order bound —
`∃ C A, ∀ s, ‖completedRiemannZeta₀ s‖ ≤ C · exp(A · ‖s‖)` — is **false**. This module refutes it,
bracketing `exists_norm_completedRiemannZeta₀_le_exp` (`C7OrderBounds`, the true maximal-type
`exp(A·‖s‖·log(‖s‖+2))` bound) in the `T3″` style: that bound is the upper bracket, this file the
lower bracket. The retired finite-type shape (FINDINGS: the C₇-order finite-type form, caught false
at the W-8 sitting and corrected to maximal type) is **not edited away but bracketed** by a compiled
countermodel.

**Real-axis route.** Witness `s = 2k → ∞`. `Λ(2k) = Gammaℝ(2k)·ζ(2k)`, `Gammaℝ(2k) = (π^k)⁻¹·(k−1)!`
(positive real), `‖ζ(2k)‖ ≥ 1`; the `1/s`, `1/(1−s)` corrections are `‖·‖ ≤ 1` on `s ≥ 2`; so
`‖Λ₀(2k)‖ ≥ (π^k)⁻¹(k−1)! − 1`, which the factorial outgrows past every `C·exp(A·2k)`.
-/

open scoped Real
open Complex Filter Topology

namespace SIDELvConservation

/-- **Brick (iii).** For any `M, c`, eventually `M·c^k < (k−1)!`. -/
theorem eventually_mul_pow_lt_factorial_sub (M c : ℝ) :
    ∀ᶠ k : ℕ in atTop, M * c ^ k < (Nat.factorial (k - 1) : ℝ) := by
  have h := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop M c 1
  have hlt := h.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlt, eventually_gt_atTop 0] with k hk hk0
  have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
  rw [div_lt_one hfac] at hk; exact hk

/-- **Brick (i): `1 ≤ ‖ζ(m)‖` for `m ≥ 2`.** Via the Dirichlet series' `n = 1` term and `re ≤ ‖·‖`. -/
theorem one_le_norm_riemannZeta {m : ℕ} (hm : 2 ≤ m) : 1 ≤ ‖riemannZeta m‖ := by
  have hm1 : 1 < m := hm
  have hcpow : ∀ n : ℕ, (1 : ℂ) / (n : ℂ) ^ m = 1 / (n : ℂ) ^ (m : ℂ) := fun n => by
    rw [Complex.cpow_natCast]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ m) := by
    rw [summable_congr hcpow]
    exact Complex.summable_one_div_nat_cpow.mpr (by rw [Complex.natCast_re]; exact_mod_cast hm1)
  have hterm : ∀ n : ℕ, (1 / (n : ℂ) ^ m).re = 1 / (n : ℝ) ^ m := fun n => by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_pow,
      ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hnn : ∀ n : ℕ, 0 ≤ (1 / (n : ℂ) ^ m).re := fun n => by rw [hterm]; positivity
  have hsummre : Summable (fun n : ℕ => (1 / (n : ℂ) ^ m).re) := by
    rw [summable_congr hterm]; exact Real.summable_one_div_nat_pow.mpr hm1
  have hre1 : (1 : ℝ) ≤ (riemannZeta m).re := by
    rw [zeta_nat_eq_tsum_of_gt_one hm1, Complex.re_tsum hsum]
    calc (1 : ℝ) = (1 / (1 : ℂ) ^ m).re := by simp
      _ ≤ ∑' n : ℕ, (1 / (n : ℂ) ^ m).re := by
          simpa using hsummre.le_tsum 1 (fun n _ => hnn n)
  exact hre1.trans (Complex.re_le_norm _)

/-- **`Gammaℝ(2k) = (π^k)⁻¹·(k−1)!`** as a real, for `k ≥ 1`. Kept entirely in ℝ. -/
theorem Gammaℝ_two_mul_nat {k : ℕ} (hk : 1 ≤ k) :
    Gammaℝ ((2 * k : ℕ) : ℂ) = (((Real.pi ^ k)⁻¹ * Nat.factorial (k - 1) : ℝ) : ℂ) := by
  have hhalf : ((2 * k : ℕ) : ℂ) / 2 = ((k - 1 : ℕ) : ℂ) + 1 := by
    rw [Nat.cast_sub hk]; push_cast; ring
  have hexp : (↑Real.pi : ℂ) ^ (-((2 * k : ℕ) : ℂ) / 2) = (((Real.pi ^ k)⁻¹ : ℝ) : ℂ) := by
    rw [show -((2 * k : ℕ) : ℂ) / 2 = -((k : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  rw [Gammaℝ_def, hhalf, Complex.Gamma_nat_eq_factorial, hexp, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul]

/-- **The countermodel: the finite-type C₇ form is false.** No `(C, A)` bounds `‖Λ₀ s‖` by
`C · exp(A · ‖s‖)`. Lower bracket to `exists_norm_completedRiemannZeta₀_le_exp` (the true
maximal-type bound); the retired finite-type shape is bracketed, not edited away. -/
theorem C7_finite_type_false :
    ¬ ∃ C A : ℝ, ∀ s : ℂ, ‖completedRiemannZeta₀ s‖ ≤ C * Real.exp (A * ‖s‖) := by
  rintro ⟨C, A, hCA⟩
  set C' := max C 1 with hC'def
  set A' := max A 0 with hA'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hCA' : ∀ s : ℂ, ‖completedRiemannZeta₀ s‖ ≤ C' * Real.exp (A' * ‖s‖) := fun s =>
    (hCA s).trans <| mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg s)))
      (Real.exp_pos _).le (le_trans zero_le_one hC'1)
  set b := Real.pi * Real.exp (2 * A') with hbdef
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπb : Real.pi ≤ b := by
    rw [hbdef]; nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * A'), hπpos.le]
  obtain ⟨k, hkbig, hk1⟩ :=
    ((eventually_mul_pow_lt_factorial_sub (C' + 1) b).and (eventually_ge_atTop 1)).exists
  have hk1' : (1 : ℕ) ≤ k := hk1
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1'
  have hsne : ((2 * k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsnorm : ‖((2 * k : ℕ) : ℂ)‖ = 2 * (k : ℝ) := by rw [Complex.norm_natCast]; push_cast; ring
  -- drop to ℝ: the real lower bound on ‖Λ‖
  have hfacpos : (0 : ℝ) < (Real.pi ^ k)⁻¹ * Nat.factorial (k - 1) := by positivity
  have hΛeq : completedRiemannZeta ((2 * k : ℕ) : ℂ)
      = Gammaℝ ((2 * k : ℕ) : ℂ) * riemannZeta ((2 * k : ℕ) : ℂ) := by
    rw [riemannZeta_def_of_ne_zero hsne, mul_div_cancel₀ _
      (Gammaℝ_ne_zero_of_re_pos (by rw [Complex.natCast_re]; positivity))]
  have hΛlow : (Real.pi ^ k)⁻¹ * Nat.factorial (k - 1) ≤ ‖completedRiemannZeta ((2 * k : ℕ) : ℂ)‖ := by
    rw [hΛeq, norm_mul, Gammaℝ_two_mul_nat hk1', Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hfacpos]
    exact le_mul_of_one_le_right hfacpos.le (one_le_norm_riemannZeta (by omega))
  -- correction ‖1/s + 1/(1-s)‖ ≤ 1
  have hs1ne : (1 : ℂ) - ((2 * k : ℕ) : ℂ) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : ‖((2 * k : ℕ) : ℂ)‖ = 1 := by rw [← h, norm_one]
    rw [hsnorm] at this; nlinarith [hkr]
  have hcorr : ‖(1 / ((2 * k : ℕ) : ℂ) + 1 / (1 - ((2 * k : ℕ) : ℂ)) : ℂ)‖ ≤ 1 := by
    have heq : (1 / ((2 * k : ℕ) : ℂ) + 1 / (1 - ((2 * k : ℕ) : ℂ)) : ℂ)
        = 1 / (((2 * k : ℕ) : ℂ) * (1 - ((2 * k : ℕ) : ℂ))) := by field_simp; ring
    have h1s : (1 : ℝ) ≤ ‖1 - ((2 * k : ℕ) : ℂ)‖ := by
      have := norm_sub_norm_le ((2 * k : ℕ) : ℂ) 1
      rw [norm_one, hsnorm] at this
      calc (1 : ℝ) ≤ 2 * (k : ℝ) - 1 := by nlinarith [hkr]
        _ ≤ ‖((2 * k : ℕ) : ℂ) - 1‖ := this
        _ = ‖1 - ((2 * k : ℕ) : ℂ)‖ := by rw [← norm_neg, neg_sub]
    have hprod : (1 : ℝ) ≤ ‖((2 * k : ℕ) : ℂ) * (1 - ((2 * k : ℕ) : ℂ))‖ := by
      rw [norm_mul, hsnorm]; nlinarith [h1s, hkr, norm_nonneg (1 - ((2 * k : ℕ) : ℂ))]
    rw [heq, norm_div, norm_one, div_le_one (lt_of_lt_of_le one_pos hprod)]; exact hprod
  -- ‖Λ₀‖ ≥ ‖Λ‖ - 1
  have hΛ0eq : completedRiemannZeta₀ ((2 * k : ℕ) : ℂ)
      = completedRiemannZeta ((2 * k : ℕ) : ℂ)
        + (1 / ((2 * k : ℕ) : ℂ) + 1 / (1 - ((2 * k : ℕ) : ℂ))) := by
    have := completedRiemannZeta_eq ((2 * k : ℕ) : ℂ); linear_combination -this
  have hlow0 : ‖completedRiemannZeta ((2 * k : ℕ) : ℂ)‖ - 1
      ≤ ‖completedRiemannZeta₀ ((2 * k : ℕ) : ℂ)‖ := by
    rw [hΛ0eq]
    have := norm_sub_le
      (completedRiemannZeta ((2 * k : ℕ) : ℂ) + (1 / ((2 * k : ℕ) : ℂ) + 1 / (1 - ((2 * k : ℕ) : ℂ))))
      (1 / ((2 * k : ℕ) : ℂ) + 1 / (1 - ((2 * k : ℕ) : ℂ)))
    simp only [add_sub_cancel_right] at this
    linarith [hcorr, this]
  -- upper bound at the witness
  have hupper : ‖completedRiemannZeta₀ ((2 * k : ℕ) : ℂ)‖ ≤ C' * Real.exp (A' * (2 * (k : ℝ))) := by
    have := hCA' ((2 * k : ℕ) : ℂ); rwa [hsnorm] at this
  -- chain in ℝ
  have hchain : (Real.pi ^ k)⁻¹ * Nat.factorial (k - 1) - 1 ≤ C' * Real.exp (A' * (2 * (k : ℝ))) := by
    linarith [hΛlow, hlow0, hupper]
  -- fold by π^k, all real
  have hπk : (0 : ℝ) < Real.pi ^ k := by positivity
  have hexpb : Real.exp (A' * (2 * (k : ℝ))) * Real.pi ^ k = b ^ k := by
    rw [show A' * (2 * (k : ℝ)) = (k : ℝ) * (2 * A') by ring, Real.exp_nat_mul, ← mul_pow, hbdef,
      mul_comm Real.pi]
  have hπbk : Real.pi ^ k ≤ b ^ k := by gcongr
  have hmul : (Nat.factorial (k - 1) : ℝ) - Real.pi ^ k ≤ C' * b ^ k := by
    have h := mul_le_mul_of_nonneg_right hchain hπk.le
    have hLHS : ((Real.pi ^ k)⁻¹ * (Nat.factorial (k - 1) : ℝ) - 1) * Real.pi ^ k
        = (Nat.factorial (k - 1) : ℝ) - Real.pi ^ k := by
      rw [sub_mul, one_mul, mul_right_comm, inv_mul_cancel₀ hπk.ne', one_mul]
    have hRHS : C' * Real.exp (A' * (2 * (k : ℝ))) * Real.pi ^ k = C' * b ^ k := by
      rw [mul_assoc, hexpb]
    rw [hLHS, hRHS] at h; exact h
  have hfinal : (Nat.factorial (k - 1) : ℝ) ≤ (C' + 1) * b ^ k := by
    have hexpand : (C' + 1) * b ^ k = C' * b ^ k + b ^ k := by ring
    rw [hexpand]; linarith [hmul, hπbk]
  exact absurd hfinal (not_le.mpr hkbig)

end SIDELvConservation
