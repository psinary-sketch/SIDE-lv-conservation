import SIDELvConservation.LeadLaw

/-!
# SaltCheck_LeadLaw — D-2a's salt-check, compiled

A theorem with unsatisfiable hypotheses is vacuously true and says nothing. D-2a's upgrade
replaced an assumed coefficient identity with the expansion relation, so the salt-check must
show the expansion relation is *satisfiable* — otherwise the upgrade would have bought a
stronger-looking theorem about nothing.

Two checks, both compiled rather than argued:

* **`expansion_exists_of_palindromic`** — at `g = 1`, EVERY palindromic normalized sequence
  admits an expansion, with the coefficients exhibited. Non-vacuity is generic, not a single
  point. (Palindromy is what the functional equation supplies, so this is the shape the
  theorem's own hypotheses produce.)
* **`hg_is_load_bearing`** — the `1 ≤ g` hypothesis of `top_coeff_of_expansion` is USED: at
  `g = 0` an expansion exists whose top coefficient is *not* the top normalized coefficient.
  This is the OVER-HYPOTHESIZED check run forward — a hypothesis is load-bearing only when its
  deletion is shown to break something.

0 sorry, 0 native_decide.
-/

namespace SIDELvConservation
namespace SaltCheckLeadLaw

open Polynomial FieldLayer

/-- `C 2 = 2` in `ℚ[X]`, proved through `C_add` so no numeral cast is needed. -/
private theorem C_two : (C (2 : ℚ) : ℚ[X]) = 2 := by
  rw [show (2 : ℚ) = 1 + 1 from by norm_num, C_add, C_1]
  ring

/-- `C a * 2 = C (2 * a)` in `ℚ[X]` — the one coefficient-arithmetic step the witnesses need. -/
private theorem C_mul_two (a : ℚ) : (C a : ℚ[X]) * 2 = C (2 * a) := by
  rw [mul_two, ← C_add]
  congr 1
  ring

/-- **Non-vacuity, generically.** At `g = 1`, every palindromic normalized sequence admits an
expansion — so `IsExpansion` is not an empty hypothesis, and `lead_law`'s premise set is
satisfiable by the very sequences its functional equation produces. -/
theorem expansion_exists_of_palindromic (pt : ℕ → ℚ) (hpal : pt 0 = pt 2) :
    IsExpansion 1 (fun j => if j = 0 then pt 1 / 2 else pt 0) pt := by
  unfold IsExpansion
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  rw [← two_mul, ← mul_assoc, C_mul_two,
      show (2 : ℚ) * (pt 1 / 2) = pt 1 from by ring, ← hpal]
  ring

/-- The witness the `g = 0` check uses: constant coefficient `1`, normalized sequence `2`. -/
theorem expansion_at_zero : IsExpansion 0 (fun _ => (1 : ℚ)) (fun _ => (2 : ℚ)) := by
  unfold IsExpansion
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  rw [C_two]

/-- **`1 ≤ g` is load-bearing.** At `g = 0` the conclusion of `top_coeff_of_expansion` is false
for an expansion that exists: the `X^0` term is `2 * c 0`, so the top coefficient is half the
top normalized coefficient, not equal to it. Deleting the hypothesis would break the theorem. -/
theorem hg_is_load_bearing :
    ∃ (c pt : ℕ → ℚ), IsExpansion 0 c pt ∧ c 0 ≠ pt (2 * 0) := by
  refine ⟨fun _ => (1 : ℚ), fun _ => (2 : ℚ), expansion_at_zero, ?_⟩
  norm_num

end SaltCheckLeadLaw
end SIDELvConservation
