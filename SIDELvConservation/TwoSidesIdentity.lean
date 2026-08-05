import Mathlib

/-!
# TwoSidesIdentity — D-2c: the two-sides balance at a small exact instance

The era's E-16 / W-TWOSIDES instrument rests on one classical identity: a Hankel determinant of
moments is ONE number reachable by two genuinely different routes — a coefficient route through
the Jacobi recurrence, and a spectral route through the nodes and weights. The instrument used
the logarithmic form; the exact form, which is what compiles, is multiplicative.

This module certifies the identity at **K = 3 for a three-atom rational measure**, symbolically
in six free variables — so it is a theorem about every such measure, not an arithmetic check at
one point — plus the coefficient-side ladder and a three-route numerical agreement.

## What is stipulated, and what is derived

**STIPULATED as instance scope.** `K = 3`, and the measure has exactly three atoms. This is an
instance. Nothing here claims the identity at general `K`, and nothing here treats a measure
with infinitely many atoms or an absolutely continuous part.

**STIPULATED at cite (the one named premise).** That the Hankel-ratio coefficients
`b j = D (j+1) * D (j-1) / D j ^ 2` are the monic-orthogonal-polynomial recurrence coefficients
of the measure — the Jacobi/Heine link, classical. **That link is not compiled here**, so the
coefficient side below is certified in its Hankel-ratio form only.

**DERIVED IN-KERNEL.** The depth-1, depth-2 and depth-3 Heine/Vandermonde identities as
polynomial identities in the six free variables; the coefficient-side ladder from the
Hankel-ratio definition; and the exact agreement of all three routes at one explicit measure.

## What this does NOT say

Nothing of ζ, RH, `h2`, GUE, or pair correlation. The log-repulsion reading of the spectral side
— the reason the instrument was built — is a reading of this identity, not a consequence of it,
and no part of that reading is compiled here.

0 sorry, 0 native_decide.
-/

namespace SIDELvConservation
namespace TwoSides

variable (w1 w2 w3 x1 x2 x3 : ℚ)

/-- The moments of the three-atom measure `w1 δ(x1) + w2 δ(x2) + w3 δ(x3)`. -/
def m (k : ℕ) : ℚ := w1 * x1 ^ k + w2 * x2 ^ k + w3 * x3 ^ k

/-- Depth-1 Hankel determinant: the total mass. -/
def D1 : ℚ := m w1 w2 w3 x1 x2 x3 0

/-- Depth-2 Hankel determinant. -/
def D2 : ℚ :=
  m w1 w2 w3 x1 x2 x3 0 * m w1 w2 w3 x1 x2 x3 2 - m w1 w2 w3 x1 x2 x3 1 ^ 2

/-- Depth-3 Hankel determinant, expanded along the first row. -/
def D3 : ℚ :=
  m w1 w2 w3 x1 x2 x3 0 *
      (m w1 w2 w3 x1 x2 x3 2 * m w1 w2 w3 x1 x2 x3 4 - m w1 w2 w3 x1 x2 x3 3 ^ 2)
    - m w1 w2 w3 x1 x2 x3 1 *
      (m w1 w2 w3 x1 x2 x3 1 * m w1 w2 w3 x1 x2 x3 4
        - m w1 w2 w3 x1 x2 x3 2 * m w1 w2 w3 x1 x2 x3 3)
    + m w1 w2 w3 x1 x2 x3 2 *
      (m w1 w2 w3 x1 x2 x3 1 * m w1 w2 w3 x1 x2 x3 3 - m w1 w2 w3 x1 x2 x3 2 ^ 2)

/-- **Depth 1.** The spectral side at `K = 1`: the empty Vandermonde is `1`. -/
theorem heine_one : D1 w1 w2 w3 x1 x2 x3 = w1 + w2 + w3 := by
  unfold D1 m; ring

/-- **Depth 2.** The spectral side at `K = 2`: pairs of atoms, each weighted by the squared
separation of its two nodes. -/
theorem heine_two : D2 w1 w2 w3 x1 x2 x3
    = w1 * w2 * (x1 - x2) ^ 2 + w1 * w3 * (x1 - x3) ^ 2 + w2 * w3 * (x2 - x3) ^ 2 := by
  unfold D2 m; ring

/-- **DEPTH 3 — THE HEINE/VANDERMONDE IDENTITY AT THE INSTANCE.** The coefficient-side object
(a determinant of moments) equals the spectral-side object (the weights' product times the
squared Vandermonde of the nodes), as a polynomial identity in all six variables. -/
theorem heine_three : D3 w1 w2 w3 x1 x2 x3
    = w1 * w2 * w3 * ((x1 - x2) * (x1 - x3) * (x2 - x3)) ^ 2 := by
  unfold D3 m; ring

/-- **The coefficient-side ladder.** With the Hankel-ratio coefficients `b0 = D1`,
`b1 = D2/D1^2`, `b2 = D3*D1/D2^2`, the depth-3 determinant is `b0^3 * b1^2 * b2` — the exact
(multiplicative) form of `log D_K = Σ (K-j) log β_j` at `K = 3`.

Certified in the Hankel-ratio form; the identification of `b_j` with the monic-OP recurrence
coefficient is the module's one cited premise and is not compiled. -/
theorem ladder_three (h1 : D1 w1 w2 w3 x1 x2 x3 ≠ 0) (h2 : D2 w1 w2 w3 x1 x2 x3 ≠ 0) :
    (D1 w1 w2 w3 x1 x2 x3) ^ 3
      * (D2 w1 w2 w3 x1 x2 x3 / D1 w1 w2 w3 x1 x2 x3 ^ 2) ^ 2
      * (D3 w1 w2 w3 x1 x2 x3 * D1 w1 w2 w3 x1 x2 x3 / D2 w1 w2 w3 x1 x2 x3 ^ 2)
    = D3 w1 w2 w3 x1 x2 x3 := by
  field_simp

/-! ### The explicit instance: three routes, one number

Nodes `0, 1, 2` with weights `1, 2, 3`. The determinant route, the Vandermonde route, and the
ladder route are computed independently and agree at `24`. -/

/-- Route 1 — the determinant of moments. -/
theorem instance_determinant : D3 1 2 3 0 1 2 = 24 := by
  unfold D3 m; norm_num

/-- Route 2 — weights times squared Vandermonde. -/
theorem instance_spectral : (1 : ℚ) * 2 * 3 * (((0:ℚ) - 1) * ((0:ℚ) - 2) * ((1:ℚ) - 2)) ^ 2 = 24 := by
  norm_num

/-- Route 3 — the Hankel-ratio ladder. -/
theorem instance_ladder :
    (D1 1 2 3 0 1 2) ^ 3 * (D2 1 2 3 0 1 2 / D1 1 2 3 0 1 2 ^ 2) ^ 2
      * (D3 1 2 3 0 1 2 * D1 1 2 3 0 1 2 / D2 1 2 3 0 1 2 ^ 2) = 24 := by
  unfold D1 D2 D3 m; norm_num

/-- **THE TWO-SIDES BALANCE AT THE INSTANCE.** All three routes give one number, and it is not
zero — so the agreement is not the trivial agreement of two vanishing sides. -/
theorem two_sides_balance :
    D3 1 2 3 0 1 2 = (1 : ℚ) * 2 * 3 * (((0:ℚ) - 1) * ((0:ℚ) - 2) * ((1:ℚ) - 2)) ^ 2
      ∧ D3 1 2 3 0 1 2 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [instance_determinant, instance_spectral]
  · rw [instance_determinant]; norm_num

/-! ### Salt-check

The identity must be shown capable of taking both values before either is read. -/

/-- **The identity detects degeneracy.** When two atoms collide the Hankel matrix drops rank and
the determinant vanishes — so `D3 ≠ 0` at the instance above is a fact about that measure, not an
automatic feature of the expression. -/
theorem heine_three_degenerate : D3 w1 w2 w3 x1 x1 x3 = 0 := by
  unfold D3 m; ring

/-- **The two sides are capable of disagreeing if the exponent is wrong.** The Vandermonde enters
SQUARED; with the square dropped the identity fails at the instance, so the squaring is
load-bearing and not a harmless normalization. -/
theorem vandermonde_square_is_load_bearing :
    D3 1 2 3 0 1 2 ≠ (1 : ℚ) * 2 * 3 * (((0:ℚ) - 1) * ((0:ℚ) - 2) * ((1:ℚ) - 2)) := by
  rw [instance_determinant]; norm_num

end TwoSides
end SIDELvConservation
