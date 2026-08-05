import Mathlib

/-!
# FieldLayer — the shared quadratic layer for the D-2 kernel leg

The layer D-2a's un-derived link and D-2b's certificates both needed: a field carrying a chosen
square root of `q`, so that the Duursma certificate's **normalized** coefficients `p i / (√q)^i`
are expressible rather than merely described. Over ℚ they are not: at `q = 2` the odd-index
normalizers are irrational, which is exactly why D-2a's first pass had to take its
top-coefficient identification as a hypothesis.

## What the layer is

A field `K`, an element `s : K` with `s ^ 2 = q`, and `s ≠ 0`. Nothing more — no Galois
apparatus, no ordering, no root-counting. The scoping pass priced the full ℚ(√q) build
(ordered structure by hand; Sturm chains absent from Mathlib entirely); **this module deliberately
takes only the part D-2a's link needs**, and takes it as a hypothesis on an arbitrary field
rather than by constructing the extension. What that buys is stated exactly in
`top_coeff_of_expansion` and `norml_top` below.

## The expansion relation

Duursma's certificate `h` is the polynomial for which `x^g * h(x + 1/x)` reproduces the
normalized zeta polynomial. Written without inverses — multiply through by `x^g` — that reads

  `∑_{j ≤ g} c j * (X^(g+j) + X^(g-j))  =  ∑_{i ≤ 2g} pt i * X^i`

since `x^g * (x^j + x^(-j)) = x^(g+j) + x^(g-j)` for `j ≤ g`. This is `IsExpansion`. It is the
**defining relation between the certificate's coefficients and the zeta polynomial's**, not an
extra premise about them: it says `c` is the coefficient sequence of *that* certificate. The
`X^0` term is `2 * c 0`, matching the basis convention `v 0 = 2`.

`top_coeff_of_expansion` extracts the top coefficient from it. That extraction is what converts
D-2a's second stipulation: `c g = pt (2g)` is now a theorem about the expansion, not an
assumption about `c`.

## What this does NOT say

No claim that the expansion EXISTS for a given normalized sequence (that direction is not needed
here and is not proved); no ordering, no root location, no Galois conjugation, no ζ, no RH.

0 sorry, 0 native_decide.
-/

namespace SIDELvConservation
namespace FieldLayer

open Polynomial

variable {K : Type*} [Field K]

/-- The self-dual functional equation for a Duursma zeta polynomial's coefficients, over a
field with `q` of size-role and genus `g`: `p (2g - i) = q ^ (g - i) * p i` for `i ≤ g`.

The cited datum (Duursma), taken here as a hypothesis; nothing below re-proves it. -/
structure SelfDualFE (q : K) (g : ℕ) (p : ℕ → K) : Prop where
  fe : ∀ i ≤ g, p (2 * g - i) = q ^ (g - i) * p i

/-- The normalized coefficient sequence `pt i = p i / s ^ i`, expressible exactly because the
layer carries `s`. -/
noncomputable def norml (s : K) (p : ℕ → K) (i : ℕ) : K := p i / s ^ i

/-- **The expansion relation.** `c` are the certificate's coefficients for the normalized
sequence `pt` when `x^g * h(x + 1/x)` reproduces `∑ pt i x^i` — written without inverses. -/
def IsExpansion (g : ℕ) (c : ℕ → K) (pt : ℕ → K) : Prop :=
  ∑ j ∈ Finset.range (g + 1), C (c j) * (X ^ (g + j) + X ^ (g - j))
    = ∑ i ∈ Finset.range (2 * g + 1), C (pt i) * X ^ i

/-- **THE CONVERSION.** The certificate's top coefficient is the top normalized coefficient —
derived from the expansion by reading off the degree-`2g` coefficient of both sides.

On the left only `j = g` contributes: `X^(g+j)` hits `2g` exactly at `j = g`, and `X^(g-j)`
cannot reach `2g` at all once `g ≥ 1`, since `g - j ≤ g < 2g`. On the right only `i = 2g`
contributes. -/
theorem top_coeff_of_expansion (g : ℕ) (hg : 1 ≤ g) (c pt : ℕ → K)
    (h : IsExpansion g c pt) : c g = pt (2 * g) := by
  have hco := congrArg (fun f : K[X] => f.coeff (2 * g)) h
  simp only [finset_sum_coeff, coeff_C_mul, coeff_add, coeff_X_pow] at hco
  have hL : (∑ j ∈ Finset.range (g + 1),
      c j * ((if 2 * g = g + j then 1 else 0) + (if 2 * g = g - j then 1 else 0))) = c g := by
    rw [Finset.sum_eq_single g]
    · have h1 : (2 * g = g + g) := by omega
      have h2 : ¬ (2 * g = g - g) := by omega
      rw [if_pos h1, if_neg h2]
      ring
    · intro j hj hjg
      simp only [Finset.mem_range] at hj
      have h1 : ¬ (2 * g = g + j) := by omega
      have h2 : ¬ (2 * g = g - j) := by omega
      simp [h1, h2]
    · intro hg1
      simp only [Finset.mem_range] at hg1
      omega
  have hR : (∑ i ∈ Finset.range (2 * g + 1),
      pt i * (if 2 * g = i then 1 else 0)) = pt (2 * g) := by
    rw [Finset.sum_eq_single (2 * g)]
    · simp
    · intro i _ hi
      have : ¬ (2 * g = i) := fun hc => hi hc.symm
      simp [this]
    · intro hmem
      simp only [Finset.mem_range] at hmem
      omega
  rw [hL, hR] at hco
  exact hco

/-- The top normalized coefficient is the constant term, forced by the functional equation.
This is the step that needs `s`: `q ^ g = (s ^ 2) ^ g = s ^ (2 * g)`, so the normalizer at the
top index cancels the functional equation's factor exactly. -/
theorem norml_top (s q : K) (hs : s ^ 2 = q) (hs0 : s ≠ 0) (g : ℕ) (p : ℕ → K)
    (H : SelfDualFE q g p) : norml s p (2 * g) = p 0 := by
  have h0 := H.fe 0 (Nat.zero_le g)
  simp only [Nat.sub_zero] at h0
  have hq : q ^ g = s ^ (2 * g) := by rw [← hs, ← pow_mul, Nat.mul_comm]
  rw [norml, h0, hq]
  field_simp

end FieldLayer
end SIDELvConservation
