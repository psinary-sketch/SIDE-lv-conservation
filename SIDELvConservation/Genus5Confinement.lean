import Mathlib

/-!
# Genus5Confinement — D-2b, unit 2: the three confinement certificates

The genus ≤ 5 theorem's second half. Unit 1 closed the catalogue (lengths 8, 16, 24); this
unit certifies each catalogued object's certificate: **`H(u)` has all its roots in `[0, 4]`**,
which is the confinement condition transported through the Galois-locked certificate.

Certificates are written in cleared integer form; clearing a positive rational denominator
changes no root, so the root statements below are the certificates' root statements.

## The three routes (each verified against the object before it was chosen)

- **e₈** — `X - 2`: one linear factor, root 2. Trivial.
- **W₈²** — `(X - 2) * (X^2 - 4*X + 1)^2`: an explicit rational factorization. The quadratic's
  roots satisfy `r * (4 - r) = 1 > 0`, which forces `0 < r < 4` without ever naming `√3`.
- **Golay** — `676X^5 - 5408X^4 + 13832X^3 - 12532X^2 + 3481X - 162`: **no rational roots**
  (checked before choosing the route), so factorization case-analysis is unavailable. Instead:
  five sign alternations at six explicit rationals give five distinct roots by the
  intermediate value theorem, and `natDegree = 5` caps the count, so those are all of them.

## Stipulated at cite

The certificate construction itself (that these polynomials ARE the Galois-locked certificates
of the three enumerators) — the same stipulation `LeadLaw` and unit 1 carry. Nothing here
re-derives it; this unit is about these polynomials' roots.

## What this does NOT say

Nothing of ζ, RH, or `h2`; nothing about any genus beyond 5; and no classification claim —
that is unit 1. Per the joint-row rule, neither unit is citable alone as the registered
statement.

0 sorry, 0 native_decide.
-/

namespace SIDELvConservation
namespace Genus5Confinement

open Polynomial

/-- The e₈ certificate, cleared: `X - 2`. -/
noncomputable def He8 : ℝ[X] := X - C 2

/-- The W₈² certificate, cleared: `(X - 2) * (X² - 4X + 1)²`. -/
noncomputable def Hw16 : ℝ[X] := (X - C 2) * (X ^ 2 - C 4 * X + C 1) ^ 2

/-- The Golay certificate, cleared to integer coefficients. -/
noncomputable def Hgolay : ℝ[X] :=
  C 676 * X ^ 5 - C 5408 * X ^ 4 + C 13832 * X ^ 3 - C 12532 * X ^ 2 + C 3481 * X - C 162

/-- **e₈ confinement.** -/
theorem e8_confined (r : ℝ) (h : He8.IsRoot r) : 0 ≤ r ∧ r ≤ 4 := by
  simp only [He8, IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] at h
  constructor <;> linarith [h]

/-- The quadratic factor's roots are confined, by `r * (4 - r) = 1 > 0`. -/
theorem quad_confined (r : ℝ) (h : r ^ 2 - 4 * r + 1 = 0) : 0 < r ∧ r < 4 := by
  have key : r * (4 - r) = 1 := by nlinarith [h]
  constructor
  · nlinarith [key]
  · nlinarith [key]

/-- **W₈² confinement.** -/
theorem w16_confined (r : ℝ) (h : Hw16.IsRoot r) : 0 ≤ r ∧ r ≤ 4 := by
  simp only [Hw16, IsRoot, eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_C] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · constructor <;> linarith
  · have hq : r ^ 2 - 4 * r + 1 = 0 :=
      (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h2
    obtain ⟨ha, hb⟩ := quad_confined r hq
    exact ⟨le_of_lt ha, le_of_lt hb⟩

/-- IVT, rising form: a sign change from negative to positive gives a root strictly between. -/
theorem root_of_sign_change (a b : ℝ) (hab : a ≤ b)
    (ha : Hgolay.eval a < 0) (hb : 0 < Hgolay.eval b) :
    ∃ r, a < r ∧ r < b ∧ Hgolay.IsRoot r := by
  have hsub := intermediate_value_Ioo hab (Hgolay.continuous.continuousOn)
  have h0 : (0 : ℝ) ∈ Set.Ioo (Hgolay.eval a) (Hgolay.eval b) := ⟨ha, hb⟩
  obtain ⟨r, hr, hval⟩ := hsub h0
  exact ⟨r, hr.1, hr.2, hval⟩

/-- IVT, falling form. -/
theorem root_of_sign_change' (a b : ℝ) (hab : a ≤ b)
    (ha : 0 < Hgolay.eval a) (hb : Hgolay.eval b < 0) :
    ∃ r, a < r ∧ r < b ∧ Hgolay.IsRoot r := by
  have hsub := intermediate_value_Ioo' hab (Hgolay.continuous.continuousOn)
  have h0 : (0 : ℝ) ∈ Set.Ioo (Hgolay.eval b) (Hgolay.eval a) := ⟨hb, ha⟩
  obtain ⟨r, hr, hval⟩ := hsub h0
  exact ⟨r, hr.1, hr.2, hval⟩

theorem hgolay_natDegree : Hgolay.natDegree = 5 := by
  unfold Hgolay
  compute_degree!

theorem hgolay_ne_zero : Hgolay ≠ 0 := by
  intro h
  have hd := hgolay_natDegree
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- **Golay confinement, the part certified here.** Five roots, pairwise separated by the six
explicit rationals of the sign table, every one of them strictly inside `(0, 4)`.

Together with `hgolay_natDegree` (degree 5) this forces the certificate to split over ℝ with
all roots in `(0,4)` — but **that last closure step is NOT compiled here** (see the module's
gap note); what is certified is the existence and location of the five. -/
theorem golay_five_roots_in_interval :
    ∃ r₁ r₂ r₃ r₄ r₅ : ℝ,
      (0 < r₁ ∧ r₁ < 1/10) ∧ (1/10 < r₂ ∧ r₂ < 1/2) ∧ (1/2 < r₃ ∧ r₃ < 3/2) ∧
      (3/2 < r₄ ∧ r₄ < 3) ∧ (3 < r₅ ∧ r₅ < 4) ∧
      Hgolay.IsRoot r₁ ∧ Hgolay.IsRoot r₂ ∧ Hgolay.IsRoot r₃ ∧
      Hgolay.IsRoot r₄ ∧ Hgolay.IsRoot r₅ := by
  obtain ⟨r1, h1a, h1b, h1r⟩ := root_of_sign_change 0 (1/10) (by norm_num)
    (by norm_num [Hgolay]) (by norm_num [Hgolay])
  obtain ⟨r2, h2a, h2b, h2r⟩ := root_of_sign_change' (1/10) (1/2) (by norm_num)
    (by norm_num [Hgolay]) (by norm_num [Hgolay])
  obtain ⟨r3, h3a, h3b, h3r⟩ := root_of_sign_change (1/2) (3/2) (by norm_num)
    (by norm_num [Hgolay]) (by norm_num [Hgolay])
  obtain ⟨r4, h4a, h4b, h4r⟩ := root_of_sign_change' (3/2) 3 (by norm_num)
    (by norm_num [Hgolay]) (by norm_num [Hgolay])
  obtain ⟨r5, h5a, h5b, h5r⟩ := root_of_sign_change 3 4 (by norm_num)
    (by norm_num [Hgolay]) (by norm_num [Hgolay])
  exact ⟨r1, r2, r3, r4, r5, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩, ⟨h4a, h4b⟩, ⟨h5a, h5b⟩,
    h1r, h2r, h3r, h4r, h5r⟩

/-- **GOLAY CONFINEMENT, closed.** The certificate's root multiset has cardinality 5 = its
degree — so it splits over ℝ and has no non-real roots — and every root lies in `(0, 4)`. -/
theorem golay_confined :
    Hgolay.roots.card = 5 ∧ ∀ r ∈ Hgolay.roots, 0 < r ∧ r < 4 := by
  obtain ⟨r1, r2, r3, r4, r5, ⟨q1, q1'⟩, ⟨q2, q2'⟩, ⟨q3, q3'⟩, ⟨q4, q4'⟩, ⟨q5, q5'⟩,
    hr1, hr2, hr3, hr4, hr5⟩ := golay_five_roots_in_interval
  have e12 : r1 ≠ r2 := by intro h; rw [h] at q1'; linarith
  have e13 : r1 ≠ r3 := by intro h; rw [h] at q1'; linarith
  have e14 : r1 ≠ r4 := by intro h; rw [h] at q1'; linarith
  have e15 : r1 ≠ r5 := by intro h; rw [h] at q1'; linarith
  have e23 : r2 ≠ r3 := by intro h; rw [h] at q2'; linarith
  have e24 : r2 ≠ r4 := by intro h; rw [h] at q2'; linarith
  have e25 : r2 ≠ r5 := by intro h; rw [h] at q2'; linarith
  have e34 : r3 ≠ r4 := by intro h; rw [h] at q3'; linarith
  have e35 : r3 ≠ r5 := by intro h; rw [h] at q3'; linarith
  have e45 : r4 ≠ r5 := by intro h; rw [h] at q4'; linarith
  set S : Finset ℝ := {r1, r2, r3, r4, r5} with hS
  have hScard : S.card = 5 := by
    rw [hS]
    simp [e12, e13, e14, e15, e23, e24, e25, e34, e35, e45]
  have hsub : S ⊆ Hgolay.roots.toFinset := by
    intro x hx
    rw [hS] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Multiset.mem_toFinset, mem_roots hgolay_ne_zero]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hge : 5 ≤ Hgolay.roots.card := by
    calc 5 = S.card := hScard.symm
      _ ≤ Hgolay.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card Hgolay.roots := Multiset.toFinset_card_le _
  have hle : Hgolay.roots.card ≤ 5 := by
    have := Hgolay.card_roots'
    rw [hgolay_natDegree] at this
    exact this
  have hcard : Hgolay.roots.card = 5 := le_antisymm hle hge
  refine ⟨hcard, ?_⟩
  -- the five located roots exhaust the root set
  have hfin : Hgolay.roots.toFinset = S := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hScard]
    calc Hgolay.roots.toFinset.card ≤ Multiset.card Hgolay.roots := Multiset.toFinset_card_le _
      _ = 5 := hcard
  intro r hr
  have : r ∈ Hgolay.roots.toFinset := Multiset.mem_toFinset.mpr hr
  rw [hfin, hS] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl | rfl <;> constructor <;> linarith

end Genus5Confinement
end SIDELvConservation
