import Mathlib

/-!
# Genus5 — D-2b, unit 1: the Type II classification arithmetic at genus ≤ 5

The genus ≤ 5 theorem's first half, certified: **the classification**. For Type II self-dual
weight enumerators the genus is forced into one residue class, and the Mallows–Sloane bound
then forces the length at each admissible genus — leaving exactly the three objects the
computational sitting found (e₈ at n = 8; W₈² at n = 16; the Golay enumerator at n = 24).

## What is stipulated at cite, and what is derived here

**STIPULATED (cited data; named in advance, per the Davenport–Heilbronn precedent).**
(1) **Mallows–Sloane**: for a Type II code, `d ≤ 4 * (n / 24) + 4`. (2) **Gleason
uniqueness**: that at each admissible `(n, d)` the invariant space is spanned as claimed and
the stated enumerator is its unique member with the required vanishing. (3) **The certificate
construction**: that `H(u)` is the Galois-locked object attached to the enumerator (the same
stipulation `LeadLaw` carries).

**DERIVED IN-KERNEL (this unit).** The genus arithmetic — that Type II forces `g % 4 = 1`, so
genera 2, 3, 4 are EMPTY — and the Mallows–Sloane forcing: at `g = 1` only `m = 1`, and at
`g = 5` only `m = 2` or `m = 3`. Together: at genus ≤ 5 the admissible lengths are exactly
n = 8, 16, 24.

**DEFERRED to unit 2 (registered, not compiled here).** The confinement certificates — that
each of the three `H(u)` has all roots in `[0, 4]` — by the per-object routes verified before
registration: e₈ linear; W₈² by its rational factorization `(u−2)(u²−4u+1)²`; the Golay by
IVT sign-alternation at six explicit rationals with the degree cap closing the count.

## What this does NOT say

Nothing of ζ, of RH, or of `h2`; no claim about any genus beyond 5; no claim that the
certificate construction, Mallows–Sloane, or Gleason uniqueness are proved here; and no
confinement claim whatever — that is unit 2.

0 sorry, 0 native_decide.
-/

namespace SIDELvConservation
namespace Genus5

/-- The parameters of a Type II self-dual weight enumerator, as used by the classification:
length `n = 8 * m`, minimum distance `d` divisible by 4 and positive, and genus `g` tied to
them by `g + d = 4 * m + 1` (the genus relation `g = n/2 − d + 1`, written without ℕ
subtraction). `MS` is the stipulated Mallows–Sloane bound. -/
structure TypeIIParams where
  m : ℕ
  d : ℕ
  g : ℕ
  hm : 1 ≤ m
  hd4 : 4 ≤ d
  hdvd : 4 ∣ d
  hgenus : g + d = 4 * m + 1
  MS : d ≤ 4 * ((8 * m) / 24) + 4

/-- **Derived.** The genus of a Type II self-dual weight enumerator is `≡ 1 (mod 4)`. -/
theorem genus_mod_four (P : TypeIIParams) : P.g % 4 = 1 := by
  obtain ⟨k, hk⟩ := P.hdvd
  have h := P.hgenus
  rw [hk] at h
  omega

/-- **Derived.** Genera 2, 3, 4 are empty for Type II. -/
theorem genus_ne_two_three_four (P : TypeIIParams) : P.g ≠ 2 ∧ P.g ≠ 3 ∧ P.g ≠ 4 := by
  have h := genus_mod_four P
  refine ⟨?_, ?_, ?_⟩ <;> (intro hg; rw [hg] at h; omega)

/-- **Derived.** At genus 1 the Mallows–Sloane bound forces `m = 1`, i.e. length 8. -/
theorem genus_one_forces (P : TypeIIParams) (h1 : P.g = 1) : P.m = 1 := by
  have hg := P.hgenus
  have hMS := P.MS
  have hm := P.hm
  rw [h1] at hg
  -- d = 4 * m, and 4 * m ≤ 4 * ((8*m)/24) + 4
  omega

/-- **Derived.** At genus 5 the Mallows–Sloane bound forces `m = 2` or `m = 3`, i.e. length
16 or 24. -/
theorem genus_five_forces (P : TypeIIParams) (h5 : P.g = 5) : P.m = 2 ∨ P.m = 3 := by
  have hg := P.hgenus
  have hMS := P.MS
  have hm := P.hm
  have hd := P.hd4
  rw [h5] at hg
  omega

/-- **THE CLASSIFICATION (derived).** At genus ≤ 5, a Type II self-dual weight enumerator has
length exactly 8, 16, or 24 — genera 2, 3, 4 being empty, genus 1 forcing length 8, and genus
5 forcing length 16 or 24. (Which enumerator sits at each length is Gleason uniqueness, a
stipulated datum; this theorem is the length classification only.) -/
theorem classification (P : TypeIIParams) (hle : P.g ≤ 5) :
    8 * P.m = 8 ∨ 8 * P.m = 16 ∨ 8 * P.m = 24 := by
  have hmod := genus_mod_four P
  have hg1 : P.g = 1 ∨ P.g = 5 := by omega
  rcases hg1 with h | h
  · left; rw [genus_one_forces P h]
  · rcases genus_five_forces P h with h2 | h3
    · right; left; rw [h2]
    · right; right; rw [h3]

end Genus5
end SIDELvConservation
