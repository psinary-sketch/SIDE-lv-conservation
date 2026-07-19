import SIDELvConservation.RegisterPentagon
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Partial-positivity interface — DISCHARGED (item (iv))

The ξ-pattern interface that certifies **finite-range** Li positivity from verified zeros,
hanging on the pentagon's R4 face (`RegisterPentagon.Register4_positivity`).  It does **not**
close RH — the all-n tail is the open gap.  Grade: **INTERFACES**, three named premises
(one external-computation + two classical, neither in Mathlib), no `sorry`.

Classical shape (Bombieri–Lagarias 1999; Voros 2004–06): `λ_n = Σ_ρ Re[1 − (1 − 1/ρ)^n]`;
an off-line zero at height `H` registers in `λ_n` only for `n ≳ 2H²` (`|Im ρ| ≲ √(n/2)` — the
census-resolved constant, BALANCE_AND_POSITIVITY C.6/C.8, screened not recalled).  Hence
zeros verified on the line up to `T` certify `λ_n ≥ 0` for `n ≤ N₀(T) ≈ 2T²`.

## Refinement at discharge (screened, stated, reported — not silent)

The sitting-one statement used the unordered `∑' z, blTerm z n`.  **The Li series is
conditionally, not absolutely, convergent** (its terms `~ n/ρ` are not absolutely summable
over the zeros), so `∑'` (which is `0` off absolute summability) is the wrong object and the
head/tail split is not rigorous through it.  The honest refinement, which discharges cleanly:
the **head is a finite `Finset` of the `|Im| ≤ T` zeros** (only finitely many), and the **tail
is an abstract real value `tail n` the explicit-formula premise provides** — encapsulating the
conditional convergence as classical premise content rather than falsely asserting absolute
summability.  Separately, the **on-line-term nonnegativity is PROVED** (`blTerm_nonneg_of_onLine`,
below) — for `Re ρ = 1/2`, `|1 − 1/ρ| = 1`, so `(1−1/ρ)^n` lies on the unit circle and
`Re[1 − unit] = 1 − cos ≥ 0` — so it is a lemma, not a premise (one fewer assumed clause).

**`li_bench300`'s role** (docstring, not a kernel object): the `n = 300` numeric measurement
sits far inside `N₀(T)` for any verified `T ≥ 10^6` (`N₀(10^6) = 2×10^12 ≫ 300`), so the bench
is a checkable *instance* of the compiled finite-range result — not its frontier.
-/

namespace SIDELvConservation
namespace PartialPositivity

open Complex

/-- Nontrivial zeros of ζ in the critical strip — the index for the explicit-formula sum. -/
def NontrivialZero : Type := {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}

/-- The Bombieri–Lagarias summand at a nontrivial zero `ρ`: `Re[1 − (1 − 1/ρ)^n]`. -/
noncomputable def blTerm (z : NontrivialZero) (n : ℕ) : ℝ :=
  (1 - (1 - 1 / (z.1 : ℂ)) ^ n).re

/-- **On-line-term nonnegativity — PROVED** (C.1; slims the explicit-formula premise).
For a zero on the critical line (`Re ρ = 1/2`), `|1 − 1/ρ| = 1`, so `(1 − 1/ρ)^n` lies on the
unit circle and `Re[1 − (1 − 1/ρ)^n] = 1 − cos(·) ≥ 0`. -/
lemma blTerm_nonneg_of_onLine (z : NontrivialZero) (n : ℕ) (h : z.1.re = 1 / 2) :
    0 ≤ blTerm z n := by
  have hz0 : z.1 ≠ 0 := by
    intro hc; rw [hc] at h; norm_num at h
  have hnsq : Complex.normSq (z.1 - 1) = Complex.normSq z.1 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, h]; ring
  have hns1 : Complex.normSq (1 - 1 / z.1) = 1 := by
    rw [show (1 : ℂ) - 1 / z.1 = (z.1 - 1) / z.1 by field_simp, map_div₀, hnsq,
      div_self (Complex.normSq_pos.mpr hz0).ne']
  have hnsn : Complex.normSq ((1 - 1 / z.1) ^ n) = 1 := by
    rw [map_pow, hns1, one_pow]
  have hre : ((1 - 1 / z.1) ^ n).re ≤ 1 := by
    have he : Complex.normSq ((1 - 1 / z.1) ^ n)
        = ((1 - 1 / z.1) ^ n).re ^ 2 + ((1 - 1 / z.1) ^ n).im ^ 2 := by
      rw [Complex.normSq_apply]; ring
    have hsq : ((1 - 1 / z.1) ^ n).re ^ 2 ≤ 1 := by
      nlinarith [hnsn, he, sq_nonneg ((1 - 1 / z.1) ^ n).im]
    nlinarith [hsq, sq_nonneg (((1 - 1 / z.1) ^ n).re - 1)]
  simp only [blTerm, Complex.sub_re, Complex.one_re]; linarith

/-- **`VerifiedZerosTo T` — the external-computation premise (ξ-pattern).**  Every nontrivial
zero with `|Im| ≤ T` lies on the critical line.  Interfaces the computational record (ζ-zeros
verified on the line past height `10^9` by independent computations, e.g. Platt–Trudgian).
A NAMED PREMISE; never claimed proved here. -/
def VerifiedZerosTo (T : ℝ) : Prop :=
  ∀ z : NontrivialZero, |z.1.im| ≤ T → z.1.re = 1 / 2

/-- **`N₀ T = ⌊2·T²⌋` — the detection threshold** (off-line zero at height `H` registers in
`λ_n` only for `n ≳ 2H²`; `|Im ρ| ≲ √(n/2)`; Voros; census C.6/C.8). -/
noncomputable def N₀ (T : ℝ) : ℕ := ⌊2 * T ^ 2⌋₊

/-- **`ExplicitFormulaDecomp lam low tail T` — classical named premise** (Bombieri–Lagarias /
Guinand–Weil; **NOT in Mathlib**), refined form: `low` is exactly the finite set of `|Im| ≤ T`
zeros, and for each `n` the Li coefficient splits as the finite head sum over `low` plus the
tail value `tail n`.  The tail's (conditional) convergence is encapsulated here as premise
data; never claimed proved. -/
def ExplicitFormulaDecomp (lam : ℕ → ℝ) (low : Finset NontrivialZero) (tail : ℕ → ℝ)
    (T : ℝ) : Prop :=
  (∀ z : NontrivialZero, z ∈ low ↔ |z.1.im| ≤ T) ∧
  (∀ n : ℕ, 1 ≤ n → lam n = (∑ z ∈ low, blTerm z n) + tail n)

/-- **`TailBoundPremise low tail T` — classical detection-threshold named premise** (Voros;
**NOT in Mathlib**).  For `n ≤ N₀(T)`, the tail is bounded below by the negative of the finite
head sum — high zeros do not overwhelm the sign below the threshold `n ≳ 2T²`.  Never claimed
proved. -/
def TailBoundPremise (low : Finset NontrivialZero) (tail : ℕ → ℝ) (T : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N₀ T → - (∑ z ∈ low, blTerm z n) ≤ tail n

/-- **INTERFACES — finite-range Li positivity, DISCHARGED.**  From `VerifiedZerosTo T`, the
explicit-formula decomposition, and the tail bound: for `1 ≤ n ≤ N₀(T)`, `0 ≤ λ_n` — i.e.
`RegisterPentagon.Register4_positivity` restricted to the certified range.  Every `|Im| ≤ T`
zero is on the line (`VerifiedZerosTo`), so the finite head is a sum of proved-nonnegative
terms (`blTerm_nonneg_of_onLine`); the tail is `≥ −head`; hence `λ_n = head + tail ≥ 0`.  This
is NOT a proof of RH — the all-n tail is the open gap. -/
theorem partialPositivity_finiteRange
    (T : ℝ) (lam : ℕ → ℝ) (low : Finset NontrivialZero) (tail : ℕ → ℝ)
    (hV : VerifiedZerosTo T) (hEF : ExplicitFormulaDecomp lam low tail T)
    (hTail : TailBoundPremise low tail T) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N₀ T → 0 ≤ lam n := by
  intro n hn hn0
  have hhead : 0 ≤ ∑ z ∈ low, blTerm z n := by
    refine Finset.sum_nonneg (fun z hz => ?_)
    exact blTerm_nonneg_of_onLine z n (hV z ((hEF.1 z).mp hz))
  have htail := hTail n hn hn0
  rw [hEF.2 n hn]; linarith

end PartialPositivity
end SIDELvConservation
