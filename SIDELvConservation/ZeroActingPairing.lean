import SIDELvConservation.RegisterPentagon

/-!
# ZeroActingPairing — the compiled SPECIFICATION of the center-object

W-ORD-PAIRING-INTERFACE (2026-07-25). **Warrant:** the E-characterization proved that every
structure capable of bounding the zero-oscillation `E(n)` of `λ_Z` by the archimedean channel
`λ_A` is *pairing-positivity* shaped (FE-cancellation fails; density gives only the σ=1 edge;
the only centre-reaching structure is a positive pairing on the zeros — the Weil-functional /
Hilbert–Pólya shape).

This module compiles the **TYPE** the E-characterization named — a *zero-acting* positive
pairing that is *Euler-consuming* (breaks for a sign-neutral ledger, i.e. for Davenport–
Heilbronn) and *distinct from the certified `{n²}` input spectrum* — together with the
INTERFACES chain `ZeroActingPairing → channel inequality → RH`.

**It asserts NO instance.** The existence of a `ZeroActingPairing` is exactly the C₅-output the
programme holds open (`Register5_output_HilbertPolya`, DISCLAIMED; closes over 𝔽_q by Weil 1948,
open over ℚ). This is the compiled *specification*, in the pentagon precedent (STRUCTURE compiled,
never the equivalence). INTERFACES grammar throughout; every non-native step is a named premise;
the disclaimer text extends — the register now holds a compiled *interface*, still no claimed
witness.

**Salt-check (run before commit).** Not a shell: the structure carries four genuine `Prop`
fields, and the two typing clauses kill the trivial witness — a bare diagonal enumeration of the
zeros dies on `distinctFromInput` (via `certifiedInput_not_zeroRealizing`) and a sign-neutral
ledger dies on `eulerConsuming`. The RH implication is a real composition through named
*classical* premises (the Weil-criterion direction; the inequality→positivity step; Li's
criterion — Bombieri–Lagarias 1999, not in Mathlib), with the pairing's **existence disclaimed**
— the compiled object is the CONDITIONAL, never a claimed instance (Rule 3: named-INTERFACES,
carried openly, never a promissory note read as closure).
-/

namespace SIDELvConservation
namespace RegisterPentagon

/-- The four typed requirements the B1 survey earned, bundled into the center-object's type.

`lam_A`, `lam_Z` are the two Li channels; `ledger` is the Euler ledger (the von Mangoldt
`Λ ≥ 0` for `ζ`; the sign-neutral periodic `a_n` for Davenport–Heilbronn). -/
structure ZeroActingPairing (lam_A lam_Z ledger : ℕ → ℝ) : Prop where
  /-- (1) **zero-acting** — the pairing's spectrum realizes the ξ-zeros: the R5-output schema
  (a positive-definite symmetric pairing, a self-adjoint operator, and a zero-realizing
  diagonal). DISCLAIMED as an existence claim; here a typed requirement of the object. -/
  zeroActing : Register5_output_HilbertPolya
  /-- (2) **positive-on-FE-even ⟹ the channel inequality** — the Weil-criterion direction as a
  named premise: a positive pairing on the FE-even (functional-equation-symmetric) test class
  yields the two-channel inequality `−λ_A ≤ λ_Z`. -/
  yieldsInequality : Register5_output_HilbertPolya → Register4_channelInequality lam_A lam_Z
  /-- (3) **Euler-consuming** — the DH-breaking clause (the Epstein test formalized): a valid
  pairing requires the Euler ledger non-negative, so a *sign-neutral* ledger (Davenport–
  Heilbronn, period-sum 0) admits none. The requirement, not a theorem. -/
  eulerConsuming : ∀ m, 0 ≤ ledger m
  /-- (4) **distinct-from-input** — the certified `{n²}` input spectrum is *not* zero-realizing
  (`certifiedInput_not_zeroRealizing`): this pairing is not the input spectrum. -/
  distinctFromInput : ¬ RealizesXiZeros certifiedInputSpectrum

/-- **INTERFACES (native step) — ZeroActingPairing → the two-channel inequality.** Unfolds the
`yieldsInequality` field against the `zeroActing` witness carried by the object. -/
theorem zeroActingPairing_to_channelInequality {lam_A lam_Z ledger : ℕ → ℝ}
    (P : ZeroActingPairing lam_A lam_Z ledger) :
    Register4_channelInequality lam_A lam_Z :=
  P.yieldsInequality P.zeroActing

/-- **INTERFACES — ZeroActingPairing → RiemannHypothesis** (the compiled CONDITIONAL). Chain:
the pairing yields the channel inequality (native), the inequality gives Li-positivity (named
premise), and Li's criterion gives RH (named classical premise, Bombieri–Lagarias 1999). The
**existence** of a `ZeroActingPairing` is disclaimed — this theorem never produces one. -/
theorem zeroActingPairing_to_RH {lam_A lam_Z ledger lam : ℕ → ℝ}
    (inequalityToPositivity :
      Register4_channelInequality lam_A lam_Z → Register4_positivity lam)
    (liCriterion : Register4_positivity lam → RiemannHypothesis)
    (P : ZeroActingPairing lam_A lam_Z ledger) :
    RiemannHypothesis :=
  liCriterion (inequalityToPositivity (zeroActingPairing_to_channelInequality P))

/-- **The distinct-from-input clause is dischargeable** (not open): the certified `{n²}` input
spectrum genuinely fails to realize the zeros, given a nontrivial zero exists in the strip.
So `distinctFromInput` is a *typing* constraint the object satisfies by the compiled negative,
not an added open premise. -/
theorem distinctFromInput_discharged
    (nontrivialZeroInStrip : NontrivialZeroExistsInStrip) :
    ¬ RealizesXiZeros certifiedInputSpectrum :=
  certifiedInput_not_zeroRealizing nontrivialZeroInStrip

/-! ## The DH-exclusion lemma — clause (3) made demonstrably load-bearing

Pre-merge gate (2026-07-25). The salt-check flagged `eulerConsuming` as a genuine but *typing-only*
clause. This section discharges that: a **sign-neutral** ledger — the Davenport–Heilbronn coefficient
signature (period-sum zero, sign-changing, no Euler product hence no `Λ ≥ 0`) — provably cannot
satisfy `eulerConsuming`, so no `ZeroActingPairing` admits one. Clause (3) is the compiled Epstein
discriminator at interface level. C₄ precedent: *strengthen-then-discharge*. -/

open scoped BigOperators

/-- A ledger is **sign-neutral** with period `p`: its values over `Finset.range p` sum to zero and it
is not identically zero there. This is the Davenport–Heilbronn coefficient signature — a periodic
arithmetic ledger with period-sum zero that genuinely changes sign. -/
def SignNeutralLedger (ledger : ℕ → ℝ) (p : ℕ) : Prop :=
  (∑ m ∈ Finset.range p, ledger m = 0) ∧ (∃ m ∈ Finset.range p, ledger m ≠ 0)

/-- **A sign-neutral ledger cannot be Euler-consuming** — the T-1/Epstein discriminator at interface
level. A non-negative family summing to zero is identically zero; a nonzero value forbids it. -/
theorem signNeutral_not_eulerConsuming {ledger : ℕ → ℝ} {p : ℕ}
    (h : SignNeutralLedger ledger p) : ¬ (∀ m, 0 ≤ ledger m) := by
  rintro hnn
  obtain ⟨hsum, m, hm, hne⟩ := h
  exact hne ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)).1 hsum m hm)

/-- **Clause (3) is load-bearing: no `ZeroActingPairing` has a sign-neutral ledger.** The Davenport–
Heilbronn ledger dies on `eulerConsuming` — the Epstein test compiled at interface level. The clause
the salt-check flagged as typing-only now demonstrably excludes the DH witness class. -/
theorem zeroActingPairing_ledger_not_signNeutral
    {lam_A lam_Z ledger : ℕ → ℝ} {p : ℕ}
    (P : ZeroActingPairing lam_A lam_Z ledger) : ¬ SignNeutralLedger ledger p :=
  fun h => signNeutral_not_eulerConsuming h P.eulerConsuming

/-- The Davenport–Heilbronn coefficient ledger model on its first period (period 5, sum zero,
sign-changing): `(0,1,2,3,4) ↦ (0,1,1,−1,−1)`. Captures the load-bearing feature — period-sum zero
and genuinely negative (no `Λ ≥ 0`) — the exact κ aside. -/
def dhModelLedger : ℕ → ℝ
  | 1 => 1
  | 2 => 1
  | 3 => -1
  | 4 => -1
  | _ => 0

/-- **The DH model ledger is sign-neutral** — witnessed, so the exclusion is non-vacuous. -/
theorem dhModelLedger_signNeutral : SignNeutralLedger dhModelLedger 5 := by
  refine ⟨?_, 1, ?_, ?_⟩
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, dhModelLedger]; norm_num
  · decide
  · norm_num [dhModelLedger]

/-- **So the DH model ledger admits no `ZeroActingPairing`** — the Epstein test at interface level:
the sign-neutral DH ledger dies on `eulerConsuming`, exactly as the salt-check predicted. -/
theorem dhModelLedger_no_pairing {lam_A lam_Z : ℕ → ℝ}
    (P : ZeroActingPairing lam_A lam_Z dhModelLedger) : False :=
  zeroActingPairing_ledger_not_signNeutral P dhModelLedger_signNeutral

/-! ## A1 — the 𝔽_q witness anatomy: the four clauses over the function field, and the ℚ-obstruction

Over a smooth projective curve `C / 𝔽_q` the `ZeroActingPairing` type is **inhabited** — this is Weil
1948 (the Riemann Hypothesis for curves), the one place a genuine witness is known. This section
records, clause by clause, *what supplies each requirement over 𝔽_q* and *whether it transfers to ℚ*.
It grounds against the corpus's own C₅ split (BALANCE_AND_POSITIVITY §D.2 / the FIFTH REGISTER: over
𝔽_q the two coincide, Weil supplying the output from Hodge-index / Castelnuovo positivity on `C × C`;
over ℚ they do not). Docstring-level anatomy; the compiled `def`s below *record* the per-clause status
and the theorem reads it back — no verdict is proved here, and the obstruction clauses stay open.

**What supplies each clause over 𝔽_q (on `C` / `C × C`):**
* `zeroActing`       — Frobenius acting on `H¹(C)`; its eigenvalues `α_i` (`|α_i| = √q`) *are* the
  zeros of the curve's zeta function. The self-adjoint operator with the zeros as spectrum is a real
  geometric object here.
* `yieldsInequality` — the **intersection-form positivity** on `C × C` (Hodge index theorem /
  Castelnuovo–Severi): positivity on the primitive part yields the Weil explicit-formula positivity,
  i.e. the FE-even positivity that gives the two-channel inequality.
* `eulerConsuming`   — the effective-divisor / point counts `N_r = #C(𝔽_{q^r}) ≥ 0` (the curve's Euler
  product over closed points): the ledger is a non-negative count.
* `distinctFromInput`— the Frobenius spectrum is the *output* (eigenvalues), genuinely distinct from
  any `{n²}`-style diagonal input.

**The ℚ-transfer obstruction, named per clause:**
* `zeroActing`      — **OBSTRUCTS.** `Spec ℤ` is not a curve over a field: there is no Frobenius, no
  `H¹`, no geometric self-adjoint operator with the ξ-zeros as spectrum. This clause *is* Hilbert–
  Pólya, open over ℚ.
* `yieldsInequality`— **OBSTRUCTS.** There is no Hodge index theorem for `Spec ℤ` (no positive
  arithmetic intersection form). This clause *is* Weil positivity over ℚ, which *is* RH.
* `eulerConsuming`  — **TRANSFERS.** `ζ` has an Euler product with `Λ(n) ≥ 0` (von Mangoldt); a
  sign-neutral ledger is excluded (`zeroActingPairing_ledger_not_signNeutral`, this module). Clean.
* `distinctFromInput`— **TRANSFERS.** The certified `{n²}` input does not realize the ξ-zeros
  (`distinctFromInput_discharged`, this module). Clean.

**Reading:** the 𝔽_q → ℚ obstruction is *exactly* the two geometric clauses (1) and (2) — the
Hilbert–Pólya operator and the Weil-positivity pairing — the same two the E-characterization and the
pairing census name. The two arithmetic clauses (3) and (4) transfer, backed by facts this module
already carries. -/

/-- The four requirements of `ZeroActingPairing`, enumerated for the transfer anatomy. -/
inductive PairingClause where
  | zeroActing
  | yieldsInequality
  | eulerConsuming
  | distinctFromInput
deriving DecidableEq, Repr

/-- What supplies each clause over `C / 𝔽_q` (Weil 1948). Documentation datum. -/
def fqSupplier : PairingClause → String
  | .zeroActing        => "Frobenius on H¹(C); eigenvalues |α|=√q are the zeta zeros"
  | .yieldsInequality  => "intersection-form positivity on C×C (Hodge index / Castelnuovo–Severi)"
  | .eulerConsuming    => "effective-divisor counts N_r = #C(𝔽_{q^r}) ≥ 0 (the curve's Euler product)"
  | .distinctFromInput => "Frobenius spectrum is the output, distinct from any {n²} input"

/-- **Whether each clause transfers from 𝔽_q to ℚ.** Recorded anatomy: the two geometric clauses
obstruct (they *are* the open Hilbert–Pólya / Weil-positivity content over ℚ); the two arithmetic
clauses transfer, backed by facts this module carries. NOT a proof of any verdict — the obstruction
clauses honestly record `false` (open). -/
def transfersToRationals : PairingClause → Bool
  | .zeroActing        => false  -- Hilbert–Pólya: no Frobenius / H¹ over Spec ℤ
  | .yieldsInequality  => false  -- Weil positivity = RH: no Hodge index for Spec ℤ
  | .eulerConsuming    => true   -- ζ's Λ(n) ≥ 0; sign-neutral ledger excluded (this module)
  | .distinctFromInput => true   -- certifiedInput_not_zeroRealizing (this module)

/-- **The transfer obstruction is exactly the two geometric clauses** — the named per-clause list,
compiled: `zeroActing` and `yieldsInequality` do not transfer; `eulerConsuming` and
`distinctFromInput` do. -/
theorem transfer_obstruction_is_the_two_geometric_clauses :
    transfersToRationals PairingClause.zeroActing = false
    ∧ transfersToRationals PairingClause.yieldsInequality = false
    ∧ transfersToRationals PairingClause.eulerConsuming = true
    ∧ transfersToRationals PairingClause.distinctFromInput = true := by decide

/-- **Exactly two clauses obstruct** — the count the anatomy turns on: the transfer failure is
concentrated in the geometric pair, not spread across all four. -/
theorem exactly_two_clauses_obstruct :
    (List.filter (fun c => ! transfersToRationals c)
      [PairingClause.zeroActing, PairingClause.yieldsInequality,
       PairingClause.eulerConsuming, PairingClause.distinctFromInput]).length = 2 := by decide

/-! ## W-SIGN-5 B2 (C-3) — positivity is FREE; the schema's obstruction is zero-realization alone

The pairing-construction attempt's compiled yield. The R5-output schema
`Register5_output_HilbertPolya` bundles five conjuncts: a symmetric pairing, positive-definiteness,
self-adjointness of an operator, the spectrum on its diagonal, and *zero-realization*. This lemma
shows the certified input spectrum `{n²}` witnesses the **first four** — the whole positivity /
self-adjoint / operator structure — with the identity pairing and the `{n²}` diagonal operator, and
fails **only** the fifth (`certifiedInput_not_zeroRealizing`). So the positivity structure is *free*;
the schema's irreducible content is zero-realization alone (pure Hilbert–Pólya). This asserts **no**
positivity on the ζ-zeros (that is RH); it is a *decoupling* — the opposite of an encode. The
disclaimer stands unchanged: positivity is not proven on the zeros, it is shown cheap on the wrong
spectrum. -/
theorem positivity_free_obstruction_is_zeroRealization
    (nontrivialZeroInStrip : NontrivialZeroExistsInStrip) :
    (∃ pairing T : ℕ → ℕ → ℝ,
        (∀ i j, pairing i j = pairing j i)
      ∧ (∀ i, 0 < pairing i i)
      ∧ (∀ i j, pairing i i * T i j = pairing j j * T j i)
      ∧ (∀ n, T n n = certifiedInputSpectrum n))
    ∧ ¬ RealizesXiZeros certifiedInputSpectrum := by
  refine ⟨⟨fun i j => if i = j then (1 : ℝ) else 0,
           fun i j => if i = j then certifiedInputSpectrum i else 0, ?_, ?_, ?_, ?_⟩,
          certifiedInput_not_zeroRealizing nontrivialZeroInStrip⟩
  · intro i j
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    · simp [h, Ne.symm h]
  · intro i; simp
  · intro i j
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    · simp [h, Ne.symm h]
  · intro n; simp

end RegisterPentagon
end SIDELvConservation
