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

/-! ## The edge lemma (Ruling 1a) — Λ≥0 ⟹ drift `D ≥ 0`, and its DH break

The σ=1 **edge** register, compiled as an actual lemma. The prime channel's smooth contribution to
`λ_Z` — the **drift** `D(n)` — is, in the two-channel packaging, a ledger-weighted sum
`Σ_m ledger(m)·w(m,n)` with `w` the nonnegative explicit-formula weight. A non-negative ledger against
a non-negative weight gives `D(n) ≥ 0`.

**Classical (cited):** the ledger non-negativity is `Λ ≥ 0` (von Mangoldt,
`ArithmeticFunction.vonMangoldt_nonneg`), and the edge itself is de la Vallée Poussin's 3-4-1
positivity (the σ=1 zero-free region). **New packaging:** `D` as the nonneg-ledger drift in the
two-channel language. **What it does NOT reach:** the zero-oscillation `E(n)` — its weight is *not*
sign-definite, so this lemma is silent on the centre (E-characterization). It is the edge, and only
the edge. -/

/-- The prime-channel **drift** as a ledger-weighted window sum: `D(n) = Σ_{m<N} ledger(m)·w(m,n)`. -/
def driftSum (ledger : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, ledger m * w m n

/-- **The edge lemma.** A non-negative ledger against a non-negative weight yields a non-negative
drift. At `ledger = Λ` this is `Λ ≥ 0 ⟹ D(n) ≥ 0` — the σ=1 edge in two-channel language. Reaches
only the edge; `E` (the zeros) is untouched. -/
theorem edge_drift_nonneg {ledger : ℕ → ℝ} {w : ℕ → ℕ → ℝ} {N n : ℕ}
    (hL : ∀ m, 0 ≤ ledger m) (hw : ∀ m, 0 ≤ w m n) :
    0 ≤ driftSum ledger w N n :=
  Finset.sum_nonneg fun m _ => mul_nonneg (hL m) (hw m)

/-- **The DH break — the discriminator run on the lemma (its content).** For the sign-neutral DH
ledger the edge lemma's hypothesis fails, and the drift genuinely goes negative: with the weight
concentrated at the DH model's negative entry (`m=3`, value `−1`), `D < 0`. The edge lemma has no
purchase on a sign-neutral ledger — exactly its content: drift positivity is the `Λ ≥ 0` edge,
ζ-specific; Davenport–Heilbronn (no positive ledger) breaks it. -/
theorem edge_drift_neg_for_signNeutral :
    ∃ (w : ℕ → ℕ → ℝ) (N n : ℕ), (∀ m, 0 ≤ w m n) ∧ driftSum dhModelLedger w N n < 0 := by
  refine ⟨fun m _ => if m = 3 then 1 else 0, 5, 0, ?_, ?_⟩
  · intro m; by_cases h : m = 3 <;> simp [h]
  · simp only [driftSum, Finset.sum_range_succ, Finset.sum_range_zero, dhModelLedger]
    norm_num

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

/-! ## W-SIGN-6 Prong 1a — the realization ledger

What the programme already holds toward "a self-adjoint operator whose spectrum realizes the
ζ-zeros", enumerated with what each asset realizes. Grounded: `certifiedInput_not_zeroRealizing`
(this module); the C₅ distance marker; SIDE-frobenius `indicial_forces_half` @ `2efe9f2` (the −½
indicial forces σ=1/2 — the *location*, `r²+r+¼=0 ⟹ −r=½`, pure ℚ-algebra); `h1_complete_at_Phi`.
The ledger's finding, compiled below: each asset realizes something else — the location, the wrong
spectrum, the distance, or the input surround — and **none realizes the discrete zero spectrum
`{γ_n}`**. That gap is zero-realization itself. -/

/-- The programme's assets bearing on zero-realization. -/
inductive RealizationAsset where
  | certifiedInput
  | c5Distance
  | berryKeatingIndicial
  | h1CompleteAtPhi
deriving DecidableEq, Repr

/-- What a realization asset actually realizes. `zeroSpectrum` is the target — held by no asset. -/
inductive RealizesWhat where
  | location            -- σ = 1/2 (Berry–Keating indicial reflection fixed point)
  | wrongSpectrum       -- {n²} (the certified input — positive, self-adjoint, WRONG)
  | distanceMarker      -- the compiled input↔output negative
  | inputSurround       -- h1 at Φ (surround, not output)
  | zeroSpectrum        -- the {γ_n} — the missing target
deriving DecidableEq, Repr

/-- The ledger map: each asset to what it realizes. -/
def assetRealizes : RealizationAsset → RealizesWhat
  | .certifiedInput       => .wrongSpectrum
  | .c5Distance           => .distanceMarker
  | .berryKeatingIndicial => .location
  | .h1CompleteAtPhi      => .inputSurround

/-- **The realization ledger's finding: no asset realizes the zero spectrum.** Four assets realize
four *different* things — location, the wrong spectrum, the distance, the surround; the discrete
zero spectrum `{γ_n}` is held by none. That absence is exactly zero-realization, the irreducible
core's first half. -/
theorem no_asset_realizes_zeroSpectrum (a : RealizationAsset) :
    assetRealizes a ≠ RealizesWhat.zeroSpectrum := by cases a <;> decide

/-- **The location is owned, the spectrum is not.** The Berry–Keating indicial realizes σ=1/2 (the
real part), and no asset realizes the discrete ordinates — the delta to zero-realization is precisely
the imaginary spectrum. -/
theorem location_owned_spectrum_not :
    assetRealizes RealizationAsset.berryKeatingIndicial = RealizesWhat.location
    ∧ ∀ a, assetRealizes a ≠ RealizesWhat.zeroSpectrum := by
  refine ⟨rfl, fun a => ?_⟩; cases a <;> decide

/-! ## W-SUBSTRATE (2026-07-27) — the two deepest-face SPECS, typed as interfaces

Arm 1 types the sign wall's single-object realization `X`; Arm 2 types the derivative wall's
family-requirement. Both are SPECIFICATIONS (Prop structures / named premises); NEITHER asserts an
instance — existence disclaimed, as with `ZeroActingPairing`. The census (PATHS §ANNEX C/D) carries
the geometric interpretation and the field-candidate grading; here is the compiled operational core. -/

/-- **Arm 1 — the X-realization spec.** The single-object geometric realization `X` of the sign
wall's deepest face. GEOMETRIC INTERPRETATION (documented, deliberately NOT encoded as opaque Lean
fields — contentless Props would be the encode-not-derive trap): (G1) `X` is a geometric object over
the arithmetic base whose Frobenius-analog realizes the ξ-ordinates; (G2) the self-product `X × X`
carries the intersection / Hodge-index pairing — the Weil positivity, UNIVERSAL because it is one
object's self-product, NOT a family (the W-FAMILY distinction); (G3) the functional equation is
Poincaré duality on `X`; (G4) the Euler ledger is the point-count of `X`. The three fields below are
the OPERATIONAL content those interpretations must supply; they compose to a `ZeroActingPairing`, so
`X` is exactly `zeroActing`, single-object in kind. -/
structure XRealization (lam_A lam_Z ledger : ℕ → ℝ) : Prop where
  /-- (X1 ← G1,G3) `X` hands over the self-adjoint operator: the Hilbert–Pólya R5-output. -/
  handsOverOperator : Register5_output_HilbertPolya
  /-- (X2 ← G2) the `X × X` intersection pairing is the FE-even positivity that yields the channel
  inequality (single-object / universal, not family-sourced). -/
  selfProductPositivity : Register5_output_HilbertPolya → Register4_channelInequality lam_A lam_Z
  /-- (X3 ← G4) the Euler ledger is the point-count of `X`, hence non-negative. -/
  pointCountLedger : ∀ m, 0 ≤ ledger m

/-- **INTERFACE — XRealization → ZeroActingPairing** (`X` is single-object-kind `zeroActing`). Three
clauses direct; `distinctFromInput` from the compiled negative under the named strip premise. No
instance asserted. -/
theorem xRealization_to_zeroActingPairing {lam_A lam_Z ledger : ℕ → ℝ}
    (nontrivialZeroInStrip : NontrivialZeroExistsInStrip)
    (X : XRealization lam_A lam_Z ledger) :
    ZeroActingPairing lam_A lam_Z ledger :=
  { zeroActing := X.handsOverOperator
    yieldsInequality := X.selfProductPositivity
    eulerConsuming := X.pointCountLedger
    distinctFromInput := certifiedInput_not_zeroRealizing nontrivialZeroInStrip }

/-- **INTERFACE — XRealization → RiemannHypothesis** (the compiled conditional, via `zeroActing`). -/
theorem xRealization_to_RH {lam_A lam_Z ledger lam : ℕ → ℝ}
    (nontrivialZeroInStrip : NontrivialZeroExistsInStrip)
    (inequalityToPositivity :
      Register4_channelInequality lam_A lam_Z → Register4_positivity lam)
    (liCriterion : Register4_positivity lam → RiemannHypothesis)
    (X : XRealization lam_A lam_Z ledger) :
    RiemannHypothesis :=
  zeroActingPairing_to_RH inequalityToPositivity liCriterion
    (xRealization_to_zeroActingPairing nontrivialZeroInStrip X)

/-- **Arm 2 — the simplicity family spec.** The derivative wall's family-requirement (§ANNEX D),
typed as a SPEC. GEOMETRIC INTERPRETATION (documented): a family `𝓕 ∋ ζ` with a large geometric
monodromy group, an equidistribution measure (the symmetry type), and a conductor ordering. What such
a family DELIVERS is only GENERIC simplicity (Katz–Sarnak / Kowalski) — modeled here by the member
index `ℕ` (conductor order) and simplicity for every member past the distinguished index `0` (= ζ). -/
structure SimplicityFamilySpec (simpleAt : ℕ → Prop) : Prop where
  /-- (F-generic ← monodromy/equidistribution over a conductor ordering) simplicity for every member
  past the distinguished index — density-1 / all-but-the-exception, here every `n ≠ 0`. -/
  deliversGeneric : ∀ n, n ≠ 0 → simpleAt n

/-- **The family's KNOWN residual — generic is NOT universal (the measure-zero escape).** A witness
meeting `SimplicityFamilySpec` need not give `simpleAt 0` (index `0` = the distinguished member, ζ):
the family delivers generic simplicity but not ζ's own. This is the honest logical shape of the
measure-zero escape — WHY no family closes the derivative wall, and why its core differs in kind from
Arm 1's single-object `X` (W-FAMILY). Not a claim about any concrete ζ-family; the residual clause. -/
theorem simplicityFamily_generic_not_universal :
    ∃ simpleAt : ℕ → Prop, SimplicityFamilySpec simpleAt ∧ ¬ (∀ n, simpleAt n) :=
  ⟨fun n => n ≠ 0, ⟨fun _ h => h⟩, fun h => (h 0) rfl⟩

end RegisterPentagon
end SIDELvConservation
