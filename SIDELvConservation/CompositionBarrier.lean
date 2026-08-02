import SIDELvConservation.QWantedPoster

/-!
# CompositionBarrier — E-8: no finite composition of criterion-layer data yields a carrier

E-8 of the experiment slate (2026-08-02), taxonomy-scoped by the screen's §0: the criterion layer
(one-variable positivities — coefficient nonnegativity, single-index moment bounds, edge-reaching
inequalities) versus the carrier layer (a two-variable positive form meeting the wanted-poster
clauses). **The compiled question: can any finite composition of criterion-layer data yield a
carrier?**

**The BGS/relativization shape, Face-E-validated.** The composition operations (sums, products,
limits along stated topologies, linear maps of one-variable reads) share one structural property:
each factors through the one-variable observable, so anything built from them TRANSPORTS along
one-variable agreement. That soundness property is how the operations are typed here — the same
§4b move the Face-E pass validated (`Derives` as transport): we do not enumerate the operations;
we type their closure by what they can see. A witness world where all criterion data agree while
the carrier property differs then bars every composition at once.

**The witness world (minimal, exact).** Two symmetric two-variable forms with EQUAL one-variable
(diagonal) data and OPPOSITE carrier status:
- `carrierForm`  = [[1, 0], [0, 1]] — positive definite (a carrier: the two-variable positivity holds);
- `impostorForm` = [[1, 2], [2, 1]] — same diagonal (1, 1), indefinite (det = −3 < 0; not a carrier).
The analytic-world kin are the arc's Epstein/Golay witnesses (same shape: agreement on the
accessible layer, divergence on the property); this module compiles the shape at the minimal
finite instance, as `SieveCeilingWitness` did for the ceiling.

**ANTI-OVERCLAIM (load-bearing).** Model-level: the forms are 2×2; the compiled content is the
SCHEMA at its minimal witness world — one-variable data underdetermines the two-variable form,
so no transport-sound composition of criterion data certifies the carrier property. No claim
about ζ beyond the shape (the analytic instantiation is Face-E's territory); the k-variable
LADDER (does k-variable data underdetermine (k+1)-variable structure — simplicity as the k = 3
suspect) remains E-8's open upper floors, not compiled here.

0 sorry, 0 native_decide. HELD where kernel lands; nothing deposits.
-/

namespace SIDELvConservation
namespace CompositionBarrier

/-- A symmetric two-variable form on two indices: [[a, b], [b, c]]. The off-diagonal `b` is the
pair-index datum — exactly what one-variable reads cannot see. -/
structure SymForm where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq, Repr

/-- The criterion layer: one-variable (diagonal) agreement. Two forms agree on every
one-variable read iff their diagonals match — coefficient values, single-index moments, and
edge inequalities are all functions of the diagonal in this world. -/
def diagAgree (M N : SymForm) : Prop := M.a = N.a ∧ M.c = N.c

/-- The carrier property (the wanted-poster's positivity at rank 2, Sylvester form):
positive-definite — the leading entry and the determinant both positive. -/
def IsCarrier (M : SymForm) : Prop := 0 < M.a ∧ 0 < M.a * M.c - M.b * M.b

/-- **The composition closure, typed by soundness** (the §4b move): a property is derivable from
criterion-layer data at `M` iff it transports to every form agreeing with `M` on that layer.
Sums, products, limits, and linear maps of one-variable reads all factor through the diagonal,
hence land inside this closure; the definition types them all at once. -/
def DerivesFromCriterion (P : SymForm → Prop) (M : SymForm) : Prop :=
  ∀ N, diagAgree M N → P N

/-- The carrier witness: the identity form, positive definite. -/
def carrierForm : SymForm := ⟨1, 0, 1⟩

/-- The impostor: same diagonal, indefinite (det = 1 − 4 = −3). -/
def impostorForm : SymForm := ⟨1, 2, 1⟩

/-- The two witnesses agree on the entire criterion layer. -/
theorem witnesses_agree : diagAgree carrierForm impostorForm := ⟨rfl, rfl⟩

/-- The carrier witness is a carrier. -/
theorem carrierForm_isCarrier : IsCarrier carrierForm := by
  constructor <;> decide

/-- The impostor is not a carrier (its determinant is negative). -/
theorem impostorForm_not_carrier : ¬ IsCarrier impostorForm := by
  intro h
  exact absurd h.2 (by decide)

/-- **THE COMPOSITION BARRIER.** No transport-sound composition of criterion-layer
(one-variable) data derives the carrier property — even at a point where the property HOLDS:
the impostor agrees on every one-variable read and fails the two-variable positivity, so the
derivation would transport to a falsehood. One-variable data underdetermines the two-variable
form; the sort's cleanness, made structural. -/
theorem composition_barrier : ¬ DerivesFromCriterion IsCarrier carrierForm :=
  fun h => impostorForm_not_carrier (h impostorForm witnesses_agree)

/-- The barrier in its two-witness statement (the Face-E sibling shape): criterion-layer
agreement plus carrier-divergence, exhibited. -/
theorem barrier_witnesses :
    diagAgree carrierForm impostorForm ∧ IsCarrier carrierForm ∧ ¬ IsCarrier impostorForm :=
  ⟨witnesses_agree, carrierForm_isCarrier, impostorForm_not_carrier⟩

end CompositionBarrier
end SIDELvConservation
