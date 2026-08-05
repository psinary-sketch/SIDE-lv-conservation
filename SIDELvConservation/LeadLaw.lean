import SIDELvConservation.FieldLayer

/-!
# LeadLaw — D-2a: the certificate's leading coefficient is the defect's square

The programme's first OWNED supplier theorem, converted from a computed law to a certified
terminal. The setting is the fourth supplier row (self-dual codes; Duursma's zeta polynomial),
and the compiled content is the identity that made the toy's selection anatomy legible:

  **the Galois-normalized certificate's leading coefficient is `p 0 ^ 2`** —

where `p` is the zeta polynomial's coefficient sequence and `p 0` its constant term (which
Duursma's `P(0)` formula identifies with `A_d / ((q-1) * C(n,d))`, the normalized minimum-weight
count — the "defect" whose square appears).

## What is stipulated at cite, and what is derived here

**STIPULATED — ONE named premise (cited datum; not re-proven, per the Davenport–Heilbronn
precedent).** Duursma's construction of the zeta polynomial `P` from a code's weight enumerator,
his `P(0)` formula, and the self-dual functional equation `p (2g - i) = q ^ (g - i) * p i`. The
functional equation enters as the HYPOTHESIS `SelfDualFE`, so the theorem's content is what
follows FROM it.

**DERIVED IN-KERNEL.** (i) that the certificate family `v` (the Chebyshev-like basis in which
`h` is expanded) is monic of degree `j` at each `j ≥ 1`; (ii) that the expansion's leading
coefficient is therefore its top coefficient `c g`; (iii) **that `c g` is the top normalized
coefficient** — this was a second stipulation at the first pass and is now derived, in
`FieldLayer.top_coeff_of_expansion`, by reading the degree-`2g` coefficient off the expansion
relation; (iv) that the functional equation forces the top normalized coefficient to equal
`p 0`; hence (v) that the certificate `H = h * hᵒ` has leading coefficient `p 0 ^ 2`.

**The premise count moved from two to one at the field layer, exactly as the scoping predicted.**
Duursma's functional equation does not convert at any field cost — it is a theorem about codes,
not about fields — so the terminal stays conditional on it and is graded accordingly.

## What this does NOT say

Nothing here mentions ζ, the Riemann Hypothesis, or `h2`; nothing asserts that any code's zeta
polynomial exists, that its roots lie anywhere, or that Duursma-RH holds in any case. The
theorem is a statement about coefficient sequences satisfying a functional equation. Its use
in the arc is exactly one sentence: the defect's square is the SYMMETRY layer's universal
gift, so selection lives entirely in the additive half.

0 sorry, 0 native_decide.
-/

namespace SIDELvConservation
namespace LeadLaw

open Polynomial FieldLayer

variable {K : Type*} [Field K]

/-- The Chebyshev-like basis in which the certificate `h` is expanded:
`v 0 = 2`, `v 1 = X`, `v (j+2) = X * v (j+1) - v j`. -/
noncomputable def v : ℕ → K[X]
  | 0 => C 2
  | 1 => X
  | (j + 2) => X * v (j + 1) - v j

@[simp] theorem v_zero : (v 0 : K[X]) = C 2 := rfl
@[simp] theorem v_one : (v 1 : K[X]) = X := rfl
theorem v_succ_succ (j : ℕ) : (v (j + 2) : K[X]) = X * v (j + 1) - v j := rfl

/-- Every `v j` with `j ≥ 1` is monic of degree `j`. -/
theorem v_monic_natDegree : ∀ j : ℕ, (v (j + 1) : K[X]).Monic ∧ (v (j + 1) : K[X]).natDegree = j + 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => exact ⟨monic_X, natDegree_X⟩
    | 1 =>
      have h2 : (v 2 : K[X]) = X ^ 2 - C 2 := by
        rw [v_succ_succ 0, v_one, v_zero]; ring
      exact ⟨by rw [h2]; exact monic_X_pow_sub_C 2 (by norm_num),
             by rw [h2]; exact natDegree_X_pow_sub_C⟩
    | (k + 2) =>
      obtain ⟨hm1, hd1⟩ := ih (k + 1) (by omega)
      obtain ⟨hm0, hd0⟩ := ih k (by omega)
      -- v (k+3) = X * v (k+2) - v (k+1)
      have hrec : (v (k + 3) : K[X]) = X * v (k + 2) - v (k + 1) := v_succ_succ (k + 1)
      have hXm : ((X : K[X]) * v (k + 2)).Monic := monic_X.mul hm1
      have hXd : ((X : K[X]) * v (k + 2)).natDegree = k + 3 := by
        rw [natDegree_mul (X_ne_zero) hm1.ne_zero, natDegree_X, hd1]
        omega
      have hsub : (v (k + 1) : K[X]).natDegree < ((X : K[X]) * v (k + 2)).natDegree := by
        rw [hXd, hd0]; omega
      have hdlt : (v (k + 1) : K[X]).degree < ((X : K[X]) * v (k + 2)).degree :=
        degree_lt_degree hsub
      refine ⟨?_, ?_⟩
      · rw [hrec]; exact hXm.sub_of_left hdlt
      · rw [hrec, natDegree_sub_eq_left_of_natDegree_lt hsub, hXd]

theorem v_monic (j : ℕ) : (v (j + 1) : K[X]).Monic := (v_monic_natDegree j).1

theorem v_natDegree (j : ℕ) : (v (j + 1) : K[X]).natDegree = j + 1 := (v_monic_natDegree j).2

/-- The normalized coefficient entering the certificate at the top index,
`pt (2g) = p (2g) / q ^ g`. -/
noncomputable def ptTop (q : K) (g : ℕ) (p : ℕ → K) : K := p (2 * g) / q ^ g

/-- The certificate `h`, expanded in the `v`-basis with the normalized coefficients:
`h = Σ_{j ≤ g} c j • v j`, whose top term is `c g • v g`. -/
noncomputable def hOf (g : ℕ) (c : ℕ → K) : K[X] :=
  ∑ j ∈ Finset.range (g + 1), C (c j) * v j

/-- **(i)–(ii)** The expansion's leading coefficient is its top coefficient: for `g ≥ 1` with a
nonzero top coefficient, `hOf` has degree `g` and leading coefficient `c g`. The proof is the
degree bookkeeping of the `v`-basis: the top term is `c g • v g` with `v g` monic of degree `g`,
and every earlier term has degree `< g`. -/
theorem leadingCoeff_hOf (g : ℕ) (c : ℕ → K) (hg : 1 ≤ g) (hc : c g ≠ 0) :
    (hOf g c).leadingCoeff = c g := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  have hsplit : hOf (k + 1) c = (∑ j ∈ Finset.range (k + 1), C (c j) * v j) + C (c (k+1)) * v (k+1) := by
    rw [hOf, Finset.sum_range_succ]
  have hdeg_top : ((C (c (k+1)) : K[X]) * v (k+1)).natDegree = k + 1 := by
    rw [natDegree_C_mul hc, v_natDegree]
  have hlead_top : ((C (c (k+1)) : K[X]) * v (k+1)).leadingCoeff = c (k+1) := by
    rw [leadingCoeff_mul, leadingCoeff_C, (v_monic k).leadingCoeff, mul_one]
  have hrest_nat : (∑ j ∈ Finset.range (k + 1), (C (c j) : K[X]) * v j).natDegree ≤ k := by
    refine natDegree_sum_le_of_forall_le _ _ ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    have hle : ((C (c j) : K[X]) * v j).natDegree ≤ j := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, zero_add]
      match j with
      | 0 => simp [v_zero]
      | (m + 1) => rw [v_natDegree]
    omega
  have hdeg_rest : (∑ j ∈ Finset.range (k + 1), (C (c j) : K[X]) * v j).degree
      < ((C (c (k+1)) : K[X]) * v (k+1)).degree :=
    degree_lt_degree (by rw [hdeg_top]; omega)
  rw [hsplit, leadingCoeff_add_of_degree_lt hdeg_rest]
  exact hlead_top

/-- **(iv)** The functional equation forces the top normalized coefficient to be `p 0`. -/
theorem ptTop_eq_p_zero (q : K) (g : ℕ) (p : ℕ → K) (hq : q ≠ 0) (H : SelfDualFE q g p) :
    ptTop q g p = p 0 := by
  have h0 := H.fe 0 (Nat.zero_le g)
  simp only [Nat.sub_zero] at h0
  rw [ptTop, h0]
  field_simp

/-- The layer's normalized sequence agrees with `ptTop` at the top index: `s ^ (2g) = q ^ g`. -/
theorem norml_top_eq_ptTop (s q : K) (hs : s ^ 2 = q) (g : ℕ) (p : ℕ → K) :
    norml s p (2 * g) = ptTop q g p := by
  rw [norml, ptTop, ← hs, ← pow_mul, Nat.mul_comm]

/-- **THE LEAD LAW (the general form).** For a coefficient sequence satisfying the self-dual
functional equation, and a certificate whose top expansion coefficient is the top normalized
coefficient, the Galois-normalized certificate `H = h * hᵒ` has leading coefficient `p 0 ^ 2`.

The Galois conjugate `hᵒ` shares `h`'s leading coefficient here because the top normalized
coefficient is `p 0`, which is fixed by the conjugation; the statement is therefore about the
product of two leading coefficients, both equal to `p 0`. -/
theorem lead_law_of_top_coeff (q : K) (g : ℕ) (p : ℕ → K) (hq : q ≠ 0) (H : SelfDualFE q g p)
    (c : ℕ → K) (hcg : c g = ptTop q g p) (hg : 1 ≤ g) (hne : c g ≠ 0) :
    (hOf g c).leadingCoeff * (hOf g c).leadingCoeff = p 0 ^ 2 := by
  rw [leadingCoeff_hOf g c hg hne, hcg, ptTop_eq_p_zero q g p hq H]
  ring

/-- **THE LEAD LAW.** The one-premise form, on the shared field layer.

The only stipulation is Duursma's functional equation. The certificate's coefficients are no
longer required to satisfy an assumed top-coefficient identity: `c` is given by the expansion
relation — the defining relation between the certificate and the zeta polynomial — and the
identification is derived from it.

Note also that no separate `q ≠ 0` hypothesis is needed: it follows from `s ≠ 0`. -/
theorem lead_law (s q : K) (hs : s ^ 2 = q) (hs0 : s ≠ 0) (g : ℕ) (p : ℕ → K)
    (H : SelfDualFE q g p) (c : ℕ → K) (hexp : IsExpansion g c (norml s p))
    (hg : 1 ≤ g) (hp0 : p 0 ≠ 0) :
    (hOf g c).leadingCoeff * (hOf g c).leadingCoeff = p 0 ^ 2 := by
  have hcg : c g = norml s p (2 * g) := top_coeff_of_expansion g hg c _ hexp
  have htop : norml s p (2 * g) = p 0 := norml_top s q hs hs0 g p H
  have hcg0 : c g = p 0 := by rw [hcg, htop]
  have hne : c g ≠ 0 := by rw [hcg0]; exact hp0
  rw [leadingCoeff_hOf g c hg hne, hcg0]
  ring

end LeadLaw
end SIDELvConservation
