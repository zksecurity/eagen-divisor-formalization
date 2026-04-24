/-
  Divisor/Axioms/AxiomHasseWeil.lean

  Hasse-Weil bound on #E(F_q).

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Theorem V.1.1 (Hasse), p. 138. See `axioms/hasse_weil.md` +
  `axioms/snippets/silverman-thm-V.1.1-hasse-155.png`.

  Supplementary: Stichtenoth, *Algebraic Function Fields and Codes*
  (GTM 254, 2nd ed.), Theorem 5.2.3 (Hasse-Weil Bound), p. 198.
-/
import Divisor.Defs

namespace Divisor

variable (E : ECSetup)

/-! ## Hasse-Weil Bound (Hasse 1936, Weil 1948)

|#E(F_q) - (q + 1)| ≤ 2·√q, equivalently (#E - q - 1)² ≤ 4q.

**Integer-squared form.** Stated as `((numPoints - q - 1) : ℤ)² ≤ 4q`
because `2·Nat.sqrt q = 2·⌊√q⌋` is strictly smaller than `⌊2·√q⌋` in
general (e.g. at `q = 7`, `2·⌊√7⌋ = 4` while `⌊2·√7⌋ = 5`). The
squared form is the sharp integer statement and implies both
one-sided bounds when needed.

**Textbook statement (verbatim), Silverman AEC Theorem V.1.1, p.138:**

> "Theorem 1.1. (Hasse) Let E/F_q be an elliptic curve defined over a
> finite field. Then
>     |#E(F_q) − q − 1| ≤ 2√q."

Our `(·)² ≤ 4q` form is equivalent: `|x| ≤ 2√q  ↔  x² ≤ 4q` for `x ∈ ℤ`. -/
axiom hasse_weil :
  ((E.numPoints : ℤ) - E.q - 1)^2 ≤ 4 * E.q

end Divisor
