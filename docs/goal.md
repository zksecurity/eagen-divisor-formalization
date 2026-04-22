# Goal — `chordLogDerivMatchesNormZ`

Prove a term of type `Divisor.chordLogDerivMatchesNormZ E D A₀ A₁` under natural non-degeneracy hypotheses, including a **splitting hypothesis** `normPoly_splits_over_Fq E D` (see §0). All definitions and theorems referenced below are in namespace `Divisor`; file paths are relative to this repository's root.

---

## 0. Prerequisite: splitting hypothesis is required

The statement `chordLogDerivMatchesNormZ E D A₀ A₁` is **false in general**. A concrete counterexample (worked out in a prior run):

- `E : y² = x³ + 1` over `F_7`.
- `D = x² + 1`, i.e. `D.a = X² + 1`, `D.b = 0`.
- `A₀ = (0, 1)`, `A₁ = (1, 3)`, giving `λ = 2`, `μ = 1`, `A₂ = (3, 0)`.
- `logDerivTerm` values: `0` at `(0,1)`, `4` at `(1,3)`, `0` at `(3,0)`; sum = `4`.
- `normPoly = (x² + 1)²` has no roots in `F_7` (`−1` is not a QR mod 7).
- `zerosFinset E D = ∅`, so `normZ E λ D = 1` (constant) and `normZ'(μ) = 0`.
- **LHS** = `(0 + 4 + 0) · 1 = 4` ≠ `0` = **RHS**.

The root cause: `normZ E λ D` only tracks zeros of `D` at F_q-rational points of `E`. When `normPoly E D` does not split over `F_q`, algebraic zeros of `D` living over non-rational x-coordinates contribute to the true function-field norm but are invisible to `normZ`. Under those conditions the target identity genuinely fails.

The fix: add the hypothesis `hSplit : normPoly_splits_over_Fq E D` (defined at `Divisor/BetaConstructive.lean:535`). The splitting predicate asserts `Multiset.card (normPoly E D).roots = (normPoly E D).natDegree`, i.e. every root lives in `F_q`. Under this hypothesis the identity is provable and mathematically correct; the classical Silverman III Prop 3.4 / function-field norm argument goes through.

---

## 1. Target theorem

```lean
theorem chordLogDerivMatchesNormZ_holds
    (E : ECSetup) (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD  : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0) :
    chordLogDerivMatchesNormZ E D A₀ A₁
```

Hypotheses are flexible — additional non-degeneracies (e.g. `hQline`, `hNormZne`, `D.degE + 1 < E.q`) may be added if required. The one hypothesis that must be present is `hSplit`: without it, the target is false (see §0).

**Do not introduce an axiom equivalent to the target.** The content Aristotle is asked to supply is the function-field trace-of-log-derivative identity (or equivalently, the polynomial identity `N(D)(z) = lc(D)^3 · ∏_Q (z − z(Q))^{β_Q}` in `F_q[z]`). A "proof" that takes the scalar identity itself as a hypothesis is not progress — it just renames the obstruction.

---

## 2. Definitions referenced by the target

### 2.1 `ECSetup` — `Divisor/Defs.lean:16`

```lean
structure ECSetup where
  q : ℕ
  hq_prime : Nat.Prime q
  curveA : ZMod q
  curveB : ZMod q
  points : Finset (ZMod q × ZMod q)
  hOnCurve : ∀ p ∈ points, p.2 ^ 2 = p.1 ^ 3 + curveA * p.1 + curveB
  hComplete : ∀ x y : ZMod q, y ^ 2 = x ^ 3 + curveA * x + curveB → (x, y) ∈ points
  numPoints : ℕ
  hNumPoints : numPoints = points.card + 1
  hq_ge : q ≥ 5
```

`ECSetup` bundles the Weierstrass data $y^2 = x^3 + A x + B$ over $\mathbb{F}_q$ together with its full set of affine $\mathbb{F}_q$-rational points.

### 2.2 `CoordRingElt` — `Divisor/Defs.lean:56-64`

```lean
structure CoordRingElt (q : ℕ) [Fact (Nat.Prime q)] where
  a : Polynomial (ZMod q)
  b : Polynomial (ZMod q)

noncomputable def CoordRingElt.degE (D : CoordRingElt q) : ℕ :=
  max (2 * D.a.natDegree) (3 + 2 * D.b.natDegree)

def CoordRingElt.eval (D : CoordRingElt q) (x y : ZMod q) : ZMod q :=
  D.a.eval x - D.b.eval x * y
```

`D = D.a(x) - y · D.b(x)`, an element of the affine coordinate ring $\mathbb{F}_q[x, y] / (y^2 - x^3 - A x - B)$.

### 2.3 Lines and chord coordinate — `Divisor/Defs.lean:38-52` and `Divisor/PolyFibK.lean:40`

```lean
structure Line (q : ℕ) [Fact (Nat.Prime q)] where
  lam : ZMod q
  mu  : ZMod q

def Line.eval (L : Line q) (x y : ZMod q) : ZMod q :=
  y - L.lam * x - L.mu

def slopeOf (x₀ y₀ x₁ y₁ : ZMod q) : ZMod q :=
  (y₁ - y₀) * (x₁ - x₀)⁻¹

def lineThrough (x₀ y₀ x₁ y₁ : ZMod q) : Line q :=
  let s := slopeOf x₀ y₀ x₁ y₁
  { lam := s, mu := y₀ - s * x₀ }

def zLambda (lam : ZMod E.q) (pt : ZMod E.q × ZMod E.q) : ZMod E.q :=
  pt.2 - lam * pt.1
```

### 2.4 `logDerivTerm` — `Divisor/LogDeriv.lean:135-144`

```lean
noncomputable def logDerivTerm
    (D : CoordRingElt E.q) (curveA : ZMod E.q) (lam : ZMod E.q)
    (pt : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let num_x := D.a.derivative.eval pt.1 - D.b.derivative.eval pt.1 * pt.2
  let num_y := -D.b.eval pt.1
  let den := D.eval pt.1 pt.2
  let dxdz_num := 2 * pt.2
  let dydz_num := 3 * pt.1 ^ 2 + curveA
  let dxdz_den := 3 * pt.1 ^ 2 + curveA - 2 * lam * pt.2
  (num_x * dxdz_num + num_y * dydz_num) * (den * dxdz_den)⁻¹
```

This is $(\mathrm{d}D/\mathrm{d}z)(\mathrm{pt}) / D(\mathrm{pt})$, the logarithmic derivative of $D$ in the chord coordinate $z = y - \lambda x$, obtained by chain rule against $2y\,\mathrm{d}y = (3x^2 + A)\,\mathrm{d}x$ on $E$ and $\mathrm{d}z = \mathrm{d}y - \lambda\,\mathrm{d}x$, giving $\mathrm{d}x/\mathrm{d}z = 2y/(3x^2 + A - 2\lambda y)$ and $\mathrm{d}y/\mathrm{d}z = (3x^2 + A)/(3x^2 + A - 2\lambda y)$.

### 2.5 `curveX`, `normPoly`, `zerosFinset`, `betaConstructive`

From `Divisor/CubicIntersection.lean:20`:

```lean
noncomputable def curveX : (ZMod E.q)[X] :=
  X ^ 3 + C E.curveA * X + C E.curveB
```

From `Divisor/BetaConstructive.lean:57-94`:

```lean
noncomputable def normPoly (D : CoordRingElt E.q) : (ZMod E.q)[X] :=
  D.a ^ 2 - D.b ^ 2 * curveX E

theorem normPoly_eval (D : CoordRingElt E.q) (x₀ : ZMod E.q) :
    (normPoly E D).eval x₀ =
      (D.a.eval x₀) ^ 2
        - (D.b.eval x₀) ^ 2 * (x₀ ^ 3 + E.curveA * x₀ + E.curveB)

theorem normPoly_eval_eq_D_mul_D_neg
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    (normPoly E D).eval P.1 = D.eval P.1 P.2 * D.eval P.1 (-P.2)

theorem normPoly_ne_zero (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) : normPoly E D ≠ 0
```

`normPoly` is the 2-sheet ($y \leftrightarrow -y$) Galois norm of $D$ into $\mathbb{F}_q[x]$.

From `Divisor/BetaConstructive.lean:167-176`:

```lean
noncomputable def betaConstructive (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if P ∈ E.points ∧ D.eval P.1 P.2 = 0 then
      if P.2 = 0 ∨ D.eval P.1 (-P.2) ≠ 0 then
        rootMultiplicity P.1 (normPoly E D)
      else
        rootMultiplicity P.1 (normPoly E D) / 2
    else 0
```

`betaConstructive E D P` is the multiplicity of $D$ at $P$: the `rootMultiplicity` of $P.1$ in `normPoly E D` on "lone" sheets, or half of it on "twin" sheets where both $(x, y)$ and $(x, -y)$ are zeros of $D$.

From `Divisor/DivisorPrincipal.lean:295-297`:

```lean
noncomputable abbrev zerosFinset (D : CoordRingElt E.q) :
    Finset (ZMod E.q × ZMod E.q) :=
  (E.points).filter (fun p => D.eval p.1 p.2 = 0)
```

### 2.6 `normZ` — `Divisor/FunctionFieldZ.lean:75-79`

```lean
noncomputable def normZ (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (ZMod E.q)[X] :=
  C ((normPoly E D).leadingCoeff) *
    ∏ Q ∈ zerosFinset E D,
      (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q)
```

`normZ E λ D` is a univariate polynomial in $z$ with leading coefficient $\mathrm{lc}(\mathrm{normPoly}\,D)$, roots at the $z$-projections of the affine $E$-zeros of $D$, multiplicities given by `betaConstructive`.

### 2.7 `chordLogDerivMatchesNormZ` — target proposition, `Divisor/Lemma6.lean:87-98`

```lean
def chordLogDerivMatchesNormZ
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Prop :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  let μ := zLambda E lam A₀
  (logDerivTerm E D E.curveA lam A₀
    + logDerivTerm E D E.curveA lam A₁
    + logDerivTerm E D E.curveA lam
        (lam ^ 2 - A₀.1 - A₁.1,
         lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
    * (normZ E lam D).eval μ
  = eval μ (derivative (normZ E lam D))
```

With $A_2 := (\lambda^2 - x_0 - x_1,\ \lambda(\lambda^2 - x_0 - x_1) + (y_0 - \lambda x_0))$ and $\mu := y_0 - \lambda x_0 = z(A_0)$:

$$\bigl(\mathrm{logDerivTerm}(A_0) + \mathrm{logDerivTerm}(A_1) + \mathrm{logDerivTerm}(A_2)\bigr) \cdot \mathrm{normZ}(\mu) \;=\; (\mathrm{normZ})'(\mu).$$

---

## 3. Already-proved theorems available as lemmas

### 3.1 `logDerivTerm_eq_explicit` — `Divisor/ClearedPolyForm.lean:1854-1863`

```lean
theorem logDerivTerm_eq_explicit
    (D : CoordRingElt E.q) (curveA lam : ZMod E.q)
    (pt : ZMod E.q × ZMod E.q) :
    logDerivTerm E D curveA lam pt =
      ((D.a.derivative.eval pt.1 - D.b.derivative.eval pt.1 * pt.2)
            * (2 * pt.2)
          + (-D.b.eval pt.1) * (3 * pt.1 ^ 2 + curveA))
        * (D.eval pt.1 pt.2 * (3 * pt.1 ^ 2 + curveA - 2 * lam * pt.2))⁻¹
```

### 3.2 `normZ_logDeriv_at_chord_intercept` — `Divisor/NormZDecomp.lean:237-248`

```lean
theorem normZ_logDeriv_at_chord_intercept
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) :
    eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
        (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D)) =
      -((normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
          (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) *
        ∑ Q ∈ zerosFinset E D,
          (betaConstructive E D Q : ZMod E.q) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
```

In symbols: $(\mathrm{normZ})'(\mu) = -\,\mathrm{normZ}(\mu) \cdot \sum_{Q \in \mathrm{zerosFinset}\,E\,D}\, \beta_Q / L_Q(Q)$.

This rewrites the target's RHS and reduces the target to the scalar identity

$$\sum_{i=0}^{2} \mathrm{logDerivTerm}(A_i, \lambda) \;=\; -\sum_{Q \in \mathrm{zerosFinset}\,E\,D} \frac{\beta_Q}{L_Q(Q)}. \qquad (\star)$$

### 3.3 `normPoly_ne_zero` and `normPoly_eval_eq_D_mul_D_neg`

Statements given in §2.5; proofs in `Divisor/BetaConstructive.lean`.

---

## 4. Mathematical content of the identity

$E : y^2 = x^3 + A x + B$ over $\mathbb{F}_q$ (non-singular: $4A^3 + 27B^2 \ne 0$, $\mathrm{char}\,\mathbb{F}_q \notin \{2, 3\}$). $D(x,y) = a(x) - y\,b(x) \in \mathbb{F}_q[E]$ nonzero. $z := y - \lambda x$.

Substituting $y = c + \lambda x$ into $y^2 = x^3 + A x + B$ gives the cubic

$$x^3 - \lambda^2 x^2 + (A - 2 \lambda c)\,x + (B - c^2) = 0, \qquad (\dagger)$$

so the equation $z = c$ cuts out three points $A_0(z), A_1(z), A_2(z)$ on $E$ (generically). Thus $\mathbb{F}_q(E)$ is a degree-3 extension of $\mathbb{F}_q(z)$ with norm
$N := N_{\mathbb{F}_q(E)/\mathbb{F}_q(z)}$.

Because $D \in \mathbb{F}_q[E]$ has only poles at $\infty$, $N(D) \in \mathbb{F}_q[z]$, with roots exactly at $z = z(Q)$ for each affine zero $Q$ of $D$, and multiplicity the divisor multiplicity $\beta_Q$. Hence

$$N(D)(z) \;=\; \mathrm{lc}(D)^3 \cdot \prod_{Q} (z - z(Q))^{\beta_Q} \qquad \in \mathbb{F}_q[z]. \qquad (\ddagger)$$

This RHS is, by construction, equal to $\mathrm{normZ}\,E\,\lambda\,D$ (see §2.6), modulo the scalar $\mathrm{lc}(\mathrm{normPoly}\,D)$.

The trace-of-log-derivative identity in function fields says: for $g \in \mathbb{F}_q(E)^\times$ of $z$-degree $< \mathrm{char}\,\mathbb{F}_q$,

$$\frac{\partial_z N(g)}{N(g)} \;=\; \sum_{i=0}^{2} \left.\frac{\partial_z g}{g}\right|_{A_i(z)}. \qquad (\ast)$$

Applied to $g = D$ and evaluated at $z = \mu = z(A_0)$:

$$\frac{(\mathrm{normZ})'(\mu)}{\mathrm{normZ}(\mu)} \;=\; \sum_{i=0}^{2} \mathrm{logDerivTerm}(A_i, \lambda).$$

Clearing the denominator $\mathrm{normZ}(\mu)$ yields `chordLogDerivMatchesNormZ`.

---

## 5. Algebraic levers on $\mathbb{F}_q$

Under the target hypotheses:

* $A_0, A_1 \in E$: $y_i^2 = x_i^3 + A x_i + B$ for $i = 0, 1$.
* $A_0.1 \ne A_1.1$: $\lambda = (y_1 - y_0)/(x_1 - x_0)$.
* $A_2 = (x_2, y_2)$ with $x_2 = \lambda^2 - x_0 - x_1$, $y_2 = \lambda x_2 + (y_0 - \lambda x_0)$; $A_2 \in E$ follows from the chord construction.
* $\{x_0, x_1, x_2\}$ are the three roots of the monic cubic $x^3 - \lambda^2 x^2 + (A - 2 \lambda \mu) x + (B - \mu^2)$ from $(\dagger)$ at $c = \mu$. Elementary symmetric polynomials:
   $$e_1 = x_0 + x_1 + x_2 = \lambda^2, \qquad
     e_2 = x_0 x_1 + x_0 x_2 + x_1 x_2 = A - 2 \lambda \mu, \qquad
     e_3 = x_0 x_1 x_2 = \mu^2 - B.$$
* $L_Q(P) = P.\mathrm{y} - \lambda\,P.\mathrm{x} - \mu = z(P) - \mu$. In particular $L_Q(A_i) = 0$ for $i \in \{0, 1, 2\}$; this is not a problem for $(\star)$'s RHS because $A_i \notin \mathrm{zerosFinset}\,E\,D$ (hypothesis `hA_i def`).

Clearing denominators, $(\star)$ is a polynomial identity in
$\mathbb{Z}[A, B, x_0, y_0, x_1, y_1, x_2, y_2, \{x_Q, y_Q, \beta_Q\}_Q]$
modulo the curve equations at each point, the cubic-symmetry relations above, and the chord/slope relation $(x_1 - x_0)\lambda = y_1 - y_0$.

---

## 6. Alternative route via the polynomial norm $(\ddagger)$

Prove $(\ddagger)$ directly as an equality of polynomials in $\mathbb{F}_q[z]$:

1. Realize $D = a(x) - (z + \lambda x) b(x) \in \mathbb{F}_q(z)[x]$ of $x$-degree $\le \max(\deg a,\ 1 + \deg b)$.
2. Compute $N(D) = \mathrm{Res}_x\bigl(D,\ x^3 - \lambda^2 x^2 + (A - 2\lambda z) x + (B - z^2)\bigr)$ as a $3 \times 3$ Sylvester determinant.
3. Match roots and multiplicities of the resultant against $\mathrm{lc}(D)^3 \prod_Q (z - z(Q))^{\beta_Q}$.

Differentiating and evaluating at $z = \mu$ recovers the target.
