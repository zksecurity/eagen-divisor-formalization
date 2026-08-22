# Plan: discharge the two divisor axioms

Goal: turn the two divisor-theoretic axioms into theorems, leaving the
Hasse bound as the project's **only** axiom.

| Axiom | Today | End state |
|---|---|---|
| `Divisor.hasse_weil_textbook` | axiom | axiom (unchanged; no Hasse bound exists in mathlib or Tau Ceti) |
| `Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero` | axiom | theorem (Phase 2) |
| `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd` | axiom | theorem (Phase 3) |

Final closures (enforced by the `#guard_msgs` pins in
`Tests/AxiomClosurePin.lean` / `Tests/F5RegressionAxiomClosure.lean`):

* `ma_extractable`, `ip_extractable`, `ma_completeness`:
  `propext, Classical.choice, Quot.sound, Divisor.hasse_weil_textbook`
* `ma_completeness_base` and the whole binary completeness chain:
  core three only (fully axiom-free).

## Decision: vendor Tau Ceti (not depend)

Tau Ceti (`TauCetiProject/TauCeti`, Apache-2.0) has the elliptic-curve
Dedekind/ideal infrastructure we need, but it has no release tags, runs
on Lean `v4.34.0-rc1`, pins mathlib at a *master* commit, and uses the
`module` / `public import` system throughout. A live lake dependency
would force our toolchain onto that moving target.

Instead we vendor a closed set of **7 files (~1,300 lines)** into
`Divisor/Vendor/TauCeti/`, adapted to our pin (Lean/mathlib v4.33.1):

| Vendored file (original path under `TauCeti/`) | Lines | What we use |
|---|---|---|
| `FieldTheory/SeparableDegree.lean` | 58 | helper |
| `FieldTheory/IntermediateField/FieldRange.lean` | 100 | helper |
| `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Finrank.lean` | 222 | `finrank_functionField` (F(W) is quadratic over F(x)) |
| `AlgebraicGeometry/EllipticCurve/Affine/Eval.lean` | 102 | evaluation helpers |
| `AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean` | 485 | `conj`, `mul_conj`, `isIntegrallyClosed_coordinateRing`, **`isDedekindDomain_coordinateRing`** |
| `AlgebraicGeometry/EllipticCurve/Affine/XYIdealMaximal.lean` | 260 | `XYIdeal_isMaximal`, `XYIdeal_ne_bot`, `XYIdeal_eq_iff`, **`finrank_quotient_eq_one_iff`** |
| `AlgebraicGeometry/EllipticCurve/Affine/LocalRing.lean` | 83 | DVR at point ideals |

Provenance to record in each vendored header: repo
`https://github.com/TauCetiProject/TauCeti`, commit
`076ae23499c00fc000838bec23b0082649b838a4` (2026-08-21), Apache-2.0,
original copyright lines kept. Adaptation: strip `module` /
`public import` / `@[expose] public section` to plain
`import` / `section`; fix v4.34→v4.33 API drift as needed.

Everything else runs on mathlib **already at our pin (v4.33)** —
verified present:

* `Ideal.finprod_heightOneSpectrum_factorization` (`I = ∏ᶠ v, v.maxPowDividing I`)
* `Ideal.relNorm_singleton` (`relNorm R (span {r}) = span {Algebra.intNorm R S r}`)
* `Ideal.spanNorm_mul` (multiplicative over Dedekind), `Ideal.relNorm_le_comap`
* `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd`,
  `intValuation_lt_one_iff_dvd`
* `WeierstrassCurve.Affine.Point.toClass_some`, `XYIdeal'_eq`,
  `ClassGroup.mk_eq_one_of_coe_ideal`, `FractionalIdeal.coeIdeal_mul/pow`
* `Polynomial.resultant_eq_prod_eval`, `resultant_map_map`
* `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`

Deliberately **not** used from Tau Ceti: the `WeilDivisor`/`OrderSystem`
layer, the `AffineModel`/`Place` layer, and `pointPlace` packaging —
mathlib's `HeightOneSpectrum` plus the 7 files above suffice.

## Phase 0 — Vendor spike (gate)

- [x] Copy the 7 files to `Divisor/Vendor/TauCeti/…`, strip module
      syntax, keep license headers, add a provenance note per file and a
      `Divisor/Vendor/TauCeti/README.md`.
- [x] Compile at v4.33.1; fix v4.34/master API drift (expected: the same
      class of renames we just crossed in the v4.28→v4.33 bump, in
      reverse and smaller). *Outcome: zero drift — all 7 files compiled
      unmodified beyond the mechanical module-syntax strip; upstream's
      v4.34.0-rc1/master API for everything these files touch is
      identical at v4.33.1.*
- [x] Bridge file `Divisor/OrdP/DedekindSetup.lean`:
      instance `E.toW.IsElliptic` from `hDisc` (we already prove
      `E.toW_Δ_ne_zero`; over a field `Δ ≠ 0 ↔ IsUnit Δ`), then
      `IsDedekindDomain E.toW.toAffine.CoordinateRing`,
      `(XYIdeal … ).IsMaximal` / `≠ ⊥` at every `P ∈ E.points`, and the
      height-one prime `pointPrime E P hP :
      HeightOneSpectrum E.toW.toAffine.CoordinateRing`. *Also landed:
      `pointPrime_asIdeal` (`rfl` simp lemma), `pointPrime_isMaximal`,
      and `pointPrime_injective` (distinct points → distinct primes, via
      vendored `XYIdeal_eq_iff`). Note `HeightOneSpectrum` at v4.33 is
      `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`.*
- **Exit criterion**: `lake build` green with those instances usable
  from a `Divisor.*` file.
- Fallback if adaptation fights us: re-derive `isDedekindDomain` with
  Tau Ceti's (documented, characteristic-uniform) proof as the guide.

## Phase 1 — Valuation bridge (shared core; long pole #1)

New module(s) `Divisor/OrdP/ValuationBridge*.lean`, generic over the
base field where cheap (we only need our short-Weierstrass shape,
`a₁ = a₂ = a₃ = 0`; don't over-generalize).

- [ ] **1a Uniformizers.** At `P = (x₀, y₀)` on the curve:
      `y₀ ≠ 0` ⇒ the maximal ideal of the localization at
      `XYIdeal x₀ (C y₀)` is generated by the class of `X − x₀`
      (`intValuation (x − x₀) = 1`); `y₀ = 0` ⇒ generated by the class
      of `Y`, with `intValuation (x − x₀) = 2`. Inputs: vendored DVR
      instance; the membership characterization already in the repo
      (`toCoordinateRing_mem_XYIdeal_iff`).
- [ ] **1b DVR facts** (mathlib): valuation of a sum with distinct
      valuations is the min; multiplicativity;
      `intValuation_le_pow_iff_dvd` as the membership interface.
- [ ] **1c Conjugation.** `conj` (vendored) maps
      `XYIdeal x (C y)` to `XYIdeal x (C (−y))`; hence
      `v_{σP}(D) = v_P(conj D)`. With `mul_conj`
      (`D * conj D` = the norm, and
      `norm_toCoordinateRing_eq_normPoly` already in
      `Divisor/CoordinateRingBridge.lean`) derive:
      * univariate input: `v_P (g(x)) = rootMultiplicity x₀ g` at
        non-2-torsion `P` (factor `g = (X−x₀)^m · h`, `h(x₀) ≠ 0` ⇒ `h`
        a unit at `P`);
      * **lone-case identity**:
        `v_P(D) + v_{σP}(D) = rootMultiplicity x₀ (normPoly E D)`.
- [ ] **1d Bridge theorems.**
      * `ordAt_eq_count` (over `ZMod E.q`): for `P ∈ E.points`,
        `ordAt E D P` equals the multiplicity of `pointPrime E P` in
        `span {D.toCoordinateRing E}`. Induction mirroring the fuel
        recursion in `Divisor/OrdP/Uniformizer.lean`: twin case via
        `divLin` exactness + 1a; lone case via 1c; 2-torsion closed form
        via the parity/min argument (1a + 1b).
      * `geomLocalOrder_eq_count` (over `Fqbar E`, base-changed curve):
        same recipe against the closed formula in
        `Divisor/GeomLocalOrder.lean` (`commonRootMultiplicity` split,
        residual sheet gets `m − k`, conjugate sheet gets `k`).
      Cross-checks: the proved identities
      `sum_ordAt_eq_natDegree_under_split` and
      `geomLocalOrder_fiber_accounting` must be derivable from the
      bridge — use them as sanity tests, not inputs.

## Phase 2 — Discharge `divisorClass_eq_zero_of_b_ne_zero`

Ships on its own (does not wait for Phase 3).

- [ ] **2a Support classification.** Under `splitsOnE E D`, every
      height-one prime `v` with `D.toCoordinateRing ∈ v.asIdeal` is
      `pointPrime E P` for some `P ∈ E.points` with `D.eval P = 0`:
      * `v ∩ F_q[X] = (X − α)` and `normPoly E D (α) = 0` (via
        `mul_conj`: `N(D) ∈ v ∩ F_q[X]`), so `α` is rational by the
        splitting half of `splitsOnE`;
      * the fiber quadratic `Y² − f(α)` has a rational root by the
        fiber-rationality half, so `CoordinateRing ⧸ v` has rank 1 over
        `F_q`; conclude with vendored `finrank_quotient_eq_one_iff`.
- [ ] **2b Factorization.**
      `span {D.toCoordinateRing} = ∏_{P ∈ E.points} (XYIdeal P)^{ordAt E D P}`
      via `finprod_heightOneSpectrum_factorization` + 1d (counts at
      point primes) + 2a (count 0 elsewhere).
- [ ] **2c Class collapse.** `divisorClass E (divisorOfD E D) _`
      `= mk (∏ (xyIdealOfPoint P)^{ordAt P})` (mathlib `toClass_some`,
      `XYIdeal'_eq`, `coeIdeal_mul/pow`; infinity killed by
      `toClass 0 = 0`) `= mk (principalFracIdeal D)` (2b)
      `= 1` (existing `classGroup_mk_principalFracIdeal_eq_one`).
- [ ] Replace the `axiom` in `Divisor/OrdP/LocalRing.lean` by the
      theorem (same name/signature; the `b ≠ 0` hypothesis likely
      becomes unnecessary — keep the signature, note the fact).
- [ ] Update both pin files in the same commit:
      `ma/ip_extractable*` closures shrink to
      `{chord_fiber…, hasse_weil_textbook}`;
      `exists_divisor_multiplicity*` / `ordAt_group_sum_zero_under_split`
      shrink to core three.

## Phase 3 — Discharge `chord_fiber_product_concrete_bar_zfiber_pow_dvd`

Entirely over `F̄ := Fqbar E` with the base-changed curve; write
`R̄ := CoordinateRing(W̄)` and `z := class of (Y − λX)`.

- [ ] **3a `F̄[Z]`-structure.** Algebra map `F̄[Z] → R̄`, `Z ↦ z`;
      `Module.Finite` with generators `{1, x, x²}` (`y = λx + z`; `x`
      integral via the monic chord cubic
      `f(X, Z) = X³ − λ²X² + (A − 2λZ)X + (B − Z²)`, and
      `f(x, z) = 0` in `R̄` is exactly the curve equation).
- [ ] **3b Lower bound by relNorm calculus** (the clean core):
      1d gives `D̄ ∈ ∏_{Q : π(Q)=z₀} m_Q^{gd.mult Q}`
      (`intValuation_le_pow_iff_dvd`); then
      `span {N(D̄)} = relNorm (span D̄)`(`relNorm_singleton`)
      `≤ ∏ relNorm(m_Q)^{mult}` (`spanNorm_mul`)
      `≤ ∏ (Z − z₀)^{mult}` (`relNorm_le_comap` +
      `m_Q ∩ F̄[Z] = (Z − z₀)`), i.e.
      **`(Z − z₀)^{Σ mult} ∣ Algebra.intNorm F̄[Z] R̄ D̄`**.
- [ ] **3c Norm = resultant** (long pole #2):
      `intNorm D̄ = ± (chord_fiber_product_concrete E lam D).map (algebraMap …)`.
      The chord cubic is monic and **separable** over `F̄(Z)`: its
      X-discriminant, as a polynomial in `Z`, has leading term `−27·Z⁴`
      (nonzero since `q ≥ 5`). Over a splitting field both sides are
      `∏ᵢ D(xᵢ)`: resultant side via `resultant_eq_prod_eval` +
      `resultant_map_map`; norm side via `Algebra.norm` base-change /
      product-over-roots. Fallback if the equality fights us: two
      one-way divisibilities, combined with the already-proved degree
      bound (`chord_fiber_product_concrete_natDegree_le_normPoly_natDegree`).
- [ ] **3d Assembly** to the axiom's exact statement in
      `Divisor/Axioms/AxiomChordFiberDivisibility.lean` (`gd.mult` is
      pinned to `geomLocalOrder` by `mult_eq_geomLocalOrder`, so fiber
      sums line up definitionally; the `[DecidableEq (Fqbar E)]`
      argument is inert). Replace axiom by theorem; update pins:
      `ma_completeness*` closures drop the chord axiom.

## Phase 4 — Surface cleanup

- [ ] README "Axiom Surface" rewritten: one axiom, Hasse.
- [ ] Final pin update; confirm the binary completeness chain closes
      over core three only.
- [ ] Delete `Divisor/Sketch/ChordFiberProductConcrete.lean`'s sorry'd
      duplicates (now fully superseded) and the axiom files that became
      empty shells.
- [ ] Vendored-code note in the top-level README (provenance, license).

## Ordering and discipline

`P0 → P1 → P2 (land + pins) → P3 → P4`. P2 is independent of P3 and
lands first. Every landing keeps `lake build Divisor Tests` green; every
axiom deletion updates the `#guard_msgs` pins **in the same commit**
(the pins fail loudly otherwise — that is what they are for). No
`maxHeartbeats` raises to paper over slow proofs; rewrite them.

## Risk register

| Risk | Where | Mitigation |
|---|---|---|
| v4.34/master API drift in vendored files | P0 | Small, known class of renames; worst case re-derive Dedekind-ness following their documented proof |
| Uniformizer lemmas harder than expected | 1a | They are the standard Silverman II §1 facts; the DVR instance plus `XYIdeal` membership API keeps them local computations |
| Lone-case norm identity | 1c/1d | Same argument the `ordAt` docstrings already sketch; now stateable in a DVR. `mul_conj` + `norm_toCoordinateRing_eq_normPoly` do the heavy lifting |
| `relNorm` of a point prime not exactly `(Z − z₀)` | 3b | Only `≤` is needed for the lower bound; `relNorm_le_comap` gives it |
| Norm-vs-resultant identity | 3c | Fallback: one-way divisibilities + existing degree bound (the squeeze consumer only needs the lower-bound half anyway) |
| Separability edge cases | 3c | `−27 Z⁴` leading-term computation; `q ≥ 5` kills char 2/3 |

## Status log

* 2026-08-22 — Plan written. Prior work on this branch: axiom audit,
  `#guard_msgs` pin enforcement (CI now builds `Tests`), trusted-surface
  cleanup, toolchain/mathlib bump to v4.33.1 with closures verified
  unchanged.
* 2026-08-22 — **Phase 0 complete.** All 7 Tau Ceti files vendored under
  `Divisor/Vendor/TauCeti/` (commit `076ae234`, provenance headers +
  README) and compile at v4.33.1 with **zero** API drift — the expected
  reverse-migration never materialized. Bridge
  `Divisor/OrdP/DedekindSetup.lean` landed: `ECSetup.instIsElliptic`,
  `IsDedekindDomain E.toW.toAffine.CoordinateRing`,
  `ECSetup.pointPrime` (+ `_asIdeal`, `_isMaximal`, `_injective`);
  wired into `Divisor.lean`, full `lake build Divisor Tests` green,
  axiom pins untouched. The Phase 0 fallback path (re-derive
  `isDedekindDomain` by hand) is dead — not needed.
