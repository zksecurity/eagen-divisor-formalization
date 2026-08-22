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

- [x] **1a Uniformizers.** Landed in `Divisor/OrdP/ValuationBridge.lean`
      as valuation statements (no localization detour needed):
      `pointPrime_intValuation_XClass_of_ne_zero` (`v_P(X−x₀) = exp(−1)`
      via mathlib's `XYIdeal_neg_mul`: `⟨X−x₀⟩ = σP·P` with `σP ≠ P` by
      vendored `XYIdeal_eq_iff` and char ≠ 2),
      `pointPrime_intValuation_XClass_of_eq_zero` (`exp(−2)`, same
      identity with `σP = P`), and
      `pointPrime_intValuation_yClassZero` (`v_P(y) = exp(−1)` at
      2-torsion, from `y² = f(x)` and `rootMult x₀ f = 1` by
      nonsingularity). Membership ↔ vanishing: `mem_pointPrime_iff`.
- [x] **1b DVR facts** (mathlib): all present at v4.33 —
      `Valuation.map_add_of_distinct_val`, `map_mul`,
      `intValuation_le_pow_iff_dvd` / `intValuation_eq_one_iff`, plus
      the `emultiplicity` squeeze pair
      (`intValuation_le_exp_iff_le_emultiplicity` and its converse)
      packaged as `intValuation_eq_exp_neg_of_emultiplicity`.
- [x] **1c Conjugation.** Done *elementwise* instead of via the
      vendored ideal-map: `CoordRingElt.conjElt D = (a, −b)` with
      `conjElt_eval : σD(x,y) = D(x,−y)`, and the norm identity
      `toCoordinateRing_mul_conjElt : D·σD = mk (C (normPoly E D))`
      proved directly from `Y² = f(X)` (no vendored `conj`/`mul_conj`
      needed). Derived: univariate `pointPrime_intValuation_mk_C`
      (`v_P(g) = exp(−e_P·rootMult x₀ g)`, both torsion cases) and the
      lone-case `pointPrime_intValuation_of_lone`.
- [ ] **1d Bridge theorems.**
      * [x] `ordAt_eq_count` (over `ZMod E.q`): landed in
        `Divisor/OrdP/ValuationBridgeOrd.lean` as
        `pointPrime_intValuation_toCoordinateRing`
        (`v_P(D) = exp(−ordAt E D P)`), with
        `multiplicity_pointPrime_eq_ordAt` and
        `count_pointPrime_eq_ordAt` (the `Associates.count` form that
        `finprod_heightOneSpectrum_factorization` consumes). Induction
        exactly as planned: twin case via
        `toCoordinateRing_divLin_of_twin` + degree-drop fuel bound,
        lone case via 1c, 2-torsion closed form
        `pointPrime_intValuation_twoTorsion` via parity/min.
      * [ ] `geomLocalOrder_eq_count` (over `Fqbar E`, base-changed
        curve): same recipe against the closed formula in
        `Divisor/GeomLocalOrder.lean` (`commonRootMultiplicity` split,
        residual sheet gets `m − k`, conjugate sheet gets `k`).
      Cross-checks: the proved identities
      `sum_ordAt_eq_natDegree_under_split` and
      `geomLocalOrder_fiber_accounting` must be derivable from the
      bridge — use them as sanity tests, not inputs.
      *Note (scope check, 2026-08-22): Phase 2 as written consumes only
      the `ZMod` bridge; the `Fqbar` half is needed for Phase 3's
      geometric side. Phase 2 can start now.*

## Phase 2 — Discharge `divisorClass_eq_zero_of_b_ne_zero`

Ships on its own (does not wait for Phase 3).

- [x] **2a Support classification.** Landed as
      `eq_pointPrime_of_mem` in
      `Divisor/OrdP/SupportClassification.lean`. *As-built deviation:
      the residue-degree/`finrank_quotient_eq_one_iff` step turned out
      to be unnecessary — after `X − α ∈ v` (contraction is `(π)` in
      the PID `F_q[X]`, `π ∣ N(D)` via the norm identity, `π` linear
      since `N(D)` splits) and `(y − y₀)(y + y₀) ≡ y² − f(α) ≡ 0 mod v`
      with `v` prime, one of `⟨X − α, Y ∓ y₀⟩ ≤ v` holds with the left
      side maximal (vendored `XYIdeal_isMaximal_of_equation`), so they
      are EQUAL. No finrank computation at all.*
- [x] **2b Factorization.** Landed as
      `span_toCoordinateRing_eq_prod`: exactly as planned via
      `finprod_heightOneSpectrum_factorization` + `maxPowDividing`
      unfold + `count_pointPrime_eq_ordAt` (Phase 1) + 2a for support.
- [x] **2c Class collapse.** Landed in `Divisor/OrdP/LocalRing.lean`:
      `divisorClass_divisorOfD_eq_sum` (infinity killed by
      `toClass_zero`, reindex along `affine`),
      `prod_xyIdealOfPoint_pow_eq_principalFracIdeal` (Units.ext +
      `coeIdealHom`/`coeIdeal_span_singleton`/`coe_toPrincipalIdeal`),
      then `toMul_sum`/`toMul_zsmul`/`map_prod` and the existing
      `classGroup_mk_principalFracIdeal_eq_one`.
- [x] Replace the `axiom` in `Divisor/OrdP/LocalRing.lean` by the
      theorem — done, same name and signature; as predicted the
      `b ≠ 0` hypothesis is unused (kept as `_hbNZ` for signature
      stability; the fact is noted in the docstring).
- [x] Update both pin files in the same commit — done;
      `ma/ip_extractable*` closures are now
      `{propext, Classical.choice, chord_fiber…, hasse_weil_textbook,
      Quot.sound}`, and `exists_divisor_multiplicity*` /
      `ordAt_group_sum_zero_under_split` are down to the core three.
      Verified by `#guard_msgs` in a full green build.

## Phase 3 — Discharge `chord_fiber_product_concrete_bar_zfiber_pow_dvd`

Entirely over `F̄ := Fqbar E` with the base-changed curve; write
`W̄ := (E.toW.map (algebraMap F_q F̄))`, `R̄ := CoordinateRing(W̄)` and
`z := class of (Y − λX)`.

*Design refinement (2026-08-22, after Phase 2 landed).* The route
below is confirmed viable against mathlib v4.33's actual API
(`Resultant/Basic.lean` has `resultant_eq_prod_eval`,
`resultant_map_map`, `resultant_mul_right`,
`exists_mul_add_mul_eq_C_resultant` — but **no** norm↔resultant
lemma, so 3c is proved via embeddings over `K := F̄(Z)`). Two key
simplifications found:
* In chord coordinates `ȳ = λ̄x̄ + z̄` with `z̄ ∈ K`, so the function
  field is **monogenic** over the z-line: `L = K(x̄)`, minpoly = the
  chord cubic. Norm-as-product-over-embeddings applies directly
  (degree 3 < char q, so separable with no discriminant computation
  — the `−27Z⁴` analysis is NOT needed).
* The 3b membership `D̄ ∈ ∏ m_Q^{k_Q}` needs the F̄-side valuation
  machinery only at ramified points; but since the same uniformizer
  toolkit gives all cases uniformly, P3.pre replays
  `ValuationBridge` over `W̄` keyed on curve equations instead of
  `E.points` membership.

- [ ] **P3.pre (Phase 1's `Fqbar` half, reduced to what 3b uses).**
      Over `W̄`: `IsElliptic` (mathlib's `(W.map f).IsElliptic`
      instance), `IsDedekindDomain R̄` (vendored), point primes
      `m_Q` at geometric points, uniformizer valuations, univariate
      valuations, conj/norm identity, and the closed-form
      `v_Q(D̄) = exp(−geomLocalOrder E D Q)` (no fuel induction: the
      closed formula of `Divisor/GeomLocalOrder.lean` is matched
      case-by-case — ramified = parity min; unramified = peel the
      common factor `(x̄−x₀)^k` then lone-case on the residual).
- [ ] **3a `F̄[Z]`-structure.** Algebra map `F̄[Z] → R̄`, `Z ↦ z`;
      `Module.Finite` with generators `{1, x, x²}` (`y = λx + z`; `x`
      integral via the monic chord cubic
      `f(X, Z) = X³ − λ²X² + (A − 2λZ)X + (B − Z²)`, and
      `f(x, z) = 0` in `R̄` is exactly the curve equation).
      If freeness/minpoly bookkeeping is needed, the cleanest route is
      the explicit iso `R̄ ≅ AdjoinRoot (f̄ : F̄[Z][X])` (both
      directions are `AdjoinRoot.lift`s with `ring`-checkable
      relation images).
- [ ] **3b Lower bound by relNorm calculus** (the clean core):
      P3.pre gives `D̄ ∈ ∏_{Q : π(Q)=z₀} m_Q^{gd.mult Q}`
      (`intValuation_le_pow_iff_mem`; distinct maximal ideals make
      the product an intersection); then
      `span {intNorm D̄} = relNorm (span D̄)` (`relNorm_singleton`)
      `≤ ∏ relNorm(m_Q)^{mult}` (`relNorm` multiplicativity)
      `≤ ∏ (Z − z₀)^{mult}` (`relNorm_le_comap` +
      `m_Q ∩ F̄[Z] = (Z − z₀)`, immediate from
      `z̄ − z₀ = (ȳ − y₀) − λ̄(x̄ − x₀) ∈ m_Q` + maximality), i.e.
      **`(Z − z₀)^{Σ mult} ∣ Algebra.intNorm F̄[Z] R̄ D̄`**.
- [ ] **3c Norm = resultant, via embeddings** (long pole #2):
      `intNorm D̄ = (chord_fiber_product_concrete E lam D).map (…)`
      exactly (no sign: the chord cubic is monic). Chain, with
      `K = F̄(Z)`, `L = Frac R̄ = K(x̄)`:
      `P̄ ↦ K` (`resultant_map_map`), over `K̄`:
      `= ∏_{roots ξ of f̄} ḡ(ξ)` (`resultant_eq_prod_eval`)
      `= ∏_{σ : L →ₐ[K] K̄} σ(D̄)` (roots ↔ embeddings for the
      primitive element; distinct roots by separability, deg 3 < q)
      `= Norm_{L/K}(D̄)` (`Algebra.norm_eq_prod_embeddings`)
      `= algebraMap K (intNorm F̄[Z] R̄ D̄)` (`algebraMap_intNorm`).
      Fallback if the equality fights us: one-way divisibility
      `intNorm ∣ P̄` suffices for 3d.
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
* 2026-08-22 — **Phase 1, `ZMod` side complete** (1a, 1b, 1c, and the
  `ordAt_eq_count` half of 1d). New modules
  `Divisor/OrdP/ValuationBridge.lean` (uniformizer valuations of
  `X − x₀` and `y`, univariate valuations, elementwise conjugate
  `conjElt` + norm identity, lone-case and 2-torsion closed forms) and
  `Divisor/OrdP/ValuationBridgeOrd.lean` (twin-case `divLin`
  exactness, the fuel induction, and the headline
  `pointPrime_intValuation_toCoordinateRing : v_P(D) = exp(−ordAt E D P)`
  with `multiplicity`/`Associates.count` corollaries). Notable
  deviation from plan: 1c uses a direct elementwise conjugate and a
  2-line `AdjoinRoot` computation for `D·σD = N(D)` instead of the
  vendored `conj`/`mul_conj` — simpler, and keeps the vendored
  surface consumed by proofs smaller. Full build green; pins
  untouched (no axiom changed yet). Remaining in Phase 1: the `Fqbar`
  half (`geomLocalOrder_eq_count`), needed by Phase 3 but not by
  Phase 2 — so Phase 2 is unblocked now.
* 2026-08-22 — **Phase 2 complete: `divisorClass_eq_zero_of_b_ne_zero`
  is DISCHARGED.** The axiom in `Divisor/OrdP/LocalRing.lean` is now a
  theorem (same name/signature). New module
  `Divisor/OrdP/SupportClassification.lean` (2a `eq_pointPrime_of_mem`
  — simpler than planned: no residue-degree computation, just
  maximal-ideal containment; 2b `span_toCoordinateRing_eq_prod`).
  Class collapse 2c assembled in `LocalRing.lean`. Both pin files
  updated in the same commit; full `lake build Divisor Tests` green
  with `#guard_msgs` certifying the new closures:
  `ma/ip_extractable*` now depend on exactly
  `{chord_fiber_product_concrete_bar_zfiber_pow_dvd,
  hasse_weil_textbook}` beyond the Lean builtins, and
  `exists_divisor_multiplicity*` / `ordAt_group_sum_zero_under_split`
  are axiom-free. **Two project axioms remain: Hasse (stays) and the
  chord-fiber bound (Phase 3).**
