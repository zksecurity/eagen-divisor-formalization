/-
  Divisor/Hasse.lean — terminal Hasse layer.

  The ONLY file in the library that imports the Hasse–Weil axiom
  (`Divisor.Axioms.AxiomHasseWeil`). Everything below this module is
  axiom-free and stated in the point-count currency
  `n = E.points.card`; this leaf bounds `n` as a function of the
  field size `q` — in both directions — exactly once, and derives
  the field-size (`_hasse`) corollaries of the extractability
  headlines.

  Currency conversions live here because only the *lower* bound on
  `n` (`q ≤ 2n + 3`) needs Hasse–Weil; the upper direction
  (`n ≤ 2q`) is the trivial fiber count `points_card_le_two_q`,
  which stays in the axiom-free core. Completeness needs no axiom at
  all: its field-size forms (`ma_completeness_q`, `ip_completeness_q`)
  therefore live in `Divisor/Soundness.lean`, not here.

  Each field-size statement comes in two flavors:

  * `_of_count` — takes the linear point-count bounds
    (`hUB : 2n ≤ 3q + 3` and/or `hLB : q ≤ 2n + 3`) as explicit
    hypotheses. For a concrete curve these are checkable arithmetic
    facts about the point count, so the `_of_count` forms are
    axiom-free end-to-end.
  * `_hasse` — discharges those hypotheses via the project's single
    axiom `hasse_weil_textbook` (through `hasse_points_bound` /
    `hasse_points_bound_lb` below).

  Contents:
  * `hasse_points_bound`      : `2n ≤ 3q + 3`  (upper, axiom-priced)
  * `hasse_points_bound_lb`   : `q ≤ 2n + 3`   (lower, axiom-priced)
  * `points_card_threshold_of_count`, `validPairs_sample_bound_of_count`
    — discharge the core `hLargeQ` / `hSample` hypotheses from the
    single field-size threshold `72·(a + 4) ≤ q` (`a = degE + k`).
  * `validPairs_card_ge_q(_of_count)` : `(q−3)·(q−9) ≤ 4·|validPairs|`
  * `ma_soundness_count_bound_of_count` / `ma_soundness_count_bound_hasse`,
    `ip_extractable_of_count` / `ip_extractable_hasse`,
    `ma_soundness_ratio_bound_of_count` /
    `ma_soundness_ratio_bound_hasse`,
    `ma_soundness_base_hasse`, `ip_extractable_base_hasse`,
    `ma_soundness_of_excess_hasse`,
    `ip_extractable_witness_of_excess_hasse` —
    field-size forms of the extractability headlines.
-/
import Divisor.Headlines
import Divisor.Axioms.AxiomHasseWeil

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Point-count vs field-size: the two Hasse-priced conversions -/

/-- From Hasse–Weil: `2 · |E.points| ≤ 3q + 3` (sharper than the
trivial fiber bound `n ≤ 2q` — needed to recover the paper constant
`36·(d+k+4)·q` below). -/
theorem hasse_points_bound : 2 * E.points.card ≤ 3 * E.q + 3 := by
  have hw : ((E.numPoints : ℤ) - E.q - 1) ^ 2 ≤ 4 * E.q := hasse_weil E
  have hnum := E.hNumPoints
  have hqge := E.hq_ge
  set m := (E.numPoints : ℤ) - E.q - 1 with hm_def
  have hm_sq : m ^ 2 ≤ 4 * (E.q : ℤ) := hw
  have h2m : 2 * m ≤ (E.q : ℤ) + 3 :=
    BivariateZerosOnExE.hasse_int_bound E.q m hqge hm_sq
  omega

/-- From Hasse–Weil: `q ≤ 2 · |E.points| + 3`. The lower-side dual of
`hasse_points_bound` — the direction no fiber count can give. Apply
`hasse_int_bound` to `m = q + 1 − numPoints`. -/
theorem hasse_points_bound_lb : E.q ≤ 2 * E.points.card + 3 := by
  have hw : ((E.numPoints : ℤ) - E.q - 1) ^ 2 ≤ 4 * E.q := hasse_weil E
  have hnum := E.hNumPoints
  have hqge := E.hq_ge
  -- Use m' = q + 1 - numPoints (so m'² = (numPoints - q - 1)² ≤ 4q).
  set m' := (E.q : ℤ) + 1 - E.numPoints with hm'_def
  have hm'_sq : m' ^ 2 ≤ 4 * (E.q : ℤ) := by
    have h := hw
    -- (numPoints - q - 1)² = (q + 1 - numPoints)² = m'²
    have : ((E.numPoints : ℤ) - E.q - 1) ^ 2 = m' ^ 2 := by ring
    linarith [this ▸ h]
  have h2m' : 2 * m' ≤ (E.q : ℤ) + 3 :=
    BivariateZerosOnExE.hasse_int_bound E.q m' hqge hm'_sq
  omega

/-! ## Discharging the core hypotheses from one field-size threshold

The axiom-free headlines (`ma_soundness_count_bound` and friends) carry two
point-count hypotheses: the SZ-on-(E×E) density threshold `hLargeQ`
(`n > 31a + 140` for `a = degE + k`) and the Frobenius slope-sampling
pigeonhole `hSample` (`18·(a+1)·q + 1 ≤ |validPairs|`). Both follow
from the single field-size threshold `72·(a + 4) ≤ q` given the lower
bound `q ≤ 2n + 3`. -/

/-- `q ≤ 2n + 3` and `72·(a + 4) ≤ q` force `n > 31·a + 140` — the
core `hLargeQ` density threshold, in exactly the shape the headlines
expect (with `a := msg.toD.degE + stmt.k`). Axiom-free. -/
theorem points_card_threshold_of_count
    (hLB : E.q ≤ 2 * E.points.card + 3)
    (a : ℕ) (hQbig : 72 * (a + 4) ≤ E.q) :
    E.points.card > 2 * (5 * (a + 2) + 3) + 21 * (a + 2) + 72 := by
  omega

/-- `q ≤ 2n + 3` and `72·(a + 4) ≤ q` force
`18·(a+1)·q + 1 ≤ |validPairs|` — the core `hSample` slope-sampling
hypothesis. Route: `|validPairs| ≥ n² − 3n` (`card_validPairs_lb`)
plus the lower bound on `n`. Axiom-free. -/
theorem validPairs_sample_bound_of_count
    (hLB : E.q ≤ 2 * E.points.card + 3)
    (a : ℕ) (hQbig : 72 * (a + 4) ≤ E.q) :
    18 * (a + 1) * E.q + 1 ≤ (validPairs E).card := by
  have hVP := card_validPairs_lb E
  unfold ECSetup.numAffine at hVP
  set n := E.points.card with hn
  set S := 18 * (a + 1) with hS
  have hn_ge : 2 * S + 9 ≤ n := by omega
  have h1 : S * E.q ≤ S * (2 * n + 3) := Nat.mul_le_mul_left _ hLB
  have h2 : (2 * S + 9) * n ≤ n * n := Nat.mul_le_mul_right _ hn_ge
  have key : S * E.q + 1 + 3 * n ≤ n * n := by nlinarith [h1, h2, hn_ge]
  exact le_trans (Nat.le_sub_of_add_le key) hVP

/-- Lower bound on `|validPairs|` in terms of `q` only, from the
explicit count bound `q ≤ 2n + 3`. For `q ≥ 9`:
`(q − 3)·(q − 9) ≤ 4·|validPairs|`, equivalently
`|validPairs| ≥ (q − 3)·(q − 9)/4 ≈ q²/4` for moderate `q`.
Axiom-free. -/
theorem validPairs_card_ge_q_of_count
    (hLB : E.q ≤ 2 * E.points.card + 3) (hQ : 9 ≤ E.q) :
    (E.q - 3) * (E.q - 9) ≤ 4 * (validPairs E).card := by
  classical
  have hVPlb := card_validPairs_lb E
  unfold ECSetup.numAffine at hVPlb
  set n := E.points.card with hn
  -- From hLB: q ≤ 2n + 3, so q - 3 ≤ 2n and q - 9 ≤ 2n - 6.
  -- card_validPairs_lb: n² - 3n ≤ |validPairs|, so 4(n² - 3n) = (2n)(2n-6) ≤ 4|validPairs|.
  -- Need: (q-3)(q-9) ≤ (2n)(2n-6).
  have hn_ge : 3 ≤ n := by omega
  have h1 : E.q - 3 ≤ 2 * n := by omega
  have h2 : E.q - 9 ≤ 2 * n - 6 := by omega
  have h3 : (E.q - 3) * (E.q - 9) ≤ (2 * n) * (2 * n - 6) :=
    Nat.mul_le_mul h1 h2
  -- (2n)(2n-6) = 4(n*n - 3n) (in ℕ for n ≥ 3).
  have hn2 : 6 ≤ 2 * n := by omega
  have h3n : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn_ge
  have h4 : (2 * n) * (2 * n - 6) = 4 * (n * n - 3 * n) := by
    zify [hn2, h3n]
    ring
  rw [h4] at h3
  omega

/-- `validPairs_card_ge_q_of_count` with the count bound discharged by
the Hasse–Weil axiom. -/
theorem validPairs_card_ge_q (hQ : 9 ≤ E.q) :
    (E.q - 3) * (E.q - 9) ≤ 4 * (validPairs E).card :=
  validPairs_card_ge_q_of_count E (hasse_points_bound_lb E) hQ

/-! ## Field-size extractability headlines -/

/-- **MA extractability, field-size form from explicit count bounds**
(axiom-free). The two linear point-count bounds `2n ≤ 3q + 3` and
`q ≤ 2n + 3` — checkable arithmetic for any concrete curve — replace
the point-count largeness hypotheses of `ma_soundness_count_bound` by the single
field-size threshold `72·(degE + k + 4) ≤ q`, and convert the
`24·(d+k+3)·n` bound into the paper's

  `≤ 36 · (d + k + 4) · q`

(using `d + k + 3 ≤ q`). -/
theorem ma_soundness_count_bound_of_count
    (hUB : 2 * E.points.card ≤ 3 * E.q + 3)
    (hLB : E.q ≤ 2 * E.points.card + 3)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by
  rcases ma_soundness_count_bound E stmt hd hd2 msg hkm hTargetOnE hBasesOnE
      (points_card_threshold_of_count E hLB (stmt.degBound + stmt.k) hQbig)
      (validPairs_sample_bound_of_count E hLB (stmt.degBound + stmt.k) hQbig)
    with hWit | hBound
  · left; exact hWit
  · right
    have h1 : 12 * (stmt.degBound + stmt.k + 3) * (2 * E.points.card)
        ≤ 12 * (stmt.degBound + stmt.k + 3) * (3 * E.q + 3) :=
      Nat.mul_le_mul_left _ hUB
    calc (maAcceptSet E stmt msg hkm).card
        ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := hBound
      _ ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by nlinarith [h1, hdk]

/-- **MA extractability, field-size form** (axiom-priced). The
Hasse–Weil axiom supplies both count bounds of
`ma_soundness_count_bound_of_count`. -/
theorem ma_soundness_count_bound_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q :=
  ma_soundness_count_bound_of_count E (hasse_points_bound E) (hasse_points_bound_lb E)
    stmt hd hd2 msg hkm hTargetOnE hBasesOnE hdk hQbig

/-- `ma_soundness_base` with `hLargeQ` and `hSample` discharged by
the Hasse–Weil axiom from the single field-size threshold
`72·(degE + k + 4) ≤ q`. Two-event accounting form. -/
theorem ma_soundness_base_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k :=
  ma_soundness_base E stmt hd hd2 msg hkm hTargetOnE hBasesOnE
    (points_card_threshold_of_count E (hasse_points_bound_lb E)
      (stmt.degBound + stmt.k) hQbig)
    (validPairs_sample_bound_of_count E (hasse_points_bound_lb E)
      (stmt.degBound + stmt.k) hQbig)

/-- `ip_extractable_base` with the point-count hypotheses discharged
by the Hasse–Weil axiom. -/
theorem ip_extractable_base_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1 hkm).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k)
    ∧ IPUniqueThirdRound E stmt msg1 :=
  ip_extractable_base E stmt hd hd2 msg1 hkm hTargetOnE hBasesOnE
    (points_card_threshold_of_count E (hasse_points_bound_lb E)
      (stmt.degBound + stmt.k) hQbig)
    (validPairs_sample_bound_of_count E (hasse_points_bound_lb E)
      (stmt.degBound + stmt.k) hQbig)

/-- **IP extractability, field-size form from explicit count bounds**
(axiom-free). Same as `ma_soundness_count_bound_of_count`, plus uniqueness of
the accepted third-round response. -/
theorem ip_extractable_of_count
    (hUB : 2 * E.points.card ≤ 3 * E.q + 3)
    (hLB : E.q ≤ 2 * E.points.card + 3)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1 hkm).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_count_bound_of_count E hUB hLB stmt hd hd2 msg1 hkm
      hTargetOnE hBasesOnE hdk hQbig
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- **IP extractability, field-size form** (axiom-priced). Same as
`ma_soundness_count_bound_hasse`, plus uniqueness of the accepted third-round
response. -/
theorem ip_extractable_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1 hkm).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q)
    ∧ IPUniqueThirdRound E stmt msg1 :=
  ip_extractable_of_count E (hasse_points_bound E) (hasse_points_bound_lb E)
    stmt hd hd2 msg1 hkm hTargetOnE hBasesOnE hdk hQbig

/-- **Single-`q` soundness probability bound from explicit count
bounds** (axiom-free). Field-size form of `ma_soundness_ratio_bound`
with `|validPairs|` lower-bounded by `(q − 3)·(q − 9)/4`:

```
|accept| · (q − 3)·(q − 9) ≤ 144·(d + k + 4)·q · |validPairs|
```

Equivalently `|accept|/|validPairs| ≤ 144·(d + k + 4)·q / ((q-3)(q-9))`,
which is `O((d+k)/q)` for `q` of moderate size. -/
theorem ma_soundness_ratio_bound_of_count
    (hUB : 2 * E.points.card ≤ 3 * E.q + 3)
    (hLB : E.q ≤ 2 * E.points.card + 3)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      * ((E.q - 3) * (E.q - 9))
      ≤ 144 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card := by
  have hQ9 : 9 ≤ E.q := by omega
  rcases ma_soundness_count_bound_of_count E hUB hLB stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hdk hQbig with hWit | hBound
  · left; exact hWit
  · right
    have hVP := validPairs_card_ge_q_of_count E hLB hQ9
    -- |accept| * (q-3)(q-9) ≤ 36(d+k+4)q * (q-3)(q-9) ≤ 36(d+k+4)q * 4|validPairs|.
    calc (maAcceptSet E stmt msg hkm).card
              * ((E.q - 3) * (E.q - 9))
        ≤ (36 * (stmt.degBound + stmt.k + 4) * E.q) * ((E.q - 3) * (E.q - 9)) :=
          Nat.mul_le_mul_right _ hBound
      _ ≤ (36 * (stmt.degBound + stmt.k + 4) * E.q) * (4 * (validPairs E).card) :=
          Nat.mul_le_mul_left _ hVP
      _ = 144 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card := by ring

/-- **Single-`q` soundness probability bound** (axiom-priced). -/
theorem ma_soundness_ratio_bound_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      * ((E.q - 3) * (E.q - 9))
      ≤ 144 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card :=
  ma_soundness_ratio_bound_of_count E (hasse_points_bound E)
    (hasse_points_bound_lb E) stmt hd hd2 msg hkm hTargetOnE hBasesOnE hdk hQbig

/-- **Auditing-friendly field-size contrapositive** (axiom-priced).
If accept-count exceeds `36·(d+k+4)·q`, the extractor returns a
witness. -/
theorem ma_soundness_of_excess_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q)
    (hExcess :
      (maAcceptSet E stmt msg hkm).card
        > 36 * (stmt.degBound + stmt.k + 4) * E.q) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_soundness_count_bound_hasse E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hdk hQbig with hWit | hBound
  · exact hWit
  · exact absurd hBound (Nat.not_le.mpr hExcess)

/-- **IP auditing-friendly field-size contrapositive** (axiom-priced). -/
theorem ip_extractable_witness_of_excess_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q)
    (hExcess :
      (maAcceptSet E stmt msg1 hkm).card
        > 36 * (stmt.degBound + stmt.k + 4) * E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg1 = some wit
        ∧ relDlog E stmt wit)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_of_excess_hasse E stmt hd hd2 msg1 hkm
      hTargetOnE hBasesOnE hdk hQbig hExcess
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

end Divisor
