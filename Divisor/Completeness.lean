/-
  Divisor/Completeness.lean

  Completeness of the MA and IP protocols: the honest prover is
  rejected on few challenge pairs. All axiom-free.

  MA side (`ma_completeness*`):
  * `ma_completeness_base` — rejection set ≤ (3·numZeros + 4)·|E_aff|,
    for any honest message (`isHonestFor`).
  * `ma_completeness` — consolidated point-count form ≤ (3d + 4)·|E|.
  * `ma_completeness_q` — field-size form ≤ (6(d+1) + 6)·q, via the
    trivial fiber bound `|E| ≤ 2q`.
  * `ma_completeness_*_for_length4Simple` — the same chain with the
    honesty predicate supplied constructively by the length-4 simple
    bridge.

  IP side (`ip_completeness*`): the honest third-round response exists
  off `eventDeg`, giving rejection ≤ (3d + 9k + 71)·|E| and the
  field-size form ≤ 18·(d + k + 12)·q.

  The constructive any-length supply for binary witnesses is in
  `Divisor/IsHonestForBinary.lean` and `Divisor/SafeSupport.lean`.
-/
import Divisor.Soundness

namespace Divisor

open Classical

variable (E : ECSetup)

/-- **MA completeness, base form.** For the honest prover's
    first-round message `msg` (witnessed by `isHonestFor`), the set of
    challenges on which the MA verifier rejects is bounded by
    `(3·N + 4) · |E_aff|` via `\ref{lem:support-disjoint}`
    (`support_disjointness`), where `N = numZeros E msg.toD`.

    The three verifier checks:
    * degree check `degE(D) ≤ stmt.degBound` — required by `hDegK`;
    * admissible-set check `(polyA, polyB) ∈ admSet` — required by `hAdm`;
    * log-derivative identity — vanishes off the bad set via the
      explicit honest-divisor bridge, given the honesty predicate.

    Hence rejection forces the challenge into the bad set.

    Factored through `ma_completeness_parameterized`
    (`Divisor/MACompletenessCore.lean`), which takes the per-pair
    `logDerivCheckFn = 0` claim as a hook, so specialized integrations
    (the length-4 simple bridge in `Divisor.LogDerivEagenLength4`, the
    explicit honest-divisor identity in `Divisor.EagenBuildRecursive`)
    can supply it directly. -/
theorem ma_completeness_base
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  let _ := hValid
  let _ := hDeg
  -- Derive D ≠ 0 from the admSet check + admSet_excludes_zero.
  have hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
    admSet_implies_toD_nonzero stmt msg hAdm
  -- Extract on-curve invariants from the strengthened isHonestFor.
  have h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points :=
    hHonestDivisor.2.2.2.1
  have h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points :=
    hHonestDivisor.2.2.2.2
  -- Route through the explicit honest-divisor bridge (no axiom).
  exact ma_completeness_via_isHonestForExplicit E stmt wit hk msg hkm
    hHonestDivisor hD h_negT h_bases hDegK hAdm

/-- **MA completeness** (headline, point-count form). Applying the
    paper-tight `numZeros ≤ degE ≤ degBound` chain to
    `ma_completeness_base`, the rejection-set cardinality is bounded by
    `(3·d + 4) · |E.points|`. Axiom-free; the field-size form is
    `ma_completeness_q` below (trivial fiber bound `|E| ≤ 2q`). -/
theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * stmt.degBound + 4) * E.points.card := by
  have hMA := ma_completeness_base E stmt wit hk hValid msg hkm hDeg hDegK hAdm hHonestDivisor
  have hNZ : numZeros E msg.toD ≤ stmt.degBound := by
    have h1 := numZeros_le_degE E msg.toD hD
    omega
  calc _ ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := hMA
    _ ≤ (3 * stmt.degBound + 4) * E.points.card := by
        unfold ECSetup.numAffine
        exact Nat.mul_le_mul_right _ (by omega)

/-- **MA completeness, field-size form.** Trivial conversion of
    `ma_completeness` via the fiber bound `|E.points| ≤ 2q`
    (`points_card_le_two_q`; no axiom): the rejection-set
    cardinality is bounded by `(6·(d + 1) + 6) · q`. Matches paper's
    `\compErr ≤ 6(\degBound + 1)/q` after dividing by `|E|² ≥ q²/2`. -/
theorem ma_completeness_q
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hMA := ma_completeness E stmt wit hk hValid msg hkm hDeg hDegK hAdm hHonestDivisor hD
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E
  calc _ ≤ (3 * stmt.degBound + 4) * E.points.card := hMA
    _ ≤ (3 * stmt.degBound + 4) * (2 * E.q) := Nat.mul_le_mul_left _ hHasse
    _ ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by ring_nf; omega

/-! ## Length-4 simple completeness via the constructive bridge

For length-4 simple sum-zero quadruples (`P_0 + P_1 + P_2 + P_3 = O`
on `E`) with all witness scalars equal to 1, the
`isHonestFor_of_isHonestForLength4Simple` bridge supplies the
strengthened `isHonestFor` predicate constructively. Composing with
`ma_completeness_base` gives an axiom-clean completeness theorem for this
case, validating the bridge end-to-end. -/

theorem ma_completeness_for_length4Simple
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p =>
          ¬ maVerifierAccepts E stmt msg
            ⟨p.1, p.2⟩
            (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm))).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_base E stmt wit hk hValid msg
    (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm)
    hDeg hDegK hAdm
    (isHonestFor_of_isHonestForLength4Simple E h_simple hk h_scalars)

/-- Point-count consolidated form for the length-4 simple bridge. -/
theorem ma_completeness_clean_for_length4Simple
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p =>
          ¬ maVerifierAccepts E stmt msg
            ⟨p.1, p.2⟩
            (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm))).card
      ≤ (3 * stmt.degBound + 4) * E.points.card := by
  -- D ≠ 0 from the eagenBuild_length4_explicit nonzero property + h_toD_eq.
  have hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) := by
    rw [h_simple.h_toD_eq]
    exact eagenBuild_length4_explicit_ne_zero E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
  exact ma_completeness E stmt wit hk hValid msg
    (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm)
    hDeg hDegK hAdm
    (isHonestFor_of_isHonestForLength4Simple E h_simple hk h_scalars)
    hD

/-- Field-size form for the length-4 simple bridge (trivial fiber
    bound; no axiom). -/
theorem ma_completeness_q_for_length4Simple
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p =>
          ¬ maVerifierAccepts E stmt msg
            ⟨p.1, p.2⟩
            (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm))).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hMA := ma_completeness_clean_for_length4Simple E stmt msg h_simple wit hk
    h_scalars hValid hDeg hDegK hAdm
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E
  calc _ ≤ (3 * stmt.degBound + 4) * E.points.card := hMA
    _ ≤ (3 * stmt.degBound + 4) * (2 * E.q) := Nat.mul_le_mul_left _ hHasse
    _ ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by ring_nf; omega


/-- **IP Completeness (off `eventDeg`).** On every challenge where
    `eventDeg` does **not** hold (paper: `¬event_deg`), the honest IP
    prover constructs a third-round message that the IP verifier
    accepts:

    * `h_i := D'(A_i) / D(A_i)` satisfies `h_i · D(A_i) = D'(A_i)`,
    * `g := -1 / L(-P)` satisfies `g · L(-P) = -1`,

    where `A_2 := computeA₂ chal = (chordX₂, chordY₂)` is the third
    chord-intersection.

    Mirrors paper Theorem `\ref{thm:ip}`'s claim `\compErr_{IP}` is
    bounded analogously to `\compErr_{MA}` once `event_deg` is
    accounted for — see `ip_completeness` below for the
    cardinality form. -/
theorem ip_accept_off_eventDeg
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (chal : MAChallenge E.q)
    (hNotDeg : ¬ eventDeg E msg.toD stmt.target stmt.bases chal.A₀ chal.A₁)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ∃ msg3 : IPProverMsg3 E.q,
      ipVerifierAccepts E stmt msg chal (computeA₂ chal) msg3 := by
  let _ := hkm
  -- Unfold ¬eventDeg = logDerivCheckFnDefined; extract the four nondegen
  -- facts via logDerivCheckFnDenom_factors_ne_zero.
  have hDef : logDerivCheckFnDefined E msg.toD stmt.target stmt.bases
                chal.A₀ chal.A₁ := not_not.mp hNotDeg
  have hFactors := logDerivCheckFnDenom_factors_ne_zero E msg.toD stmt.target
                     stmt.bases chal.A₀ chal.A₁ hDef
  obtain ⟨hD₀_nz, hD₁_nz, hD₂_chord_nz, _, _, _, hLP_nz, _⟩ := hFactors
  -- D(A_2)-nondegeneracy: A_2 = computeA₂ chal = (chordX₂, chordY₂)
  -- definitionally; use this to align with the chord form from hFactors.
  have hA₂_eq : computeA₂ chal =
      (chordX₂ chal.A₀ chal.A₁, chordY₂ chal.A₀ chal.A₁) := rfl
  have hD₂_nz : msg.toD.eval (computeA₂ chal).1 (computeA₂ chal).2 ≠ 0 := by
    rw [hA₂_eq]; exact hD₂_chord_nz
  -- Construct honest msg3.
  let D := msg.toD
  let A₂ := computeA₂ chal
  let h0 := (D.a.derivative.eval chal.A₀.1 -
              D.b.derivative.eval chal.A₀.1 * chal.A₀.2) /
                D.eval chal.A₀.1 chal.A₀.2
  let h1 := (D.a.derivative.eval chal.A₁.1 -
              D.b.derivative.eval chal.A₁.1 * chal.A₁.2) /
                D.eval chal.A₁.1 chal.A₁.2
  let h2 := (D.a.derivative.eval A₂.1 -
              D.b.derivative.eval A₂.1 * A₂.2) /
                D.eval A₂.1 A₂.2
  let g := -1 / (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
                  stmt.target.1 (-stmt.target.2)
  refine ⟨⟨fun i => match i with | 0 => h0 | 1 => h1 | 2 => h2, g⟩,
          hDegK, ?_, ?_, ?_, ?_⟩
  · show h0 * D.eval chal.A₀.1 chal.A₀.2 = _
    simp only [h0]; exact div_mul_cancel₀ _ hD₀_nz
  · show h1 * D.eval chal.A₁.1 chal.A₁.2 = _
    simp only [h1]; exact div_mul_cancel₀ _ hD₁_nz
  · show h2 * D.eval A₂.1 A₂.2 = _
    simp only [h2]; exact div_mul_cancel₀ _ hD₂_nz
  · show g * _ = -1
    simp only [g]; exact div_mul_cancel₀ _ hLP_nz

/-- **IP completeness, cardinality form.** The set of challenges on
    which no third-round message makes the IP verifier accept is
    bounded by `(3·d + 9·k + 71) · |E.points|`, where
    `d = msg.toD.degE` and `k = stmt.k`.

    Single-set bound: IP rejection ⊆ `eventDeg`. The MA denominator
    cases (`D(A_i) = 0`, `A₂ = ∞`) and the IP-specific ones
    (`L(-P) = 0`, `L(B_j) = 0`, `dx/dz = 0`) all live inside
    `eventDeg`, so one bound on `|eventDeg|` covers both. -/
theorem ip_completeness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
  classical
  let _ := hkm
  -- IP rejection ⊆ eventDeg via `ip_accept_off_eventDeg` contrapositive.
  set rejectIP : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                  (computeA₂ ⟨p.1, p.2⟩) msg3) with hRIPdef
  set eventDegSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => eventDeg E msg.toD stmt.target stmt.bases p.1 p.2) with hUdef
  have hSub : rejectIP ⊆ eventDegSet := by
    intro p hp
    simp only [hRIPdef, Finset.mem_filter] at hp
    obtain ⟨hp_pts, hp_no_msg3⟩ := hp
    simp only [hUdef, Finset.mem_filter]
    refine ⟨hp_pts, ?_⟩
    by_contra hNotDeg
    apply hp_no_msg3
    exact ip_accept_off_eventDeg E stmt msg hkm ⟨p.1, p.2⟩ hNotDeg hDegK
  -- |eventDegSet| ≤ (3d + 9k + 71)·|E| by Bezout-on-(E×E).
  have hEventDegEq : eventDegSet =
      (E.points ×ˢ E.points).filter
        (fun p => ¬ logDerivCheckFnDefined E msg.toD stmt.target stmt.bases
                    p.1 p.2) := by
    rw [hUdef]
    exact Finset.filter_congr fun p _ => by simp only [eventDeg]
  calc rejectIP.card
      ≤ eventDegSet.card := Finset.card_le_card hSub
    _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
        rw [hEventDegEq]
        exact logDerivCheckFn_undefined_set_bound_tight E msg.toD stmt.target
                stmt.k stmt.bases hD

/-- **IP completeness, field-size form.** Trivial conversion of
    `ip_completeness` via the fiber bound `|E.points| ≤ 2q`
    (`points_card_le_two_q`; no axiom): the rejection-set
    cardinality is bounded by `18 · (d + k + 12) · q`. -/
theorem ip_completeness_q
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by
  have hIP := ip_completeness E stmt msg hkm hDegK hD
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E
  calc _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := hIP
    _ ≤ (3 * stmt.degBound + 9 * stmt.k + 71) * (2 * E.q) :=
        Nat.mul_le_mul (by omega) hHasse
    _ ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by ring_nf; omega

end Divisor
