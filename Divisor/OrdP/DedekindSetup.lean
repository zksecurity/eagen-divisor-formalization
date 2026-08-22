/-
  Divisor/OrdP/DedekindSetup.lean — Dedekind-domain structure on the
  coordinate ring of an `ECSetup` curve (plan.md, Phase 0).

  This is the bridge between the vendored Tau Ceti development
  (`Divisor/Vendor/TauCeti/*`) and the project's `ECSetup`:

  * `ECSetup.instIsElliptic` — `E.toW.IsElliptic`, from the bundled
    discriminant hypothesis `hDisc` via `E.toW_Δ_ne_zero` (over the
    field `ZMod E.q`, `Δ ≠ 0 ↔ IsUnit Δ`).
  * `instIsDedekindDomainCoordinateRing` —
    `IsDedekindDomain E.toW.toAffine.CoordinateRing`, Tau Ceti's
    `isDedekindDomain_coordinateRing` applied to `E.toW.toAffine`.
  * `ECSetup.pointPrime` — the height-one prime
    `⟨X − x, Y − y⟩ ∈ HeightOneSpectrum` at an affine point
    `(x, y) ∈ E.points`, with `asIdeal` definitionally
    `CoordinateRing.XYIdeal E.toW.toAffine x (C y)`; maximality is
    Tau Ceti's `XYIdeal_isMaximal_of_equation` and nontriviality is
    `XYIdeal_ne_bot`.

  Downstream (plan.md Phases 1–3) this is what `ordAt_eq_count`,
  the factorization of `spanSingleton D.toCoordinateRing`, and the
  norm-pushforward argument are stated over.
-/
import Divisor.Vendor.TauCeti.LocalRing
import Divisor.CoordinateRingBridge
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Divisor

variable (E : ECSetup)

/-- `E.toW` is an elliptic curve in mathlib's sense: its discriminant
is a unit. Over the field `ZMod E.q` this is exactly `E.toW_Δ_ne_zero`,
which comes from the bundled `hDisc : 4A³ + 27B² ≠ 0`. -/
instance ECSetup.instIsElliptic : E.toW.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr E.toW_Δ_ne_zero⟩

/-- The coordinate ring of an `ECSetup` curve is a Dedekind domain
(Tau Ceti's `isDedekindDomain_coordinateRing`, vendored). -/
instance instIsDedekindDomainCoordinateRing :
    IsDedekindDomain E.toW.toAffine.CoordinateRing :=
  TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing E.toW.toAffine

/-- The maximal ideal `⟨X − x, Y − y⟩` at an affine point
`(x, y) ∈ E.points`, as an element of the height-one spectrum of the
coordinate ring. Its `asIdeal` is definitionally
`CoordinateRing.XYIdeal E.toW.toAffine P.1 (C P.2)`. -/
noncomputable def ECSetup.pointPrime {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    IsDedekindDomain.HeightOneSpectrum E.toW.toAffine.CoordinateRing where
  asIdeal := CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C P.2)
  isPrime :=
    (TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
      ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))).isPrime
  ne_bot :=
    TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot P.1 (Polynomial.C P.2)

@[simp] theorem ECSetup.pointPrime_asIdeal {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    (E.pointPrime hP).asIdeal
      = CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C P.2) := rfl

/-- The point ideal is maximal (not merely prime). -/
theorem ECSetup.pointPrime_isMaximal {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    (E.pointPrime hP).asIdeal.IsMaximal :=
  TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
    ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))

/-- Distinct affine points give distinct point ideals
(Tau Ceti's `XYIdeal_eq_iff`, vendored). -/
theorem ECSetup.pointPrime_injective {P P' : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hP' : P' ∈ E.points)
    (h : E.pointPrime hP = E.pointPrime hP') : P = P' := by
  have hIdeal : CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C P.2)
      = CoordinateRing.XYIdeal E.toW.toAffine P'.1 (Polynomial.C P'.2) :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  obtain ⟨hx, hy⟩ :=
    (TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff
      ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))).mp hIdeal
  exact Prod.ext hx hy

end Divisor
