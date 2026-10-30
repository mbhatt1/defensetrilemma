import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "A Recoverability-Monitor Interface" =>

An earlier draft of this thesis defined recoverability as a probability —
the best-case-over-defender, worst-case-over-adversary chance of returning
to a confidently safe core region before failing — and asserted, without
proof, that crossing a resulting boundary was the event most worth
monitoring in a deployed agent. That probability was never computed, no
existence result was given for it, and no Lean object backed it, so under
this thesis's rule it was removed (Chapter 7). What remains is the
interface a monitor implementing some future, actual recoverability
estimate would need.

```lean
/-- An interface for a recoverability monitor: given a current estimate and
an observation, produce the next estimate, and flag the event that the
estimate has dropped from at or above a threshold to below it. Nothing here
computes, bounds, or justifies `estimate`; the structure only fixes what a
caller would pass in and get back. -/
structure RecoverabilityMonitor (Y : Type) where
  estimate : Float
  update   : Y → Float

def crossedPointOfNoReturn (eta prevEstimate newEstimate : Float) : Bool :=
  (1.0 - eta ≤ prevEstimate) && (newEstimate < 1.0 - eta)
```

`RecoverabilityMonitor` and `crossedPointOfNoReturn` type-check; that is the
whole of this chapter's content. `crossedPointOfNoReturn` is a pure
comparison of two floating-point numbers against a threshold — it says
nothing about what `estimate` should be computed from, and no instance of
`RecoverabilityMonitor` is constructed anywhere in this thesis. The chapter
is included, rather than cut along with the rest of the recoverability
material, because it is genuinely Lean: two declarations that type-check
against Chapter 3's structures and nothing more.
