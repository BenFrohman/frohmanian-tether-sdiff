-- FrohmanianTether/TestFieldFamily.lean, line 117
@[expose] public def concField (x : T3) {r : ℝ} (hr : 0 < r) : CoadjointOrbit :=
  curlOrbit (concBump x hr) (concBump x hr).contDiff
