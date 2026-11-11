# Vendored pillar: classical periodic continuation (BKM, Kato local existence, maximal solution)

These files are copies of proved, upstream Lean sources, used by
`FrohmanianTether/Pillars/BKMContinuation.lean`:

| Directory | Upstream repository | Commit |
|---|---|---|
| `FeffermanClayNS.lean`, `FeffermanClayNS/` (all 7 modules) | `BenFrohman/fefferman-clay-navier-stokes` | `ebcf10921e02350e46b32b3bcded8dd8ca2c87c4` |
| `PeriodicNSContinuation/` (the 44 modules imported by `PeriodicNSContinuation.IntegrabilityAttack`) | `BenFrohman/periodic-ns-classical-continuation` | `502ff17` |

`ebcf109` is the `FeffermanClayNS` revision pinned by `periodic-ns-classical-continuation` @ `502ff17`.
Lake dependencies `TorusFourierNS` (`e63af4e`) and `WeightedEnstrophy` (`1df4652`) are required as in
upstream (see `lakefile.lean`).

**The only change** is a mechanical rename, applied to every file:

```
sed -E 's/\bNavierStokes3D\b/FeffermanNavierStokes3D/g;
        s/^((public )?import )(FeffermanClayNS|PeriodicNSContinuation)\b/\1BKMPillar.\3/'
```

It is needed because `FeffermanClayNS/Defs.lean` declares `NavierStokes3D.T3`, `convective`,
`laplacian`, `div`, `pressureGradient`, `vorticity`, `vorticity_sup_norm`, ... with the same fully
qualified names as `FrohmanianTether/NS_Equations.lean`, so the upstream packages cannot be imported
next to this library. No proof, statement or definition body is changed. `bash scripts/check_vendor.sh`
clones both upstream repositories at the commits above, applies the rename and checks every vendored
file byte for byte.

The operators used by the bridge are shown equal to this library's by `rfl` in
`FrohmanianTether/Pillars/BKMContinuation.lean`. The vendored modules are included in the strict
axiom audit (`scripts/AxiomAudit.lean`, module prefix `BKMPillar`). Licence: Apache-2.0, same author.
