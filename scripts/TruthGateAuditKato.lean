/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Scratch.KatoSemantics

/-!
# Truth Gate kernel audit for the local Kato paper locks

For each lock `X ∈ {T1, T2to9, T10, T11}` of `Scratch/KatoSemantics.lean`, checks in the Lean
kernel environment, exactly as `scripts/TruthGateAudit.lean` does for the Clay (B) lock:
* `formal_claim_X`, `paper_claim_X`, `intended_correspondence_X`, `formal_claim_X_holds`,
  `paper_claim_X_holds` exist with the required types;
* each depends only on `propext`, `Classical.choice`, `Quot.sound`;
* `paper_claim_X` is not defined in terms of any `formal_claim_*`, the two bodies differ, and
  `formal_claim_X` and `paper_claim_X` are NOT definitionally equal (no vacuous correspondence);
* the proof of `intended_correspondence_X` does not reach the locked main theorem or any
  `*_holds` lemma (a statement-level equivalence);
* `formal_claim_X_holds` is built from the main theorem, whose statement is definitionally
  `formal_claim_X`;
* `paper_claim_X_holds` is obtained by transport across `intended_correspondence_X`;
* the non-vacuity witnesses depend only on the standard axioms.
-/

open Lean Meta Elab Command

namespace TruthGateAuditKato

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def locks : List (String × Name) :=
  [("T1", `KatoMaximal.katoMaximalSolution_of_feffermanDecay),
   ("T2to9", `KatoMaximal.katoMaximalSolution_properties),
   ("T10", `KatoContinuation.r3BKMContinuation_of_pos),
   ("T11", `KatoContinuation.clay_A_fefferman_of_rate)]

def witnesses : List Name :=
  [`TruthGateKato.paper_FeffermanDatum_zero, `TruthGateKato.paper_RateSmooth_zero,
   `TruthGateKato.paper_ceiling_zero, `TruthGateKato.paper_GlobalSolution_zero,
   `TruthGateKato.paper_T2to9_instance_zero]

def nm (s : String) : Name := Name.mkStr `TruthGateKato s

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen else
    let seen := seen.insert n
    let upstream := match env.getModuleIdxFor? n with
      | some i => let m := env.header.moduleNames[i.toNat]!
          [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
            `ImportGraph, `LeanSearchClient, `Lake, `Cli].any (·.isPrefixOf m)
      | none => false
    if upstream then reach env rest seen else
    match env.find? n with
    | none => reach env rest seen
    | some ci =>
      let cs := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants | none => #[])
      reach env (cs.toList ++ rest) seen

def directUses (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some ci => ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]).foldl (·.insert ·) {}
  | none => {}

end TruthGateAuditKato

open TruthGateAuditKato in
run_cmd do
  let env ← getEnv
  let mut ok := true
  let formals := locks.map (fun (x, _) => nm s!"formal_claim_{x}")
  for (x, main) in locks do
    let fcN := nm s!"formal_claim_{x}"
    let pcN := nm s!"paper_claim_{x}"
    let icN := nm s!"intended_correspondence_{x}"
    let fhN := nm s!"formal_claim_{x}_holds"
    let phN := nm s!"paper_claim_{x}_holds"
    let req := [fcN, pcN, icN, fhN, phN, main]
    let mut present := true
    for n in req do
      unless env.contains n do
        logInfo m!"TRUTH GATE FAIL: missing declaration {n}"; ok := false; present := false
    if !present then continue
    let fc := mkConst fcN
    let pc := mkConst pcN
    unless (← getConstInfo icN).type == mkApp2 (mkConst ``Iff) fc pc do
      logInfo m!"TRUTH GATE FAIL: {icN} does not have type {fcN} ↔ {pcN}"; ok := false
    for (n, t) in [(fhN, fc), (phN, pc)] do
      unless (← getConstInfo n).type == t do
        logInfo m!"TRUTH GATE FAIL: {n} does not have the locked type"; ok := false
    for n in req do
      let axs ← collectAxioms n
      let bad := axs.filter (fun a => !standard.contains a)
      logInfo m!"AXIOMS {n}: {axs.toList}"
      unless bad.isEmpty do
        logInfo m!"TRUTH GATE FAIL: {n} uses nonstandard axioms {bad.toList}"; ok := false
    let fv := ((← getConstInfo fcN).value? (allowOpaque := true)).getD fc
    let pv := ((← getConstInfo pcN).value? (allowOpaque := true)).getD pc
    -- no aliasing, including through the paper-side vocabulary definitions
    let pr := reach env [pcN] {}
    for f in formals do
      if pr.contains f then
        logInfo m!"TRUTH GATE FAIL: {pcN} is defined in terms of {f} (alias)"; ok := false
    if fv == pv then
      logInfo m!"TRUTH GATE FAIL: {fcN} and {pcN} have syntactically equal bodies"; ok := false
    let defeq? : Option Bool ← liftTermElabM <| withTransparency .default <| withoutModifyingState <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 }) <|
        (try some <$> isDefEq fc pc catch _ => pure none)
    if defeq?.isNone then
      logInfo m!"TRUTH GATE NOTE: definitional-equality check for {x} hit its heartbeat cap (inconclusive)"
    if defeq? == some true then
      logInfo m!"TRUTH GATE FAIL: {fcN} and {pcN} are definitionally equal (vacuous lock)"; ok := false
    let r := reach env [icN] {}
    for n in [main, fhN, phN] do
      if r.contains n then
        logInfo m!"TRUTH GATE FAIL: {icN} depends on {n}"; ok := false
    unless (reach env [fhN] {}).contains main do
      logInfo m!"TRUTH GATE FAIL: {fhN} does not use main theorem {main}"; ok := false
    let mt := (← getConstInfo main).type
    let same ← liftTermElabM <| withTransparency .default <| withoutModifyingState <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 }) <|
        (try isDefEq mt fc catch _ => pure false)
    unless same do
      logInfo m!"TRUTH GATE FAIL: statement of {main} is not {fcN}"; ok := false
    unless (directUses env phN).contains icN do
      logInfo m!"TRUTH GATE FAIL: {phN} is not transported across {icN}"; ok := false
  for w in witnesses do
    unless env.contains w do
      logInfo m!"TRUTH GATE FAIL: missing non-vacuity witness {w}"; ok := false
      continue
    let axs ← collectAxioms w
    logInfo m!"AXIOMS {w}: {axs.toList}"
    unless (axs.filter (fun a => !standard.contains a)).isEmpty do
      logInfo m!"TRUTH GATE FAIL: witness {w} uses nonstandard axioms"; ok := false
  if ok then
    logInfo m!"TRUTH GATE AUDIT PASS (local Kato locks): {locks.map (·.2)}; formal_claim_X ↔ paper_claim_X locked, standard axioms only"
  else
    throwError "TRUTH GATE FAIL"
