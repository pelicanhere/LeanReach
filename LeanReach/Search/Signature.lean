import Lean.Elab.Term
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assumption
import Lean.PrettyPrinter
import LeanReach.Runtime.Environment

namespace LeanReach

open Lean Meta Elab

inductive SignatureMatchKind where
  | exact
  | applicable
  | conclusion
  | sameHead
  | similar
  deriving Inhabited, BEq, Repr

structure SignatureSimilarity where
  shared : Nat := 0
  total : Nat := 0
  deriving Inhabited, BEq

structure SignatureMatch where
  kind : SignatureMatchKind
  coveredInputs : Nat := 0
  extraInputs : Array String := #[]
  extraObligations : Array String := #[]
  similarity : SignatureSimilarity := {}
  deriving Inhabited, BEq

private def SignatureMatchKind.rank : SignatureMatchKind → Nat
  | .exact => 4
  | .applicable => 3
  | .conclusion => 2
  | .sameHead => 1
  | .similar => 0

private def SignatureSimilarity.betterThan
    (left right : SignatureSimilarity) : Bool :=
  if left.total == 0 then false
  else if right.total == 0 then true
  else left.shared * right.total > right.shared * left.total

def SignatureMatch.betterThan (left right : SignatureMatch) : Bool :=
  if left.kind.rank != right.kind.rank then left.kind.rank > right.kind.rank
  else if left.extraObligations.size != right.extraObligations.size then
    left.extraObligations.size < right.extraObligations.size
  else if left.extraInputs.size != right.extraInputs.size then
    left.extraInputs.size < right.extraInputs.size
  else if left.coveredInputs != right.coveredInputs then
    left.coveredInputs > right.coveredInputs
  else
    left.similarity.betterThan right.similarity

private structure TypeSummary where
  head? : Option Name
  constants : NameSet
  inputConstants : NameSet
  resultConstants : NameSet

private def summarizeType (type : Expr) : MetaM TypeSummary :=
  forallTelescopeReducing type fun inputs conclusion => do
    let mut inputConstants : NameSet := {}
    for input in inputs do
      inputConstants := inputConstants ++
        (← inferType input).getUsedConstantsAsSet
    let conclusion ← whnf conclusion
    return {
      head? := conclusion.getAppFn.constName?
      constants := type.getUsedConstantsAsSet
      inputConstants
      resultConstants := conclusion.getUsedConstantsAsSet
    }

private def sharedConstants (left right : NameSet) : Nat :=
  left.toArray.countP right.contains

private def similarity (wanted candidate : TypeSummary) : SignatureSimilarity :=
  let shared :=
    sharedConstants wanted.constants candidate.constants +
    sharedConstants wanted.inputConstants candidate.inputConstants +
    2 * sharedConstants wanted.resultConstants candidate.resultConstants
  let total :=
    wanted.constants.size + candidate.constants.size +
    wanted.inputConstants.size + candidate.inputConstants.size +
    2 * (wanted.resultConstants.size + candidate.resultConstants.size)
  { shared := 2 * shared, total }

private def renderGoal (goal : MVarId) : MetaM String := do
  let type ← instantiateMVars (← goal.getType)
  return (← PrettyPrinter.ppExpr type).pretty (width := 120)

private def applicationMatch? (wantedType : Expr) (candidateName : Name) :
    MetaM (Option (Nat × Array String × Array String)) :=
  withNewMCtxDepth do
    forallTelescopeReducing wantedType fun _ conclusion => do
      let target ← mkFreshExprMVar conclusion
      let candidate ← mkConstWithFreshMVarLevels candidateName
      let goals ← try
          target.mvarId!.apply candidate {
            newGoals := .all
            allowSynthFailures := true
            approx := false
          }
        catch _ => return none
      let mut coveredInputs := 0
      for goal in goals do
        unless ← goal.isAssigned do
          if ← goal.assumptionCore then coveredInputs := coveredInputs + 1
          else
            try
              let synthesized ← goal.withContext do synthInstance (← goal.getType)
              goal.assign synthesized
            catch _ => pure ()
      let mut extraInputs := #[]
      let mut extraObligations := #[]
      for goal in goals do
        unless ← goal.isAssigned do
          let type ← instantiateMVars (← goal.getType)
          let rendered ← renderGoal goal
          if ← try isProp type catch _ => pure false then
            extraObligations := extraObligations.push rendered
          else
            extraInputs := extraInputs.push rendered
      return some (coveredInputs, extraInputs, extraObligations)

private def scoreSignature (wantedType : Expr) (wanted : TypeSummary)
    (candidateName : Name) : MetaM SignatureMatch := do
  let candidateSummary ← withNewMCtxDepth do
    summarizeType (← inferType (← mkConstWithFreshMVarLevels candidateName))
  let structural := similarity wanted candidateSummary
  let exact ← withNewMCtxDepth do
    let candidate ← mkConstWithFreshMVarLevels candidateName
    isDefEq (← inferType candidate) wantedType
  if exact then return { kind := .exact, similarity := structural }
  if let some (coveredInputs, extraInputs, extraObligations) ←
      applicationMatch? wantedType candidateName then
    return {
      kind := if extraInputs.isEmpty && extraObligations.isEmpty then
        .applicable else .conclusion
      coveredInputs
      extraInputs
      extraObligations
      similarity := structural
    }
  return {
    kind := if candidateSummary.head?.isSome &&
      candidateSummary.head? == wanted.head? then .sameHead else .similar
    similarity := structural
  }

private def elaborateWanted (source : String) : Term.TermElabM Expr := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term source "<wanted>" with
    | .ok stx => pure stx
    | .error message => throwError message
  let type ← Term.elabType stx
  Term.synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  if type.hasMVar then throwError "wanted type contains unresolved metavariables"
  return type

unsafe def elaborateSignatureIO (env : Environment) (source : String) : IO Expr :=
  unsafe runCore env <| MetaM.run' <| Term.TermElabM.run' (elaborateWanted source)

unsafe def scoreSignaturesIO (env : Environment) (wantedType : Expr)
    (candidateNames : Array Name) : IO (Array (Name × SignatureMatch)) :=
  unsafe runCore env <| MetaM.run' do
    let wantedSummary ← summarizeType wantedType
    candidateNames.mapM fun name => return (name, ← scoreSignature wantedType wantedSummary name)

end LeanReach
