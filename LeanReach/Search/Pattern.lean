module

public import LeanReach.Search.Match
public import Regex
import all Regex.Syntax.Parser.Basic
import Regex.Unicode.CaseFold
import Std.Data.HashSet

public section

namespace LeanReach

open Lean

universe u v
open Regex.Data (Class Classes)
open Regex.Syntax.Parser

namespace SearchPattern

/--
For each inner array, an executor may load the posting list of any one trigram
(normally the rarest); it must then union the selected lists across the outer
array. Every match is guaranteed to occur in that superset.
-/
inductive CandidatePlan where
  | all
  | empty
  | postings (alternatives : Array (Array String))

end SearchPattern

inductive SearchPattern where
  | regex (compiled : Regex) (candidates : SearchPattern.CandidatePlan)
  | tokens (normalized : Array String) (candidates : SearchPattern.CandidatePlan)

namespace SearchPattern

private def maxPatternBytes := 4096
private def maxAstDepth := 128
private def maxAstNodes := 4096
private def maxExpandedNodes := 8192
private def maxRepeat := 1024
private def maxAlternatives := 64
private def maxLiterals := 256
private def maxGramsPerAlternative := 64

private def addWithin (limit left right : Nat) : Option Nat :=
  if left ≤ limit && right ≤ limit - left then some (left + right) else none

private def mulWithin (limit left right : Nat) : Option Nat :=
  if left == 0 || right ≤ limit / left then some (left * right) else none

private def checkedAdd (what : String) (limit left right : Nat) : Except String Nat :=
  match addWithin limit left right with
  | some total => pure total
  | none => throw s!"regex {what} exceeds the limit of {limit}"

private partial def classesCost (classes : Classes)
    (depth : Nat) : Except String Nat := do
  if depth > maxAstDepth then
    throw s!"regex nesting exceeds the limit of {maxAstDepth}"
  let unary (child : Classes) := do
    checkedAdd "AST size" maxAstNodes 1 (← classesCost child (depth + 1))
  let binary (left right : Classes) := do
    let nodes ← checkedAdd "AST size" maxAstNodes
      (← classesCost left (depth + 1)) (← classesCost right (depth + 1))
    checkedAdd "AST size" maxAstNodes 1 nodes
  match classes with
  | .atom _ => return 1
  | .complement child => unary child
  | .union left right
  | .intersection left right
  | .difference left right
  | .symDiff left right => binary left right

private partial def astCost (ast : Ast) (depth : Nat := 0) : Except String (Nat × Nat) := do
  if depth > maxAstDepth then
    throw s!"regex nesting exceeds the limit of {maxAstDepth}"
  let unary (child : Ast) := do
    let (nodes, expanded) ← astCost child (depth + 1)
    return (← checkedAdd "AST size" maxAstNodes 1 nodes,
      ← checkedAdd "expanded size" maxExpandedNodes 1 expanded)
  let binary (left right : Ast) := do
    let (leftNodes, leftExpanded) ← astCost left (depth + 1)
    let (rightNodes, rightExpanded) ← astCost right (depth + 1)
    let nodes ← checkedAdd "AST size" maxAstNodes leftNodes rightNodes
    let expanded ← checkedAdd "expanded size" maxExpandedNodes leftExpanded rightExpanded
    return (← checkedAdd "AST size" maxAstNodes 1 nodes,
      ← checkedAdd "expanded size" maxExpandedNodes 1 expanded)
  match ast with
  | .group child => unary child
  | .alternate left right
  | .concat left right => binary left right
  | .repeat min upper _ child => do
    if min > maxRepeat || upper.any (· > maxRepeat) then
      throw s!"regex repetition exceeds the limit of {maxRepeat}"
    let (nodes, expanded) ← astCost child (depth + 1)
    let copies := match upper with
      | some upper => upper
      | none => Nat.max 1 (min + 1)
    let some expanded ← pure (mulWithin maxExpandedNodes (expanded + 2) copies)
      | throw s!"regex expanded size exceeds the limit of {maxExpandedNodes}"
    return (← checkedAdd "AST size" maxAstNodes 1 nodes,
      ← checkedAdd "expanded size" maxExpandedNodes 1 expanded)
  | .classes classes => do
    let nodes ← checkedAdd "AST size" maxAstNodes 1
      (← classesCost classes (depth + 1))
    return (nodes, nodes)
  | _ => return (1, 1)

private partial def unionClasses (values : Array Classes)
    (start count : Nat) : Classes :=
  if count ≤ 1 then values[start]!
  else
    let left := count / 2
    .union (unionClasses values start left)
      (unionClasses values (start + left) (count - left))

private def caseFoldSingle (char : Char) : Classes := Id.run do
  let (representative, equivalents) :=
    Regex.Unicode.getCaseFoldEquivChars char
  let mut chars := #[representative]
  for equivalent in equivalents do
    unless chars.contains equivalent do chars := chars.push equivalent
  let values := chars.map fun char => Classes.atom (.single char)
  return unionClasses values 0 values.size

private def inCharRange (first last char : Char) : Bool :=
  first ≤ char && char ≤ last

private def caseFoldRange (first last : Char) : Classes := Id.run do
  let table := Regex.Unicode.caseFoldRepresentatives.get
  let mut representatives : Std.HashSet Char := {}
  let mut values : Array Classes := #[.atom (.range first last)]
  for (source, representative) in table do
    if (inCharRange first last source || inCharRange first last representative) &&
        !representatives.contains representative then
      representatives := representatives.insert representative
      unless inCharRange first last representative do
        values := values.push (.atom (.single representative))
  for (source, representative) in table do
    if representatives.contains representative &&
        !inCharRange first last source then
      values := values.push (.atom (.single source))
  return unionClasses values 0 values.size

private partial def caseFoldClasses : Classes → Classes
  | .atom (.single char) => caseFoldSingle char
  | .atom (.range first last) => caseFoldRange first last
  | .atom (.perl perl) => .atom (.perl perl)
  | .complement child => .complement (caseFoldClasses child)
  | .union left right => .union (caseFoldClasses left) (caseFoldClasses right)
  | .intersection left right =>
      .intersection (caseFoldClasses left) (caseFoldClasses right)
  | .difference left right =>
      .difference (caseFoldClasses left) (caseFoldClasses right)
  | .symDiff left right =>
      .symDiff (caseFoldClasses left) (caseFoldClasses right)

/--
lean-regex folds literal characters under `(?i)`, but not explicit character
classes. Close those classes under the same Unicode simple-fold relation while
preserving the parser's scoped flag state.
-/
private partial def foldCaseInsensitiveClasses (caseInsensitive : Bool) :
    Ast → Bool × Ast
  | .group child =>
      let (_, child) := foldCaseInsensitiveClasses caseInsensitive child
      (caseInsensitive, .group child)
  | .alternate left right =>
      let (caseInsensitive, left) :=
        foldCaseInsensitiveClasses caseInsensitive left
      let (caseInsensitive, right) :=
        foldCaseInsensitiveClasses caseInsensitive right
      (caseInsensitive, .alternate left right)
  | .concat left right =>
      let (caseInsensitive, left) :=
        foldCaseInsensitiveClasses caseInsensitive left
      let (caseInsensitive, right) :=
        foldCaseInsensitiveClasses caseInsensitive right
      (caseInsensitive, .concat left right)
  | .repeat min upper greedy child =>
      let (caseInsensitive, child) :=
        foldCaseInsensitiveClasses caseInsensitive child
      (caseInsensitive, .repeat min upper greedy child)
  | .classes classes =>
      (caseInsensitive,
        .classes (if caseInsensitive then caseFoldClasses classes else classes))
  | .flags enabled => (enabled, .flags enabled)
  | ast => (caseInsensitive, ast)

private def simpleCaseFold (value : String) : String :=
  value.map fun char =>
    if char.toNat < 128 then char.toLower
    else (Regex.Unicode.getCaseFoldEquivChars char).1

/--
A trigram is safe for the existing cache when every character in each of its
simple-fold classes is normalized to the same representative by `Char.toLower`.
-/
private def isCacheFoldSafe (value : String) : Bool :=
  value.toList.all fun char =>
    let (representative, equivalents) :=
      Regex.Unicode.getCaseFoldEquivChars char
    representative.toLower == representative &&
      equivalents.all (·.toLower == representative)

private def asciiChar (char : Char) : Option String :=
  if char.toNat < 128 then some char.toString else none

private def asciiLiteral? : Ast → Option String
  | .epsilon
  | .anchor _
  | .flags _ => some ""
  | .char char => asciiChar char
  | .group child => asciiLiteral? child
  | .concat left right => return (← asciiLiteral? left) ++ (← asciiLiteral? right)
  | .repeat min (some upper) _ child =>
      if min == upper && min ≤ 16 then do
        let value ← asciiLiteral? child
        return (List.replicate min value).foldl (· ++ ·) ""
      else none
  | _ => none

private def combine (left right : Array (Array String)) :
    Option (Array (Array String)) := Id.run do
  if left.size * right.size > maxAlternatives then return none
  let mut result := #[]
  for left in left do
    for right in right do
      if left.size + right.size > maxLiterals then return none
      result := result.push (left ++ right)
  return some result

/--
Returns a disjunction of conjunctions of proven-required ASCII literals.
`none` means that analysis was intentionally abandoned, never that no match
exists.
-/
private def requiredLiterals (ast : Ast) : Option (Array (Array String)) :=
  if let some literal := asciiLiteral? ast then
    some #[#[literal]]
  else
    match ast with
    | .empty => some #[]
    | .group child => requiredLiterals child
    | .alternate left right => do
        let left ← requiredLiterals left
        let right ← requiredLiterals right
        if left.size + right.size > maxAlternatives then none
        else some (left ++ right)
    | .concat left right => do
        combine (← requiredLiterals left) (← requiredLiterals right)
    | .repeat min _ _ child =>
        if min == 0 then some #[#[]] else requiredLiterals child
    | _ => some #[#[]]

private def enablesCaseInsensitive : Ast → Bool
  | .flags enabled => enabled
  | .group child
  | .repeat _ _ _ child => enablesCaseInsensitive child
  | .alternate left right
  | .concat left right => enablesCaseInsensitive left || enablesCaseInsensitive right
  | _ => false

private def candidatePlanFor (ast : Ast) : CandidatePlan :=
  if enablesCaseInsensitive ast then .all
  else
    match requiredLiterals ast with
    | none => .all
    | some alternatives => Id.run do
      if alternatives.isEmpty then return .empty
      let mut postingAlternatives := #[]
      for literals in alternatives do
        let mut grams := #[]
        for literal in literals do
          for gram in NameSearch.trigrams literal.toLower do
            if grams.size < maxGramsPerAlternative && !grams.contains gram then
              grams := grams.push gram
        if grams.isEmpty then return .all
        postingAlternatives := postingAlternatives.push grams
      return .postings postingAlternatives

def compileRegex (source : String) : Except String SearchPattern := do
  if source.utf8ByteSize > maxPatternBytes then
    throw s!"regex exceeds the limit of {maxPatternBytes} bytes"
  let ast ← match parseAst source with
    | .ok ast => pure ast
    | .error error => throw s!"invalid regex: {error}"
  discard <| astCost ast
  let ast := (foldCaseInsensitiveClasses false ast).2
  discard <| astCost ast
  return .regex (Regex.fromExpr (Ast.toRegex (.group ast))) (candidatePlanFor ast)

def compileTokens (tokens : Array String) : Except String SearchPattern := do
  if tokens.isEmpty then throw "token search requires at least one token"
  let mut normalized := #[]
  let mut bytes := 0
  for token in tokens do
    if token.isEmpty then throw "token search does not accept an empty token"
    bytes := bytes + token.utf8ByteSize
    if bytes > maxPatternBytes then
      throw s!"token query exceeds the limit of {maxPatternBytes} bytes"
    let token := simpleCaseFold token
    unless normalized.contains token do
      normalized := normalized.push token
  let mut grams := #[]
  for token in normalized do
    for gram in NameSearch.trigrams token do
      if isCacheFoldSafe gram && grams.size < maxGramsPerAlternative &&
          !grams.contains gram then
        grams := grams.push gram
  let candidates := if grams.isEmpty then .all else .postings #[grams]
  return .tokens normalized candidates

def candidatePlan : SearchPattern → CandidatePlan
  | .regex _ candidates
  | .tokens _ candidates => candidates

/--
Uses a loaded posting directory to retain the rarest required trigram in each
possible regex branch. A missing trigram proves that branch has no candidates.
-/
def CandidatePlan.select (plan : CandidatePlan)
    (count? : String → Option Nat) : CandidatePlan :=
  match plan with
  | .postings alternatives => Id.run do
      let mut selected := #[]
      for grams in alternatives do
        if let some gram := NameSearch.rarestTrigram? grams count? then
          selected := selected.push #[gram]
      return if selected.isEmpty then .empty else .postings selected
  | plan => plan

def unionIds (left right : Array UInt32) : Array UInt32 := Id.run do
  let mut result := #[]
  let mut i := 0
  let mut j := 0
  while i < left.size || j < right.size do
    let value ← if h : i < left.size then
      if h' : j < right.size then
        let a := left[i]
        let b := right[j]
        if a ≤ b then
          i := i + 1
          if a == b then j := j + 1
          pure a
        else
          j := j + 1
          pure b
      else
        let a := left[i]
        i := i + 1
        pure a
    else
      let b := right[j]!
      j := j + 1
      pure b
    unless result.back? == some value do result := result.push value
  return result

def isMatch : SearchPattern → Name → Bool
  | .regex compiled _, name =>
      compiled.test (privateToUserName name).toString
  | .tokens normalized _, name =>
      let name := simpleCaseFold (privateToUserName name).toString
      normalized.all fun token => name.contains token

def collect {α : Type u} {β : Type v} (pattern : SearchPattern)
    (size : Nat) (itemAt : Nat → α) (project : α → Option β)
    (nameOf : β → Name) (limit : Nat) : Array β := Id.run do
  let mut result := #[]
  for position in [0:size] do
    if result.size == limit then break
    let some item := project (itemAt position) | continue
    if pattern.isMatch (nameOf item) then result := result.push item
  return result

end SearchPattern

end LeanReach

end
