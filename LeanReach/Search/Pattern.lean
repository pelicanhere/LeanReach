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

structure SearchPattern where
  private mk ::
  compiled : Regex
  candidates : SearchPattern.CandidatePlan

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
private partial def foldCaseInsensitiveClasses : Ast → StateM (Bool × Bool) Ast
  | .group child =>
      do
        let (caseInsensitive, _) ← get
        let child ← foldCaseInsensitiveClasses child
        modify fun (_, changed) => (caseInsensitive, changed)
        return .group child
  | .alternate left right => do
      return .alternate (← foldCaseInsensitiveClasses left)
        (← foldCaseInsensitiveClasses right)
  | .concat left right => do
      return .concat (← foldCaseInsensitiveClasses left)
        (← foldCaseInsensitiveClasses right)
  | .repeat min upper greedy child =>
      return .repeat min upper greedy (← foldCaseInsensitiveClasses child)
  | .classes classes => do
      let (caseInsensitive, _) ← get
      if caseInsensitive then
        return .classes (caseFoldClasses classes)
      return .classes classes
  | .flags enabled => do
      modify fun state => (enabled, state.2 || enabled)
      return .flags enabled
  | ast => return ast

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

/-!
Each alternative below is an ordered list of required ASCII literal runs.
An empty string is a consuming barrier; an empty list is a zero-width match.
Adjacent runs may be joined only when no barrier separates them.
-/

private def concatRuns (left right : Array String) : Array String := Id.run do
  if let some leftLast := left.back? then
    if let some rightFirst := right[0]? then
      if !leftLast.isEmpty && !rightFirst.isEmpty then
        return (left.pop.push (leftLast ++ rightFirst)) ++
          right.extract 1 right.size
  left ++ right

private def combineRuns (left right : Array (Array String)) :
    Option (Array (Array String)) := Id.run do
  if left.size * right.size > maxAlternatives then return none
  let mut result := #[]
  for left in left do
    for right in right do
      let literals := concatRuns left right
      if literals.size > maxLiterals then return none
      result := result.push literals
  return some result

/--
Returns a disjunction of conjunctions of proven-required ASCII literals.
`none` means that analysis was intentionally abandoned, never that no match
exists.
-/
private def requiredRuns (ast : Ast) : Option (Array (Array String)) :=
  if let some literal := asciiLiteral? ast then
    some #[if literal.isEmpty then #[] else #[literal]]
  else
    match ast with
    | .empty => some #[]
    | .epsilon
    | .anchor _
    | .flags _ => some #[#[]]
    | .char char =>
        some #[asciiChar char |>.map (#[·]) |>.getD #[""]]
    | .group child => requiredRuns child
    | .alternate left right => do
        let left ← requiredRuns left
        let right ← requiredRuns right
        if left.size + right.size > maxAlternatives then none
        else some (left ++ right)
    | .concat left right => do
        combineRuns (← requiredRuns left) (← requiredRuns right)
    | .repeat min _ _ child =>
        if min == 0 then
          some #[#[""]]
        else
          (requiredRuns child).map fun alternatives =>
            alternatives.map fun literals => (#[""] ++ literals).push ""
    | .classes _
    | .perl _
    | .dot => some #[#[""]]

private def candidatePlanFor (ast : Ast) (caseInsensitive : Bool) : CandidatePlan :=
  match requiredRuns ast with
  | none => .all
  | some alternatives => Id.run do
    if alternatives.isEmpty then return .empty
    let mut postingAlternatives := #[]
    for literals in alternatives do
      let mut grams := #[]
      for literal in literals do
        for gram in NameSearch.trigrams literal.toLower do
          if (!caseInsensitive || isCacheFoldSafe gram) &&
              grams.size < maxGramsPerAlternative && !grams.contains gram then
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
  let (ast, _, caseInsensitive) :=
    (foldCaseInsensitiveClasses ast).run (false, false)
  if caseInsensitive then discard <| astCost ast
  return {
    compiled := Regex.fromExpr (Ast.toRegex (.group ast))
    candidates := candidatePlanFor ast caseInsensitive
  }

def candidatePlan (pattern : SearchPattern) : CandidatePlan :=
  pattern.candidates

/--
Uses a loaded posting directory to retain the rarest required trigram in each
possible regex branch. `none` requests a full scan; `some #[]` proves that no
branch has candidates.
-/
def CandidatePlan.select (plan : CandidatePlan)
    (count? : String → Option Nat) : Option (Array String) :=
  match plan with
  | .postings alternatives => Id.run do
      let mut selected := #[]
      for grams in alternatives do
        if let some gram := NameSearch.rarestTrigram? grams count? then
          unless selected.contains gram do selected := selected.push gram
      return some selected
  | .all => none
  | .empty => some #[]

/-- Merges sorted, duplicate-free declaration ID arrays. -/
def mergeSortedIds (left right : Array UInt32) : Array UInt32 := Id.run do
  if left.isEmpty then return right
  if right.isEmpty then return left
  let mut result := #[]
  let mut i := 0
  let mut j := 0
  while hi : i < left.size do
    if hj : j < right.size then
      let a := left[i]
      let b := right[j]
      if a < b then
        result := result.push a
        i := i + 1
      else
        result := result.push b
        j := j + 1
        if a == b then i := i + 1
    else break
  return result ++ left.extract i left.size ++ right.extract j right.size

def mergePostingsM {m : Type → Type} [Monad m] (grams : Array String)
    (posting : String → m (Array UInt32)) : m (Array UInt32) := do
  let mut ids := #[]
  for gram in grams do ids := mergeSortedIds ids (← posting gram)
  return ids

def isMatch (pattern : SearchPattern) (name : Name) : Bool :=
  pattern.compiled.test (privateToUserName name).toString

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
