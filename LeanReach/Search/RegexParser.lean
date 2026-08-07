module

import all Regex.Syntax.Parser.Basic
public import Regex.Syntax.Ast
public import Regex.Syntax.Parser.Error

namespace LeanReach.Search.RegexParser

open Regex.Syntax.Parser

public def parseAst (source : String) : Except Error Ast :=
  Regex.Syntax.Parser.parseAst source

end LeanReach.Search.RegexParser
