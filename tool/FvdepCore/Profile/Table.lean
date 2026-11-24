import FvdepCore.Profile.Types

/-! The implementation profile v1's table (contract `docs/contracts/U6-profile.md` K, P4, I3, K4):
the admitted node kinds, each with the atoms it may own + its slot rule; S = the namespaces carrying
scoped parser entries under `Init` + `Std`; the generated declaration names; the deriving classes.
Frozen data (Q2: a change = a new profile version). The atom sets = each admitted kind's own tokens
(its Lean 4.35 parser definition, ASCII alternatives included; the probe corpus missed tokens shared
with antiquotation syntax, contract U6 K0's correction) minus K's refused atoms; a token a parser
only tests (`withForbiddens`, `notFollowedBy`, `lookahead`) is consumed by no admitted form. -/

namespace FvdepCore.Profile

/-- K0: a kind's slot rule beyond its atoms. -/
inductive Shape where
  /-- No slot rule. -/
  | free
  /-- K2: exactly the opener atom, then one payload atom (any text). -/
  | doc (opener : String)
  /-- K6: exactly one atom, the lexer's spelling (any text). -/
  | literal
  /-- K6: exactly one `name` node, no atom. -/
  | quotedName
  /-- K6: exactly two `` ` `` atoms, then one identifier. -/
  | doubleQuotedName
  /-- K4: the class term (child 1) is one identifier. -/
  | derivingClass
  /-- K3 + P4: `namespace` + one identifier. -/
  | namespaceCmd
  /-- K3 + C1: the section header, `section`, an optional identifier. -/
  | sectionCmd
  /-- K3 + C1: `end`, an optional identifier + its empty tail (`identWithPartialTrailingDot`). -/
  | endCmd
  /-- K4 + K0': an `extends` parent: its optional `toFoo :` slot (an empty `null`, or the
  projection's name + `:`), then the parent's type. -/
  | structParent
  /-- K4 + K0' + I2: `instance`: its attribute kind, the keyword, its priority, its optional name
  (an empty `null`, or a `declId`), its signature + value. -/
  | instanceCmd
  deriving DecidableEq, Repr

/-- K: an admitted kind (its name's components), the atoms it may own (K0: an atom inside `null` or
`group` belongs to its nearest other ancestor) + its slot rule. -/
structure Rule where
  kind : List String
  atoms : List String
  shape : Shape
  deriving DecidableEq, Repr

def rule (k : String) (atoms : List String) (shape : Shape := .free) : Rule :=
  ⟨k.splitOn ".", atoms, shape⟩

/-- K1–K6, v1: every admitted kind. -/
def table : List Rule :=
  [rule "Lean.Parser.Command.moduleDoc" [] (.doc "/-!"),
    rule "Lean.Parser.Command.docComment" [] (.doc "/--"),
    rule "Lean.Parser.Command.namespace" ["namespace"] .namespaceCmd,
    rule "Lean.Parser.Command.section" ["section"] .sectionCmd,
    rule "Lean.Parser.Command.sectionHeader" [], rule "Lean.Parser.Command.end" ["end"] .endCmd,
    rule "Lean.Parser.Command.open" ["open"], rule "Lean.Parser.Command.openSimple" [],
    rule "Lean.Parser.Command.openOnly" ["(", ")"],
    rule "Lean.Parser.Command.variable" ["variable"],
    rule "Lean.Parser.Command.universe" ["universe"], rule "Lean.Parser.Command.declaration" [],
    rule "Lean.Parser.Command.declModifiers" [], rule "Lean.Parser.Command.private" ["private"],
    rule "Lean.Parser.Command.protected" ["protected"],
    rule "Lean.Parser.Command.definition" ["def"], rule "Lean.Parser.Command.abbrev" ["abbrev"],
    rule "Lean.Parser.Command.instance" ["instance"] .instanceCmd,
    rule "Lean.Parser.Term.attrKind" [], rule "Lean.Parser.Command.structure" [":=", "where"],
    rule "Lean.Parser.Command.structureTk" ["structure"],
    rule "Lean.Parser.Command.classTk" ["class"],
    rule "Lean.Parser.Command.extends" [",", "extends"],
    rule "Lean.Parser.Command.structParent" [":"] .structParent,
    rule "Lean.Parser.Command.structCtor" ["::"], rule "Lean.Parser.Command.structFields" [],
    rule "Lean.Parser.Command.structSimpleBinder" [],
    rule "Lean.Parser.Command.structExplicitBinder" ["(", ")"],
    rule "Lean.Parser.Command.structImplicitBinder" ["{", "}"],
    rule "Lean.Parser.Command.structInstBinder" ["[", "]"],
    rule "Lean.Parser.Command.inductive" [":=", "inductive", "where"],
    rule "Lean.Parser.Command.ctor" ["|"], rule "Lean.Parser.Command.mutual" ["end", "mutual"],
    rule "Lean.Parser.Command.declId" [",", ".{", "}"], rule "Lean.Parser.Command.declSig" [],
    rule "Lean.Parser.Command.optDeclSig" [], rule "Lean.Parser.Command.declValSimple" [":="],
    rule "Lean.Parser.Command.declValEqns" [], rule "Lean.Parser.Command.whereStructInst" ["where"],
    rule "Lean.Parser.Term.whereDecls" [";", "where"], rule "Lean.Parser.Term.letRecDecl" [],
    rule "Lean.Parser.Command.optDeriving" [",", "deriving"],
    rule "Lean.Parser.Command.derivingClass" [] (.derivingClass),
    rule "Lean.Parser.Termination.suffix" [],
    rule "Lean.Parser.Termination.terminationBy" ["=>", "structural", "termination_by"],
    rule "Lean.Parser.Termination.decreasingBy" ["decreasing_by"],
    rule "Lean.Parser.Tactic.tacticSeq" [], rule "Lean.Parser.Tactic.tacticSeq1Indented" [";"],
    rule "Lean.Parser.Tactic.paren" ["(", ")"], rule "Lean.Parser.Tactic.omega" ["omega"],
    rule "Lean.Parser.Tactic.decide" ["decide"], rule "Lean.Parser.Tactic.optConfig" [],
    rule "Lean.Parser.Tactic.allGoals" ["all_goals"], rule "Lean.cdot" [],
    rule "Lean.cdotTk" [".", "·"], rule "Lean.Parser.Term.app" [],
    rule "Lean.Parser.Term.paren" [")"], rule "Lean.Parser.Term.hygienicLParen" ["("],
    rule "Lean.Parser.Term.tuple" [")", ","], rule "Lean.Parser.Term.typeAscription" [")", ":"],
    rule "Lean.Parser.Term.anonymousCtor" [",", "⟨", "⟩"], rule "Lean.Parser.Term.hole" ["_"],
    rule "Lean.Parser.Term.cdot" [".", "·"], rule "Lean.Parser.Term.proj" ["."],
    rule "Lean.Parser.Term.dotIdent" ["."], rule "Lean.Parser.Term.pipeProj" ["|>."],
    rule "Lean.Parser.Term.explicit" ["@"], rule "Lean.Parser.Term.namedArgument" ["(", ")", ":="],
    rule "Lean.Parser.Term.typeSpec" [":"], rule "Lean.Parser.Term.explicitBinder" ["(", ")", ":"],
    rule "Lean.Parser.Term.implicitBinder" [":", "{", "}"],
    rule "Lean.Parser.Term.instBinder" ["[", ":", "]"],
    rule "Lean.Parser.Term.strictImplicitBinder" [":", "{", "}", "⦃", "⦄"],
    rule "Lean.Parser.Term.binderDefault" [":="], rule "Lean.binderIdent" [],
    rule "Lean.explicitBinders" [], rule "Lean.unbracketedExplicitBinders" [":"],
    rule "Lean.bracketedExplicitBinders" ["(", ")", ":"], rule "Lean.binderPred<_" ["<"],
    rule "Lean.binderPred>_" [">"], rule "Lean.binderPred≤_" ["≤"], rule "Lean.binderPred≥_" ["≥"],
    rule "Lean.binderPred≠_" ["≠"], rule "Lean.binderPred∈_" ["∈"], rule "Lean.binderPred∉_" ["∉"],
    rule "Lean.binderPred⊆_" ["⊆"], rule "Lean.binderPred⊂_" ["⊂"], rule "Lean.binderPred⊇_" ["⊇"],
    rule "Lean.binderPred⊃_" ["⊃"], rule "Lean.Parser.Term.type" ["Type"],
    rule "Lean.Parser.Term.sort" ["Sort"], rule "Lean.Parser.Term.prop" ["Prop"],
    rule "Lean.Parser.Level.addLit" ["+"], rule "Lean.Parser.Level.max" ["max"],
    rule "Lean.Parser.Level.imax" ["imax"], rule "Lean.Parser.Level.paren" ["(", ")"],
    rule "Lean.Parser.Level.hole" ["_"], rule "Lean.Parser.Term.fun" ["fun", "λ"],
    rule "Lean.Parser.Term.basicFun" ["=>", "↦"], rule "Lean.Parser.Term.arrow" ["->", "→"],
    rule "Lean.Parser.Term.depArrow" ["->", "→"],
    rule "Lean.Parser.Term.forall" [",", "forall", "∀"], rule "Lean.Parser.Term.let" [";", "let"],
    rule "Lean.Parser.Term.have" [";", "have"], rule "Lean.Parser.Term.letConfig" [],
    rule "Lean.Parser.Term.letDecl" [], rule "Lean.Parser.Term.letIdDecl" [":="],
    rule "Lean.Parser.Term.letPatDecl" [":="], rule "Lean.Parser.Term.letId" [],
    rule "termIfThenElse" ["else", "if", "then"],
    rule "termDepIfThenElse" [":", "else", "if", "then"],
    rule "termIfLet" [":=", "else", "if", "let", "then"],
    rule "boolIfThenElse" ["bif", "else", "then"],
    rule "Lean.Parser.Term.match" [",", "match", "with"], rule "Lean.Parser.Term.matchDiscr" [":"],
    rule "Lean.Parser.Term.matchAlts" [], rule "Lean.Parser.Term.matchAlt" [",", "=>", "|"],
    rule "Lean.Parser.Term.matchAltsWhereDecls" [],
    rule "Lean.Parser.Term.structInst" [",", ":", "with", "{", "}"],
    rule "Lean.Parser.Term.structInstFields" [",", ";"], rule "Lean.Parser.Term.structInstField" [],
    rule "Lean.Parser.Term.structInstLVal" ["."],
    rule "Lean.Parser.Term.structInstFieldDef" [":=", "private"],
    rule "Lean.Parser.Term.optEllipsis" [".."], rule "Lean.Parser.Term.quotedName" [] (.quotedName),
    rule "Lean.Parser.Term.doubleQuotedName" ["`"] (.doubleQuotedName),
    rule "Lean.Parser.Term.do" ["do"], rule "Lean.Parser.Term.doSeqIndent" [],
    rule "Lean.Parser.Term.doSeqItem" [";"], rule "Lean.Parser.Term.doExpr" [],
    rule "Lean.Parser.Term.doNested" ["do"], rule "Lean.Parser.Term.doLet" ["let", "mut"],
    rule "Lean.Parser.Term.doLetArrow" ["let", "mut"], rule "Lean.Parser.Term.doIdDecl" ["<-", "←"],
    rule "Lean.Parser.Term.doPatDecl" ["<-", "|", "←"],
    rule "Lean.Parser.Term.doLetElse" [":=", "let", "mut", "|"],
    rule "Lean.Parser.Term.doHave" ["have"], rule "Lean.Parser.Term.doReassign" [],
    rule "Lean.Parser.Term.letIdDeclNoBinders" [":="], rule "Lean.Parser.Term.doReassignArrow" [],
    rule "Lean.Parser.Term.doIf" ["else", "if", "then"], rule "Lean.Parser.Term.doIfProp" [":"],
    rule "Lean.Parser.Term.doIfLet" ["let"], rule "Lean.Parser.Term.doIfLetPure" [":="],
    rule "Lean.Parser.Term.doMatch" [",", "match", "with"],
    rule "Lean.Parser.Term.doFor" [",", "do", "for"], rule "Lean.Parser.Term.doForDecl" [":", "in"],
    rule "Lean.Parser.Term.doUnless" ["do", "unless"], rule "Lean.Parser.Term.doBreak" ["break"],
    rule "Lean.Parser.Term.doContinue" ["continue"], rule "Lean.Parser.Term.doReturn" ["return"],
    rule "Lean.Parser.Term.nestedAction" ["<-", "←"], rule "term_+_" ["+"], rule "term_-_" ["-"],
    rule "term_*_" ["*"], rule "term_/_" ["/"], rule "term_%_" ["%"], rule "term_^_" ["^"],
    rule "term-_" ["-"], rule "term_&&&_" ["&&&"], rule "term_|||_" ["|||"],
    rule "term_^^^_" ["^^^"], rule "term_<<<_" ["<<<"], rule "term_>>>_" [">>>"],
    rule "term~~~_" ["~~~"], rule "term_<_" ["<"], rule "term_>_" [">"], rule "term_≤_" ["<=", "≤"],
    rule "term_≥_" [">=", "≥"], rule "term_=_" ["="], rule "term_≠_" ["≠"], rule "term_==_" ["=="],
    rule "term_!=_" ["!="], rule "term_&&_" ["&&"], rule "term_||_" ["||"], rule "term!_" ["!"],
    rule "term_∧_" ["/\\", "∧"], rule "term_∨_" ["\\/", "∨"], rule "term¬_" ["¬"],
    rule "term_↔_" ["↔"], rule "term_<->_" ["<->"], rule "term_∈_" ["∈"], rule "term_∉_" ["∉"],
    rule "term∃_,_" [",", "∃"], rule "termExists_,_" [",", "exists"],
    rule "Lean.term∃__,_" [",", "∃"], rule "Lean.term∀__,_" [",", "∀"],
    rule "term[_]" [",", "[", "]"], rule "term#[_,]" ["#[", ",", "]"], rule "term_::_" ["::"],
    rule "term_++_" ["++"], rule "term__[_]" ["[", "]"], rule "term__[_]_!" ["!", "[", "]"],
    rule "term__[_]_?" ["?", "[", "]"], rule "term__[_]'_" ["[", "]'"],
    rule "term{_}" [",", "{", "}"], rule "term{}" ["{", "}"], rule "term∅" ["∅"],
    rule "term_×_" ["×"], rule "term{_:_//_}" ["//", ":", "{", "}"], rule "term_<|_" ["<|"],
    rule "term_|>_" ["|>"], rule "term_∘_" ["∘"], rule "term_$__" ["$"], rule "term_<|>_" ["<|>"],
    rule "term_>>=_" [">>="], rule "term_<$>_" ["<$>"], rule "term_<*>_" ["<*>"],
    rule "term_*>_" ["*>"], rule "term_<*_" ["<*"], rule "term_>>_" [">>"],
    rule "coeNotation" ["↑"], rule "Lean.Parser.Term.doIfLetBind" ["<-", "←"],
    rule "num" [] .literal, rule "str" [] .literal, rule "char" [] .literal,
    rule "scientific" [] .literal, rule "name" [] .literal, rule "fieldIdx" [] .literal,
    rule "hygieneInfo" []]

/-- P4: S over `[Init, Std]` (Lean 4.35.0; a gate check pins it against the live grammar). -/
def scopedNamespaces : List (List String) :=
  [["Array"], ["BitVec"], ["Int"], ["Lean"], ["Lean", "Order"], ["Lean", "Parser", "Tactic"],
    ["Lean", "Parser", "Tactic", "Conv"], ["Lean", "Parser", "Tactic", "Grind"], ["List"], ["Rat"],
    ["String", "Internal"], ["Vector"], ["Std", "DHashMap"], ["Std", "DHashMap", "Internal", "Raw"],
    ["Std", "DHashMap", "Internal", "Raw₀"], ["Std", "DHashMap", "Raw"], ["Std", "DTreeMap"],
    ["Std", "DTreeMap", "Internal", "Impl"], ["Std", "DTreeMap", "Raw"], ["Std", "Do"],
    ["Std", "HashMap"], ["Std", "HashMap", "Raw"], ["Std", "HashSet"], ["Std", "HashSet", "Raw"],
    ["Std", "Sat", "AIG"], ["Std", "TreeMap"], ["Std", "TreeMap", "Raw"], ["Std", "TreeSet"],
    ["Std", "TreeSet", "Raw"], ["Std", "WP"]]

/-- I3 (b): Lean's generated declaration names (besides `eq_<n>`, `match_<n>`, `proof_<n>`). -/
def generatedNames : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
    "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "sizeOf_spec", "inj", "injEq",
    "eq_def", "induct", "mutual_induct", "fun_cases", "splitter", "match_on_same_ctor"]

/-- K4: the admitted deriving classes. -/
def derivingClasses : List String := ["DecidableEq", "Repr", "BEq", "Hashable", "Ord", "Inhabited"]

end FvdepCore.Profile
