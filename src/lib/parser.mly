%{
%}

%token TLParen        "("
%token TRParen        ")"
%token TComma         ","
%token TDot           "."
%token TSeq           "|-"
%token TQuotation     "?"
%token TConj          "∧"
%token TDisj          "∨"
%token TImpl          "→"
%token TEq            "↔"
%token TNeg           "¬"
%token TForall        "∀"
%token TExists        "∃"
%token <int>    TIdx
%token <string> TIdUppercase
%token <string> TIdLowercase
%token TEOF

%start <(Infer.Goaltable.t, string) result> main

%%
let main :=
  | fs = list(formula); TEOF;
    { Ok(Infer.Goaltable.mk [] fs) }
  | lhs = list(formula); "|-"; rhs = list(formula); TEOF;
    { Ok(Infer.Goaltable.mk lhs rhs) }
  | TEOF; { Error("No input formula") }

let formula :=
  | "("; ~ = formula; ")"; <>
  | id = TIdUppercase; ts = option(pred_args);
    { Syntax.Pred(id, ts |> Core.Option.value ~default:[]) }
  | c = unary_connective; f = formula;
    { Syntax.Conn(c, [f]) }
  | fl = formula; c = bin_connective; fr = formula;
    { Syntax.Conn(c, [fl; fr]) }
  | q = quant; v = TIdLowercase; "."; f = formula;
    { Syntax.Quant(q, v, f) }

let pred_args :=
  "("; ~ = separated_list(",", term); ")"; <>

let term :=
  | v = TIdLowercase;
    { Syntax.Var(v) }
  | v = TIdLowercase; "("; vs = separated_list(",", quotation_var); ")";
    { Syntax.Param(v, vs) }
  | idx = TIdx;
    { Syntax.Bound(idx) }
  | fn = TIdLowercase; "("; ts = list(term); ")";
    { Syntax.Fun(fn, ts) }

let quotation_var :=
  "?"; v = TIdLowercase; { v }

let unary_connective :=
  | TNeg;   { Syntax.CNeg }

let bin_connective :=
  | TConj;  { Syntax.CConj }
  | TDisj;  { Syntax.CDisj }
  | TImpl;  { Syntax.CImpl }
  | TEq;    { Syntax.CEq }

let quant :=
  | TForall; { Syntax.Forall }
  | TExists; { Syntax.Exists }
