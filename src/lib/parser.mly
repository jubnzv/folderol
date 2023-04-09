%{
%}

%token TLParen        "("
%token TRParen        ")"
%token TComma         ","
%token TDot           "."
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

%start <(Syntax.formula, string) result> main

%%
let main :=
  | f = formula; TEOF; { Ok(f) }
  | TEOF; { Error("No input formula") }

let formula :=
  | "("; ~ = formula; ")"; <>
  | id = TIdUppercase; ts = option(pred_args);
    { Syntax.Pred(id, ts |> Core.Option.value ~default:[]) }
  | c = connective; f = formula;
    { Syntax.Conn(c, [f]) }
  | fl = formula; c = connective; fr = formula;
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

let connective :=
  | TConj;  { Syntax.CConj }
  | TDisj;  { Syntax.CDisj }
  | TImpl;  { Syntax.CImpl }
  | TEq;    { Syntax.CEq }
  | TNeg;   { Syntax.CNeg }

let quant :=
  | TForall; { Syntax.Forall }
  | TExists; { Syntax.Exists }
