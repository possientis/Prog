" Vim syntax file
" Modified:     2026-05-24 by Hermes + gpt 5.5
" Language:     Rocq
" Filenames:    *.v
" Maintainer:  Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Last Change: 2008 Dec 02 - Added Program and Obligation constructions
"                            (Rocq v8.2), with Serge Leblanc.
"              2008 Jan 30 - Applied improvements for all constructions;
"                            added 'with' and 'where' for fixpoints and
"                            inductives; fixed some old hard bugs.
"              2008 Jan 27 - Changed colouring; improved colouring efficiency.
"              2008 Jan 25 - Added Ltac and Notations; bugfixes.
"              2007 Dec 1  - Added Record's.
"              2007 Nov 28 - Added syntax groups for plugins to detect that
"                            they are inside a proof.
"              2007 Nov 19 - Fixed bug with comments.
"              2007 Nov 17 - Various minor bugfixes.
"              2007 Nov 8  - Added keywords.
"              2007 Nov 8  - Fixed ill-highlighting in declaration types.
"              2007 Nov 8  - Fixed keyword bug: "\<...\>" had been forgotten
"                            (thanks to Vasileios Koutavas).
"              2007 Nov 8  - Definition...Defined now works as expected;
"                            fixed an unrecognized-tactics bug and other bugs.
"              2007 Nov 7  - Complete refactoring; much more accurate
"                            highlighting. Much bigger file...
"              2007 Nov 7  - Added tactic colouration and other keywords
"                            (thanks to Tom Harke).
"              2007 Nov 6  - Added "Defined" keyword (thanks to Serge Leblanc).
"              2007 Nov 5  - Initial version.
" License:     public domain
" TODO: mark bad constructions (eg. Section ended but not opened)

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
 syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "rocq"
 finish
endif

" Rocq is case sensitive.
syn case match

syn cluster rocqVernac contains=rocqRequire,rocqCheck,rocqEval,rocqNotation,rocqTacNotation,rocqDecl,rocqThm,rocqLtacDecl,rocqDef,rocqFix,rocqInd,rocqRec,rocqShow,rocqModule,rocqDeclare,rocqCoercion,rocqScheme

" Various
syn match   rocqError             "\S\+"
syn match   rocqVernacPunctuation ":=\|\.\|:"
syn match   rocqIdent             contained "[_[:alpha:]][_'[:alnum:]]*"
syn keyword rocqTopLevel          Type Canonical Structure Cd Derive Drop Existential
syn region  rocqCoercion          contains=rocqIdent,rocqCoercionClass,rocqCoercionKwd,rocqVernacPunctuation matchgroup=rocqVernacCmd start="\<Coercion\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn keyword rocqCoercionClass     contained Funclass
syn match   rocqCoercionKwd       contained ">->"
"...
syn keyword rocqVernacCmd         Functional Back
syn keyword rocqFeedback          Show About Print

" Terms
syn cluster rocqTerm            contains=rocqKwd,rocqTermPunctuation,rocqKwdMatch,rocqKwdLet,rocqKwdParen
syn region rocqKwdMatch         contained contains=@rocqTerm matchgroup=rocqKwd start="\<match\>" end="\<with\>"
syn region rocqKwdLet           contained contains=@rocqTerm matchgroup=rocqKwd start="\<let\>"   end=":="
syn region rocqKwdParen         contained contains=@rocqTerm matchgroup=rocqTermPunctuation start="(" end=")" keepend extend
syn keyword rocqKwd             contained as else end exists2 fix forall fun if in return struct then
syn match   rocqKwd             contained "\<where\>"
syn match   rocqKwd             contained "\<exists!\?"
syn match   rocqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|-\|*\|=\|>\|<\|<="
syn match rocqTermPunctuation   contained ":=\|:>\|:\|;\|,\|||\|\[\|\]\|@\|?\|\<_\>"

" Various
syn region rocqRequire contains=rocqString matchgroup=rocqVernacCmd start="\<Require\>\%(\_s\+\%(Export\|Import\)\>\)\?" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqRequire matchgroup=rocqVernacCmd start="\<Import\>" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqRequire matchgroup=rocqVernacCmd start="\<Export\>" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqCheck   contains=@rocqTerm matchgroup=rocqVernacCmd start="\<Check\>" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqOpaque  matchgroup=rocqVernacCmd start="\<\%(Opaque\|Transparent\)\>" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqShow       matchgroup=rocqVernacCmd start="\<Show\_s\+\%(\%(Implicits\|Script\|Tree\|Proof\|Conjectures\|Intros\?\|Existentials\)\>\)\?" end="\.\_s"

" Schemes
syn region rocqScheme contains=rocqIdent,rocqSchemeKwd,rocqSchemePunctuation matchgroup=rocqVernacCmd start="\<Scheme\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqScheme contains=rocqIdent,rocqSchemeKwd,rocqSchemePunctuation matchgroup=rocqVernacCmd start="\<Combined\_s\+Scheme\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn keyword rocqSchemeKwd contained Induction Minimality Elimination Sort Prop Set Type for with from
syn match   rocqSchemePunctuation contained ":=\|\.\|,"

" Declare
syn region rocqDeclare contains=rocqDeclareScope,rocqVernacPunctuation matchgroup=rocqVernacCmd start="\<Declare\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqDeclareScope contained contains=rocqDeclareArg matchgroup=rocqVernacCmd start="\<Scope\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn match  rocqDeclareArg contained "[_[:alpha:]][_'[:alnum:]]*"

" Sections
syn region rocqSection contains=rocqSection,@rocqVernac matchgroup=rocqVernacCmd start="\<Section\_s*\z(\S\+\)\_s*\.\_s" end="\<End\_s\+\z1\_s*\.\_s"

" Modules
syn region rocqModule contains=rocqModuleName,rocqModuleAlias,rocqVernacPunctuation matchgroup=rocqVernacCmd start="\<Module\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqModuleAlias contained contains=rocqModulePath,rocqVernacPunctuation matchgroup=rocqVernacPunctuation start=":=" end="\.\_s" keepend
syn match  rocqModuleName contained "[_[:alpha:]][_'[:alnum:]]*"
syn match  rocqModulePath contained "[_[:alpha:]][_'[:alnum:]]*"

" Obligations
syn region rocqObligation contains=rocqIdent   matchgroup=rocqVernacCmd start="\<\%(\%(\%(Admit\_s\+\)\?Obligations\)\|\%(Obligation\_s\+\d\+\)\|\%(Next\_s\+Obligation\)\|Preterm\)\%(\_s\+of\)\?\>" end="\.\_s"
syn region rocqObligation contains=rocqOblOf   matchgroup=rocqVernacCmd start="\<Solve\_s\+Obligations\>" end="\.\_s" keepend
syn region rocqOblOf      contains=rocqIdent,rocqOblUsing matchgroup=rocqVernacCmd start="\<of\>" end="\.\_s" keepend
syn region rocqObligation contains=rocqOblUsing   matchgroup=rocqVernacCmd start="\<Solve\_s\+All\_s\+Obligations\>" end="\.\_s" keepend
syn region rocqOblUsing   contains=rocqLtac   matchgroup=rocqVernacCmd start="\<using\>" end="\.\_s"
syn region rocqObligation contains=rocqOblExpr matchgroup=rocqVernacCmd start="\<Obligations\_s\+Tactic\>" end="\.\_s" keepend
syn region rocqOblExpr    contains=rocqLtac   matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"

" Scopes
syn region rocqBind    contains=rocqScope matchgroup=rocqVernacCmd start="\<Bind\|Delimit\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqArgsScope contains=rocqScope matchgroup=rocqVernacCmd start="\<Arguments\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqOpen    contains=rocqScope matchgroup=rocqVernacCmd start="\<Open\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqClose   contains=rocqScope,rocqLocalScope matchgroup=rocqVernacCmd start="\<Close\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqScope   contained matchgroup=rocqVernacCmd start="\<Scope\>" end="\.\_s"
syn region rocqLocalScope contained contains=rocqScope matchgroup=rocqVernacCmd start="\<Local\>" end="\.\_s"

" Hints
syn region rocqHint contains=rocqHintOption start="\<Hint\>" end="\.\_s" keepend
syn region rocqHintOption start="\<\%(Resolve\|Immediate\|Constructors\|Unfold\|Extern\)\>" end="\.\_s"

" Add
syn region rocqAdd       contains=rocqAddOption,rocqAddOption2 matchgroup=rocqVernacCmd start="\<Add\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqAddOption         contained contains=rocqAddPrintingOption matchgroup=rocqVernacCmd start="\<Printing\>" end="\.\_s"
syn region rocqAddPrintingOption contained matchgroup=rocqVernacCmd start="\<\%(Let\|If\)\>" end="\.\_s"
syn region rocqAddOption         contained contains=rocqAddLegacyOption matchgroup=rocqVernacCmd start="\<Legacy\>" end="\.\_s"
syn region rocqAddLegacyOption   contained contains=rocqAddRingOption,rocqAddSemiRingOption matchgroup=rocqVernacCmd start="\<Abstract\>" end="\.\_s"
syn region rocqAddRingOption     contained matchgroup=rocqVernacCmd start="\<Ring\>" end="\.\_s"
syn region rocqAddSemiRingOption contained contains=rocqAddRingOption matchgroup=rocqVernacCmd start="\<Semi\>" end="\.\_s"
syn region rocqAddLegacyOption   contained matchgroup=rocqVernacCmd start="\<Field\>" end="\.\_s"
syn region rocqAddOption         contained matchgroup=rocqVernacCmd start="\<Field\>" end="\.\_s"
syn region rocqAddOption         contained matchgroup=rocqVernacCmd start="\<Relation\>" end="\.\_s"
syn region rocqAddOption         contained matchgroup=rocqVernacCmd start="\<Ring\>" end="\.\_s"
syn region rocqAddOption         contained matchgroup=rocqVernacCmd start="\<Setoid\>" end="\.\_s"
syn region rocqAddOption         contained matchgroup=rocqVernacCmd start="\<Morphism\>" end="\.\_s"
syn region rocqAddOption         contained contains=rocqAddOption2 matchgroup=rocqVernacCmd start="\<Rec\>" end="\.\_s"
syn region rocqAddOption2        contained contains=rocqString matchgroup=rocqVernacCmd start="\<LoadPath\>" end="\.\_s"
syn region rocqAddOption2        contained contains=rocqAddMLPath matchgroup=rocqVernacCmd start="\<ML\>" end="\.\_s"
syn region rocqAddMLPath         contained contains=rocqString matchgroup=rocqVernacCmd start="\<Path\>" end="\.\_s"

" Set
syn region rocqSet       contains=rocqSetOption matchgroup=rocqVernacCmd start="\<Set\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqSetOption           contained contains=rocqSetPrintingOption matchgroup=rocqVernacCmd start="\<Printing\>" end="\.\_s"
syn region rocqSetPrintingOption   contained matchgroup=rocqVernacCmd start="\<\%(Coercions\|All\|Implicit\|Matching\|Notations\|Synth\|Universes\|Wildcard\)\>" end="\.\_s"
syn region rocqSetPrintingOption   contained matchgroup=rocqVernacCmd start="\<\%(Width\|Depth\)\>" end="\.\_s"
syn region rocqSetPrintingOption   contained matchgroup=rocqVernacCmd start="\<Coercion\>" end="\.\_s"
syn region rocqSetOption           contained matchgroup=rocqVernacCmd start="\<\%(Silent\|Virtual\_s\+Machine\)\>" end="\.\_s"
syn region rocqSetOption           contained matchgroup=rocqVernacCmd start="\<Undo\>" end="\.\_s"
syn region rocqSetOption           contained matchgroup=rocqVernacCmd start="\<Hyps\>" end="\.\_s"
syn region rocqSetHypsOtion        contained matchgroup=rocqVernacCmd start="\<Limit\>" end="\.\_s"
syn region rocqSetOption           contained contains=rocqContextOption matchgroup=rocqVernacCmd start="\<\%(Contextual\|Strict\)\>" end="\.\_s"
syn region rocqContextOption       contained matchgroup=rocqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region rocqSetOption           contained contains=rocqExtractOption matchgroup=rocqVernacCmd start="\<Extraction\>" end="\.\_s"
syn region rocqExtractOption       contained matchgroup=rocqVernacCmd start="\<\%(AutoInline\|Optimize\)\>" end="\.\_s"
syn region rocqSetOption           contained contains=rocqSetFirstorderOption matchgroup=rocqVernacCmd start="\<Firstorder\>" end="\.\_s"
syn region rocqSetFirstorderOption contained matchgroup=rocqVernacCmd start="\<Depth\>" end="\.\_s"
syn region rocqSetOption           contained contains=rocqImplicitOption matchgroup=rocqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region rocqImplicitOption      contained matchgroup=rocqVernacCmd start="\<Arguments\>" end="\.\_s"
syn region rocqSetOption           contained contains=rocqLtacOption matchgroup=rocqVernacCmd start="\<Ltac\>" end="\.\_s"
syn region rocqLtacOption          contained matchgroup=rocqVernacCmd start="\<Debug\>" end="\.\_s"
syn region rocqSetOption           contained contains=rocqLtacOption matchgroup=rocqVernacCmd start="\<Transparent\_s\+Obligations\>" end="\.\_s"

" Unset
syn region rocqUnset       contains=rocqUnsetOption matchgroup=rocqVernacCmd start="\<Unset\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqUnsetOption           contained contains=rocqUnsetPrintingOption matchgroup=rocqVernacCmd start="\<Printing\>" end="\.\_s"
syn region rocqUnsetPrintingOption   contained matchgroup=rocqVernacCmd start="\<\%(Coercions\?\|All\|Implicit\|Matching\|Notations\|Synth\|Universes\|Wildcard\|Width\|Depth\)\>" end="\.\_s"
syn region rocqUnsetOption           contained matchgroup=rocqVernacCmd start="\<\%(Silent\|Virtual\_s\+Machine\)\>" end="\.\_s"
syn region rocqUnsetOption           contained matchgroup=rocqVernacCmd start="\<Undo\>" end="\.\_s"
syn region rocqUnsetOption           contained matchgroup=rocqVernacCmd start="\<Hyps\>" end="\.\_s"
syn region rocqUnsetHypsOtion        contained matchgroup=rocqVernacCmd start="\<Limit\>" end="\.\_s"
syn region rocqUnsetOption           contained contains=rocqContextOption matchgroup=rocqVernacCmd start="\<\%(Contextual\|Strict\)\>" end="\.\_s"
syn region rocqContextOption         contained matchgroup=rocqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region rocqUnsetOption           contained contains=rocqExtractOption matchgroup=rocqVernacCmd start="\<Extraction\>" end="\.\_s"
syn region rocqExtractOption         contained matchgroup=rocqVernacCmd start="\<\%(AutoInline\|Optimize\)\>" end="\.\_s"
syn region rocqUnsetOption           contained contains=rocqUnsetFirstorderOption matchgroup=rocqVernacCmd start="\<Firstorder\>" end="\.\_s"
syn region rocqUnsetFirstorderOption contained matchgroup=rocqVernacCmd start="\<Depth\>" end="\.\_s"
syn region rocqUnsetOption           contained contains=rocqImplicitOption matchgroup=rocqVernacCmd start="\<Implicit\>" end="\.\_s"
syn region rocqImplicitOption        contained matchgroup=rocqVernacCmd start="\<Arguments\>" end="\.\_s"
syn region rocqUnsetOption           contained contains=rocqLtacOption matchgroup=rocqVernacCmd start="\<Ltac\>" end="\.\_s"
syn region rocqLtacOption            contained matchgroup=rocqVernacCmd start="\<Debug\>" end="\.\_s"

" Eval
syn region rocqEval      contains=rocqEvalTac matchgroup=rocqVernacCmd start="\<Eval\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqEvalTac   contained contains=rocqEvalIn matchgroup=rocqTactic start="\<\%(\%(vm_\)\?compute\|red\|hnf\|simpl\|fold\)\>" end="\.\_s" keepend
syn region rocqEvalTac   contained contains=rocqEvalFlag,rocqEvalIn matchgroup=rocqTactic start="\<\%(cbv\|lazy\)\>" end="\.\_s"
syn keyword rocqEvalFlag contained beta delta iota zeta
syn region rocqEvalFlag  contained start="-\?\[" end="\]"
syn region rocqEvalTac   contained contains=@rocqTerm,rocqEvalIn matchgroup=rocqTactic start="\<\%(unfold\|pattern\)\>" end="\.\_s"
syn region rocqEvalIn    contained contains=@rocqTerm matchgroup=rocqVernacCmd start="in" matchgroup=rocqVernacPunctuation end="\.\_s"

" Notations
syn region rocqNotation     contains=rocqNotationDef start="\%(\%(\%(\<Reserved\>\_s*\)\?\<Notation\>\)\|\<Infix\>\)\(\_s*\<Local\>\)\?" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqNotationDef       contained contains=rocqNotationString,rocqNotationTerm matchgroup=rocqVernacCmd start="\%(\%(\%(\<Reserved\>\_s*\)\?\<Notation\>\)\|\<Infix\>\)\(\_s*\<Local\>\)\?" end="\.\_s"
syn region rocqNotationTerm      contained contains=rocqNotationExpr matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqNotationExpr      contained contains=@rocqTerm,rocqNotationEndExpr matchgroup=rocqTermPunctuation start="(" end="\.\_s"
syn region rocqNotationEndExpr   contained contains=rocqNotationFormat,rocqNotationScope matchgroup=rocqTermPunctuation start=")" end="\.\_s"
syn region rocqNotationExpr      contained contains=@rocqTerm,rocqNotationFormat,rocqNotationScope start="[^[:blank:](]" matchgroup=NONE end="\.\_s"
syn region rocqNotationFormat    contained contains=rocqNotationKwd,rocqString,rocqNotationEndFormat matchgroup=rocqVernacPunctuation start="(" end="\.\_s"
syn region rocqNotationEndFormat contained contains=rocqNotationScope matchgroup=rocqVernacPunctuation start=")" end="\.\_s"
syn region rocqNotationScope     contained matchgroup=rocqVernacPunctuation start=":" end="\.\_s"

syn match   rocqNotationKwd contained "at \(next \)\?level"
syn match   rocqNotationKwd contained "\(no\|left\|right\) associativity"
syn match   rocqNotationKwd contained "only parsing"
syn match   rocqNotationKwd contained "(\|,\|)\|:"
syn keyword rocqNotationKwd contained ident global bigint format

syn region rocqNotationString contained start=+"+ skip=+""+ end=+"+ extend

" Tactic notations
syn region rocqTacNotation     contains=rocqTacNotationDef start="\<Tactic\_s\+Notation\>" end="\.\_s" keepend
syn region rocqTacNotationDef  contained contains=rocqNotationString,rocqTacNotationKwd,rocqTacNotationTerm matchgroup=rocqVernacCmd start="Tactic\_s\+Notation" end="\.\_s"
syn region rocqTacNotationTerm contained contains=rocqString,rocqTactic,rocqTacticKwd,rocqLtac,rocqProofPunctuation matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"

syn keyword rocqTacNotationKwd contained ident simple_intropattern hyp reference constr integer int_or_var tactic
syn match   rocqTacNotationKwd contained "at level"

" Declarations 
syn region rocqDecl       contains=rocqIdent,rocqDeclTerm,rocqDeclBinder matchgroup=rocqVernacCmd start="\<\%(Axiom\|Conjecture\|Hypothes[ie]s\|Parameters\?\|Variables\?\)\>" matchgroup=rocqVernacCmd end="\.\_s" keepend
syn region rocqDeclBinder contained contains=rocqIdent,rocqDeclTerm matchgroup=rocqVernacPunctuation start="(" end=")" keepend
syn region rocqDeclTerm   contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" end=")"
syn region rocqDeclTerm   contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" end="\.\_s"

" Theorems
syn region rocqThm       contains=rocqThmName matchgroup=rocqVernacCmd start="\<\%(Program\_s\+\)\?\%(Theorem\|Proposition\|Lemma\|Example\|Corollary\)\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s" keepend
syn region rocqThmName   contained contains=rocqThmTerm,rocqThmBinder matchgroup=rocqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s"
syn region rocqThmTerm   contained contains=@rocqTerm,rocqProofBody matchgroup=rocqVernacCmd start=":" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>"
syn region rocqThmBinder contained matchgroup=rocqVernacPunctuation start="(" end=")" keepend

syn region rocqGoal      contains=rocqGoalTerm start="\<Goal\>" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>" keepend
syn region rocqGoalTerm  contained contains=@rocqTerm,rocqProofBody matchgroup=rocqVernacCmd start="Goal" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\>" keepend

" Ltac
syn region rocqLtacDecl     contains=rocqLtacProfile start="\<Ltac\>" end="\.\_s" keepend
syn region rocqLtacProfile  contained contains=rocqLtacIdent,rocqVernacPunctuation,rocqLtacContents start="Ltac" end="\.\_s"
syn region rocqLtacIdent    contained matchgroup=rocqVernacCmd start="Ltac" matchgroup=rocqIdent end="[_[:alpha:]][_'[:alnum:]]*"
syn region rocqLtacContents contained contains=rocqTactic,rocqTacticKwd,rocqLtac,rocqProofPunctuation matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"

syn keyword rocqLtac contained do info progress repeat try
syn keyword rocqLtac contained abstract constr context end external eval fail first fresh fun goal
syn keyword rocqLtac contained idtac in let ltac lazymatch match of rec reverse solve type with return
syn match   rocqLtac contained "|-\|=>\|||\|\[\|\]\|\<_\>\||"

" Proofs
syn region rocqProofBody  contained contains=rocqProofPunctuation,rocqTactic,rocqTacticKwd,rocqProofComment,rocqProofKwd,rocqProofEnder,rocqProofDelim,rocqLtac matchgroup=rocqVernacPunctuation start="\.\s" start="\.$" matchgroup=NONE end="\<\%(Qed\|Defined\|Admitted\|Abort\)\.\_s" end="\<Save\>.*\.\_s" keepend
syn region rocqProofDelim contained matchgroup=rocqProofDelim start="\<Proof\>" matchgroup=rocqProofDot end="\.\_s"
syn region rocqProofEnder contained matchgroup=rocqProofDelim start="\<\%(Qed\|Defined\|Admitted\)\>" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqProofEnder contained matchgroup=rocqError start="\<Abort\>" matchgroup=rocqVernacPunctuation end="\.\_s"
syn region rocqProofEnder contained contains=rocqIdent matchgroup=rocqProofDelim start="\<Save\>" matchgroup=rocqVernacPunctuation end="\.\_s"

syn keyword rocqTactic    contained absurd apply assert assumption auto autorewrite firstorder specialize
syn keyword rocqTactic    contained case[_eq] change clear[body] cofix cbv lazy compare compute congruence constructor contradiction cut[rewrite]
syn keyword rocqTactic    contained decide decompose dependant destruct discriminate double
syn keyword rocqTactic    contained eapply eassumption eauto econstructor elim[type] equality evar exact eexact exists exfalso
syn keyword rocqTactic    contained field fix f_equal fold fourier functional generalize hnf
syn keyword rocqTactic    contained idtac induction injection instantiate intro[s] intuition inversion[_clear]
syn keyword rocqTactic    contained lapply left move now lia pattern pose proof quote
syn keyword rocqTactic    contained red refine reflexivity remember rename replace revert rewrite right ring
syn keyword rocqTactic    contained set simpl[e] simplify_eq split subst stepl stepr symmetry
syn keyword rocqTactic    contained tauto transitivity trivial unfold vm_compute
syn keyword rocqTacticKwd contained as at by in using with into after until eqn

  " The following is just to help other plugins to detect via syntax groups that we are inside a proof
syn keyword rocqProofKwd         contained else end exists exists2 forall fun if in match let struct then where with
syn match   rocqProofKwd         contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|="
syn match   rocqProofPunctuation contained "(\|)\|:=\|:>\|:\|\.\|;\|,\|||\|\[\|\]\|@\|?"
syn region  rocqProofComment     contained contains=rocqProofComment,rocqTodo start="(\*" end="\*)" extend keepend

" Definitions
syn region rocqDef          contains=rocqDefName matchgroup=rocqVernacCmd start="\<\%(Program\_s\+\)\?\%(Definition\|Let\)\>" matchgroup=rocqVernacPunctuation end=":="me=e-2 end="\.$"me=e-1 end="\.\s"me=e-2 nextgroup=rocqDefContents1,rocqProofBody keepend skipnl skipwhite skipempty
syn region rocqDefName       contained contains=rocqDefBinder,rocqDefType,rocqDefContents1 matchgroup=rocqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="\.\_s" end=":="
syn region rocqDefBinder     contained contains=rocqDefBinderType matchgroup=rocqVernacPunctuation start="(" end=")" keepend
syn region rocqDefBinderType contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" end=")"
syn region rocqDefType       contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" matchgroup=NONE end="\.\_s" end=":="
syn region rocqDefContents1  contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":=" matchgroup=rocqVernacPunctuation end="\.\_s"

" Fixpoints
syn region rocqFix     contains=rocqFixBody start="\<\%(Program\_s\+\)\?\%(\%(\%(Co\)\?Fixpoint\)\|Fixpoint\|Function\)\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqFixBody       contained contains=rocqFixName matchgroup=rocqVernacCmd start="\%(\%(\%(Co\)\?Fixpoint\)\|Function\)" start="\<with\>" matchgroup=NONE end="\.\_s"
syn region rocqFixName       contained contains=rocqFixBinder,rocqFixAnnot,rocqFixTerm,rocqFixContent matchgroup=rocqIdent start="[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="\.\_s"
syn region rocqFixBinder     contained contains=rocqFixBinderType matchgroup=rocqVernacPunctuation start="(" end=")" keepend
syn region rocqFixBinderType contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" end=")" keepend
syn region rocqFixAnnot      contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start="{\_s*struct" end="}" keepend
syn region rocqFixTerm       contained contains=@rocqTerm,rocqFixContent matchgroup=rocqVernacPunctuation start=":" end="\.\_s"
syn region rocqFixContent    contained contains=rocqFixBody,@rocqTerm,rocqKwdMatch,rocqFixNot matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqFixNot        contained contains=rocqNotationString,rocqFixNotTerm matchgroup=rocqVernacCmd start="\<where\>" end="\.\_s"
syn region rocqFixNotTerm    contained contains=@rocqTerm,rocqFixBody,rocqFixNotScope matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqFixNotScope   contained contains=rocqFixBody matchgroup=rocqVernacPunctuation start=":" end="\.\_s"

"Inductives
syn region rocqInd            contains=rocqIndBody start="\<\%(Co\)\?Inductive\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqIndBody     contained contains=rocqIdent,rocqIndTerm,rocqIndBinder matchgroup=rocqVernacCmd start="\%(Co\)\?Inductive" start="\<with\>" matchgroup=NONE end="\.\_s"
syn region rocqIndBinder      contained contains=rocqIndBinderTerm matchgroup=rocqVernacPunctuation start="("  end=")" keepend
syn region rocqIndBinderTerm  contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" end=")"
syn region rocqIndTerm        contained contains=@rocqTerm,rocqIndContent matchgroup=rocqVernacPunctuation start=":" matchgroup=NONE end="\.\_s"
syn region rocqIndContent     contained contains=rocqIndConstructor start=":=" end="\.\_s"
syn region rocqIndConstructor contained contains=rocqConstructor,rocqIndBinder,rocqIndConsTerm,rocqIndNot,rocqIndBody,rocqIndPunctuation matchgroup=rocqVernacPunctuation start=":=\%(\_s*|\)\?" matchgroup=rocqVernacPunctuation start="|" matchgroup=NONE end="\.\_s"
syn region rocqIndConsTerm    contained contains=rocqIndBody,@rocqTerm,rocqIndConstructor,rocqIndNot matchgroup=rocqConstructor start=":" matchgroup=NONE end="\.\_s"
syn region rocqIndNot         contained contains=rocqNotationString,rocqIndNotTerm matchgroup=rocqVernacCmd start="\<where\>" end="\.\_s"
syn region rocqIndNotTerm     contained contains=@rocqTerm,rocqIndNotScope,rocqIndBody matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqIndNotScope    contained contains=rocqIndBody matchgroup=rocqVernacPunctuation start=":" end="\.\_s"
syn match  rocqIndPunctuation contained "|"
syn match  rocqConstructor    contained "[_[:alpha:]][_'[:alnum:]]*"

" Records
syn region rocqRec        contains=rocqRecProfile start="\<Record\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqRecProfile contained contains=rocqIdent,rocqRecTerm,rocqRecBinder matchgroup=rocqVernacCmd start="Record" matchgroup=NONE end="\.\_s"
syn region rocqRecBinder  contained contains=@rocqTerm matchgroup=rocqTermPunctuation start="("  end=")"
syn region rocqRecTerm    contained contains=@rocqTerm,rocqRecContent matchgroup=rocqVernacPunctuation start=":"  end="\.\_s"
syn region rocqRecContent contained contains=rocqConstructor,rocqRecStart matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqRecStart   contained contains=rocqRecField,@rocqTerm start="{" matchgroup=rocqVernacPunctuation end="}" keepend
syn region rocqRecField   contained contains=rocqField matchgroup=rocqVernacPunctuation start="{" end=":"
syn region rocqRecField   contained contains=rocqField matchgroup=rocqVernacPunctuation start=";" end=":"
syn match rocqField       contained "[_[:alpha:]][_'[:alnum:]]*"

" Classes
syn region rocqCla        contains=rocqClaProfile start="\<Class\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqClaProfile contained contains=rocqIdent,rocqClaTerm,rocqClaBinder,rocqClaContent matchgroup=rocqVernacCmd start="Class" matchgroup=NONE end="\.\_s"
syn region rocqClaBinder  contained contains=rocqClaBinderType matchgroup=rocqVernacPunctuation start="("  end=")" keepend
syn region rocqClaBinderType contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":" end=")"
syn region rocqClaTerm    contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start=":\ze[^=]"  end="\.\_s" end=":="
syn region rocqClaContent contained contains=rocqConstructor,rocqClaStart matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqClaStart   contained contains=rocqClaField,@rocqTerm matchgroup=rocqTermPunctuation start="{" matchgroup=rocqTermPunctuation end="}" keepend
syn region rocqClaField   contained contains=rocqField matchgroup=rocqTermPunctuation start="{" end=":"
syn region rocqClaField   contained contains=rocqField matchgroup=rocqTermPunctuation start=";" end=":"

" Instances
syn region rocqInst        contains=rocqIdent,rocqInstTerm,rocqInstBinder,rocqInstContent matchgroup=rocqVernacCmd start="\<\%(Global\|Local\)\_s\+Instance\>" start="\<Instance\>" matchgroup=rocqVernacPunctuation end="\.\_s" keepend
syn region rocqInstProfile contained contains=rocqIdent,rocqInstTerm,rocqInstBinder matchgroup=rocqVernacCmd start="Instance" matchgroup=NONE end="\.\_s"
syn region rocqInstBinder  contained contains=@rocqTerm matchgroup=rocqVernacPunctuation start="("  end=")"
syn region rocqInstTerm    contained contains=@rocqTerm,rocqInstContent matchgroup=rocqVernacPunctuation start=":"  end="\.\_s"
syn region rocqInstContent contained contains=rocqConstructor,rocqInstStart matchgroup=rocqVernacPunctuation start=":=" end="\.\_s"
syn region rocqInstStart   contained contains=rocqInstField,@rocqTerm matchgroup=rocqTermPunctuation start="{" matchgroup=rocqTermPunctuation end="}" keepend
syn region rocqInstField   contained contains=rocqField matchgroup=rocqTermPunctuation start="{" end=":="
syn region rocqInstField   contained contains=rocqField matchgroup=rocqTermPunctuation start=";" end=":="

" Various (High priority)
syn region  rocqComment           containedin=ALL contains=rocqComment,rocqTodo start="(\*" end="\*)" extend keepend
syn keyword rocqTodo              contained TODO FIXME XXX NOTE
syn region  rocqString            start=+"+ skip=+""+ end=+"+ extend

" Synchronization
syn sync minlines=50
syn sync maxlines=500

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_rocq_syntax_inits")
 if version < 508
  let did_rocq_syntax_inits = 1
  command -nargs=+ HiLink hi link <args>
 else
  command -nargs=+ HiLink hi def link <args>
 endif

 " PROOFS
 HiLink rocqTactic                    Keyword
 HiLink rocqLtac rocqTactic
 HiLink rocqProofKwd rocqTactic
 HiLink rocqProofPunctuation rocqTactic
 HiLink rocqTacticKwd rocqTactic
 HiLink rocqTacNotationKwd rocqTactic
 HiLink rocqEvalFlag rocqTactic
 " Exception
 HiLink rocqProofDot rocqVernacular

 " PROOF DELIMITERS ("Proof", "Qed", "Defined", "Save")
 HiLink rocqProofDelim                Underlined

 " TERMS AND TYPES
 HiLink rocqTerm                      Type
 HiLink rocqKwd             rocqTerm
 HiLink rocqTermPunctuation rocqTerm

 " VERNACULAR COMMANDS
 HiLink rocqVernacular                PreProc
 HiLink rocqVernacCmd         rocqVernacular
 HiLink rocqVernacPunctuation rocqVernacular
 HiLink rocqSchemeKwd         rocqVernacular
 HiLink rocqSchemePunctuation rocqVernacular
 HiLink rocqIndPunctuation    rocqVernacular
 HiLink rocqHint              rocqVernacular
 HiLink rocqFeedback          rocqVernacular
 HiLink rocqTopLevel          rocqVernacular
 HiLink rocqCoercionKwd       rocqVernacular
 HiLink rocqCoercionClass     rocqIdent

 " DEFINED OBJECTS
 HiLink rocqIdent                     Identifier
 HiLink rocqDeclareArg                rocqRequire
 HiLink rocqModuleName                Identifier
 HiLink rocqModulePath                rocqRequire
 HiLink rocqNotationString rocqIdent

 " CONSTRUCTORS AND FIELDS
 HiLink rocqConstructor               Keyword
 HiLink rocqField rocqConstructor

 " NOTATION SPECIFIC ("at level", "format", etc)
 HiLink rocqNotationKwd               Special

 " USUAL VIM HIGHLIGHTINGS
   " Comments
   HiLink rocqComment                   Comment
   HiLink rocqProofComment rocqComment

   " Todo
   HiLink rocqTodo                      Todo

   " Errors
   HiLink rocqError                     Error

   " Strings
   HiLink rocqString                    String

 delcommand HiLink
endif

let b:current_syntax = "rocq"
