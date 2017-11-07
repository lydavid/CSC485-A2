% ==============================================================================
% ALE -- Attribute Logic Engine
% ==============================================================================
% Version 4.0 --- alpha version
% Developed under: SICStus Prolog, Version 3.11.2
% Ported to SICStus Prolog, Version 4.0.7

% Authors:

% Bob Carpenter                     
% ---------------------------
% Alias I
% 181 N. 11th St., #401
% Brooklyn, NY 11211
% USA                              
% carp@colloquial.com
%
% Gerald Penn
% --------------------------------
% Department of Computer Science
% University of Toronto
% 10 King's College Rd.
% Toronto M5S 3G4
% Canada
% gpenn@cs.toronto.edu
%
% Copyright 1992-1995, Bob Carpenter and Gerald Penn
% Copyright 1998,1999,2001--2006 Gerald Penn

% BUG FIX  12 JAN 1993 '|' changed to ',' in compile_body(!,.. -- Carpenter

% Extensional types added, using predicates from general constraint
%  resolver - extensionality checked in rules before every edge assertion
%  1/26/93 - G. Penn

% Added iso/2, plus code for compiling extensionality check.
%  2/2/93 - G. Penn

% Bug corrected:  extensionalise hung on cyclic feature structures.
%  2/15/93 - G. Penn

% Added inequations:  checked in rules before edge insertion and after every 
%  recognised daughter description.  Inequation checking partially compiled, in
%  the manner of iso/2.
%  2/24/93 - G. Penn

% Added prolog-style inequation checking to procedural attachments.
%  2/25/93 - G. Penn

% Bug corrected: extensionalise did not handle feature structures with
%  shared structures
%  2/26/93 - G. Penn

% Interpreter added
%  2/26/93 - G. Penn

% Inequation pruning added (at time of full dereferencing)
%  3/3/93 - G. Penn

% Bug corrected: daughters list for parse tree was reversed
%  3/4/93 - G. Penn

% Structure-sharing marked in mother, daughters, and inequations in
%  interpreted mode.  Break command uses prolog "break".
%  3/4/93 - G. Penn

% Bug corrected: reload did not load .extensional.pl
%  3/4/93 - G. Penn

% Bug corrected: interpreter did not assert edges with variable tags.
%  3/4/93 - G. Penn

% Bug corrected: edge/2 printed nothing in non-interpreted mode, and did not
%  print inequations in interpreted mode.
%  3/6/93 - G. Penn

% Edge indices removed, and "trace" information incorporated into edge.  In
%  non-interpreted mode, extra information is uninstantiated.  Edge/2 will not
%  provide interpreter information for edges created while interpreter was
%  inactive
%  3/6/93 - G. Penn

% Inequation data-structure converted from ineq(Tag1-SVs1,Tag2-SVs2,Rest) to
%  ineq(Tag1,SVs1,Tag2,SVs2,Rest).
%  3/6/93 - G. Penn

% Bug corrected: extensionalise_list did not unify eligible structures from
%  different FSs in the given list
%  3/6/93 - G. Penn

% Extensionalise and extensionalise_list now extensionalise a given list of
%  inequations also (they don't check their consistency, however).
%  3/6/93 - G. Penn

% Bug corrected: nth_elt hung with input N <= 0.
%  3/12/93 - G. Penn

% Edges now indexed by a unique number, and daughters now stored by edge index.
%  3/12/93 - G. Penn

% General constraints added to types
%  3/17/93 - G. Penn

% Bug corrected: current_predicate needed to test existence of cons first in
%  compile_cons
%  3/29/93 - G. Penn

% Bug corrected: ud did not unify IqsIn and Out when tags were identical
%  3/29/93 - G. Penn

% Bug corrected: inequations were threaded through negated predicates in
%  compile_body
%  3/29/93 - G. Penn

% Bug corrected: quiet_interpreter mode not reset after parse is finished
%  (now reset by build and by clear).
%  3/29/93 - G. Penn

% cats> category added.  WARNING: Daughter indices not properly recorded for
%  initial cats> elements.
%  4/5/93 - G. Penn

% =\= converted to unary operator with general descriptions.  =@ added to
%  dcs language.
%  4/7/93 - G. Penn

% Bug corrected: find_exts_list terminating condition had too many arguments
%  4/13/93 - G. Penn

% Bug corrected: duplicates_list was passed the wrong FS in add_to
%  4/14/93 - G. Penn

% Bug corrected: lexical items were fully dereferenced and pruned before
%  lexical rules applied.  Now, after.
%  4/17/93 - G. Penn

% Empty categories now undergo lexical rules.
%  4/17/93 - G. Penn

% Bug corrected: add_to(Type,... used cut to prevent false error messages, but
%  also prevented backtracking to satisfy disjunctive constraints on Type.
%  4/17/93 - G. Penn

% Bug corrected: noadd option on query_edge_act did not have enough anonymous
%  arguments
%  4/19/93 - G. Penn

% Bug corrected: compile_body included the code for =@ on the solve list
%  rather than the prolog goal list.
%  4/19/93 - G. Penn

% Bug corrected: daughters of edges were not being printed with re-entrancy
%  intact, since edges were recorded by index and recalled from memory as
%  needed (which broke tag sharing).  Daughters are now printed with accurate
%  re-entrancy, although structure sharing between a daughter and a parent is
%  not indicated still.  Also, daughters of daughters, etc. are now available
%  from any parent edge.
%  4/24/93 - G. Penn

% Bug corrected: in pp_vs(_unwritten), when no_write_feat_flag(F) was detected,
%  the difference list for visited nodes was unlinked
%  4/24/93 - G. Penn

% Bug corrected: =\= had an operator precedence value higher than that of :,
%  and both =\= and : had precedence values lower than ==.
%  5/2/93 - G. Penn

% Bug corrected: extensionalise hung on cyclic feature structures
%  7/20/93 - G. Penn

% general hooks to prolog added (of the form prolog(Goal)).
%  7/20/93 - G. Penn

% option added to suppress error messages from add_to - disjunctive type
%  constraints can yield to many incompatible type messages before the
%  appropriate disjunct is found.  A check is also now made that every
%  word with a lexical description has a lexical entry.
%  7/20/93 - G. Penn

% rec/1 flushes buffer after printing CATEGORY (to allow more accurate timing
%  of rec/4).
%  7/20/93 - G. Penn

% disposed of unnecessary interpreter control code in interp.pl and renamed
%  secret_interp to secret_verbose.
%  10/26/93 - G. Penn

% Suppressing adderrs now automatic for compile_lex.  It remains an option
%  for other top-level predicates which usse add_to.  "Secret" versions of
%  control predicates added.
%  10/26/93 - G. Penn

% Bug corrected: cons/2 and cons/3 were not declared as dynamic.  Thus, the 
%  user could not use certain top-level predicates such as show_type and 
%  show_cons in signatures where no constraints existed.
%  10/26/93 - G. Penn

% Suppressing adderrs now automatic for compile_empty also.
%  11/20/93 - G. Penn

% Bug corrected: suppress_adderrs checks were not accompanied by fail.
%  11/23/93 - G. Penn

% dynamic no_interpreter added.  Helps non-interpreted mode not to be
%  impeded by interpreter code.
%  12/15/93 - G. Penn

% error message now given if extensional type in signature is not maximal.
%  12/15/93 - G. Penn

% Cuts switched from before retracts to after retracts where only one retract 
%  should be done since retract can succeed on backtracking (just to be safe -
%  cuts in other predicates probably prevented any errors before).
%  1/4/94 - G. Penn

% =.. replaced by functor(... when only functor was needed.
%  3/19/94 - G. Penn

% Bug corrected: SVsOut = changed to SVsOut =.. in prune_deref
%  3/19/94 - G. Penn

% fully(TagOut) changed to fully(TagOut,SVsOut), so that prune_deref does
%  not have to redereference the SVs-structure for TagOut.
%  3/19/94 - G. Penn

% Bug corrected: suppress_adderrs was not dynamically declared.
%  3/22/94 - G. Penn

% Bug corrected: missing ! in cats_member check for cats> [].
%  8/1/94 - G. Penn

% Bug corrected: maximality check always failed because every type subsumes
%  itself.  And I'm also really bummed out at the baseball strike that
%  started today since it's the first time the Yankees have had a shot at the 
%  pennant in 13 years.
%  8/12/94 - G. Penn

% ----------------------------------------
% Ale 2.0.1 patches

% Hello message now says Version 2.0.1 instead of Beta.
% 12/22/94 - G. Penn

% match_list and match_list_rest error messages missing set of parentheses.
% 12/22/94 - G. Penn
 
% missing extensionalise_list definition added.
% 12/22/94 - G. Penn

% Compiler did not flush continuants before adding prolog hooks.
%  NOTE - TAIL-RECURSIVE solve PLUS HOOKS LEADS TO UNEXPECTED BEHAVIOUR IN
%  SOME CASES
% 12/23/94 - G. Penn

% Missing abolishes added to compiler code.
% 12/23/94 - G. Penn

% Empty appropriateness definition inserted when no features exist to
%  avert SICStus existence error.
% 12/23/94 - G. Penn

% Missing cut added to compile_dtrs_rest in the final cats> clause.
% 12/23/94 - G. Penn

% 1/8/95 - Bob Carpenter
% Made Quintus compatible by bracketing if_h/1 and renaming append/3

% =====================================================================
% Errors Corrected 2.0.2
% =====================================================================

% 1/23/95 - Bob Carpenter
% Reported by Adam Przepiorkowski
% problem is that featval can be non-deterministic with constraints
% removed faulty cuts in add_to/5 to allow backtracking due to constraints
%    also conditioned error message
% removed cut after featval/6 in 2nd clause of pathval/7
%   conditioned error message

% =====================================================================
% ALE 2.0.2z 
% =====================================================================

% atoms (# _) have been added as extensional types, subsumed by bottom,
%  subsuming nothing, with no appropriate features, and no constraints.
%  As a result, bottom must have no appropriate features or constraints.
% 11-17-95 - G. Penn

% check_sub_seq compiler modified to add fail predicate if there are no
%  non_atomic extensional types.  Before, it only added fail predicate if
%  there were no extensional types.  check_sub_seq is never used with
%  atoms; and the main if_h check_sub_seq compiler clause depends on this
%  fact.
% 12-26-95 - G. Penn

% atom functor changed from #/1 to a_/1.  Because #/2 was already defined,
%  there was a problem with getting prolog to recognize hashed predicates
%  such as unify_type_#(X,Y,Z) as 'unify_type_#'(X,Y,Z) and not #(unify_type_,
%  (X,Y,Z)).  As a result, there can be no type called 'a_'.
% 12-26-95 - G. Penn

% =====================================================================
% Patches integrated from ALE 2.0.3
% =====================================================================

% Added reload/1 in order to load grammar source too (which needs to be there).
% 3/1/97 - G. Penn

% Added a clause for prolog hooks to satisfy_dtrs_goal/6 and pp_goal/4 so that
%  top-level show clauses can display them.
% 3/1/97 - G. Penn

% Added deref_list/2 to deref before calls to extensionalise_list/2.
% Added deref calls before extensionalise calls in show_type/1, mgsat/1,
%  query/1, macro/1, lex_rule/1, show_clause/1 and rule/1
% 3/1/97 - G. Penn

% Added extensionalisation check to compile_body just before =@ calls.
% 3/1/97 - G. Penn

% Added extensionalise/2 predicate for people to use inside hooks.
% 3/5/97 - G. Penn

% =====================================================================
% ALE 3.0
% =====================================================================

% 4/1/96 - Octav Popescu
% Changed compile_body/6 to take an extra argument that's used to compute the
% Goals list as a difference list

% Missing comma added to abolish(add_to_typcons,6) predicate in compile_gram/1.
% 4/5/96 - G. Penn

% 5/1/96 - Octav Popescu
% Added generator based on semantic head-driven generation algorithm
% (Shieber et al, 1990)

% 5/1/96 - Octav Popescu
% Added a test to check_inequal/2 for the case the inequations list is
% uninstantiated

% 5/1/96 - Octav Popescu
% Added test to compile_lex_rules/0 to signal lack of 'morphs' specification
% in a lexical rule

% 5/15/96 - Octav Popescu
% Added indexing and index compilation of the lexicon for generation

% 5/15/96 - Octav Popescu
% Changed to display the new version and add the banner to the version/0 message

% 7/15/96 - Octav Popescu
% Removed some ":" and added some " " to message errors to make them uniform

% Bug corrected: changed call to duplicates_list/8 from Args to
%  ArgsOut in query/1 to take advantage of earlier dereferencing.
% 4/13/97 - G. Penn

% Added missing multiple_heads/1 and sem_head_member/1 definitions
% 5/5/97 - G. Penn

% Removed dynamic cons declarations (which are erased by abolish/2 anyway) and
%  inserted current_predicate/2 declarations to protect top-level show
%  predicates and compile-time error messages which call cons.
% 5/5/97 - G. Penn

% 5/5/97 - Octav Popescu
% Removed 'var' test from check_inequal/2 and prune/2 to allow for first
%  argument indexing

% 5/7/97 - Octav Popescu
% Modified chained/6 and collect_entries/1 to avoid infinite loops generated by
%  the lack of a 'var' test in check_inequal/2

% 6/2/97 - Octav Popescu
% Introduced sem_goal> tags

% 6/10/97 - Octav Popescu
% Added tests for wrongly placed sem_goal> tags

% Changed operator precedence of mgsat/1 to 1125 (from 1150).
% 6/14/97 - G. Penn

% maximal_defaults and bottom_defaults added:  now if type is mentioned
%  as subtype, or introduces features, but is not mentioned as super, assume 
%  sub [] (maximal_defaults); if type is mentioned as supertype, but not as 
%  subtype, assume bot sub (bottom_defaults).
%  6/15/97 - G. Penn

% intro is now autonomous.  Only one of _ intro _ or _ sub _ intro _ is
%  allowed per type.
%  6/15/97 - G. Penn

% subsumption testing added, with interpreter interface.  Commands subtest 
%  and nosubtest toggle testing (run-time option and predicate).
%  6/15/97 - G. Penn

% functional constraints added to description language.
%  6/15/97 - G. Penn

% =@ flagged in type constraints.  More compiler-time error messages added 
%  to compiler code.
%  6/15/97 - G. Penn

% Bug corrected: mgsat/1 tried to print description out after having added
%  it to bottom - big trouble if it involved variables and created a cyclic
%  feature structure.
%  6/15/97 - G. Penn

% Bug corrected: bottom_defaults should not add a default for atoms.
%  9/15/97 - G. Penn

% Added edge/1 to display edge by index.
%  9/16/97 - G. Penn

% Changed name of next option of query_edgeout/9 to continue, and of discard 
%  option of query_discard/10 to noadd.  Added abort options to levels of
%  interpreter that didn't have them. Changed query_proceed in edge/2 to fail.
%  9/17/97 - G. Penn

% setof's removed from maximal_defaults.
%  9/17/97 - G. Penn

% Bug corrected:  T subs Ts did not behave correctly for uninstantiated T
%  9/17/97 - G. Penn

% Bug corrected: a_ X clauses in add_to_typeact and uact didn't bind reference
%  tags correctly.
%  9/23/97 - G. Penn

% Bug corrected: homomorphism condition check modified to handle non-grounded
%  atomic value restrictions.
%  9/23/97 - G. Penn

% Bug corrected: missing set of paren's in map_new_feats_introduced and
%  map_new_feats_find resulting in an improper list for atoms.
%  9/23/97 - G. Penn

% Removed extra lex_rule abolish from compile_lex_rules.
%  9/24/97 - G. Penn

% Bug corrected: maximal_defaults wasn't looking in _ sub Ss intro _ for
%  maximal members of Ss.
%  9/24/97 - G. Penn

% Bug corrected: pp_fs wasn't grounding VisOut for atoms
%  9/24/97 - G. Penn

% Added dynamic declaration for num/1.
%  9/25/97 - G. Penn

% Added abolish_preds/0.
%  9/25/97 - G. Penn

% Reordered type/1 clauses, cleaned up add_to's functional desc. handling,
%  and removed several extraneous extensionality checks on atoms.
%  9/27/97 - G. Penn

% Bug corrected:  current_predicate check added for if/2 in compile_cons.
%  9/27/97 - G. Penn

% Bug corrected:  Ref added to visited list for atoms also.
%  9/27/97 - G. Penn

% Moved secret_noadderrs/0 call in compile_rules past multi-hashing of rule/6.
%  10/5/97 - G. Penn

% Added parse, generate, and parse_and_gen modes.  Still only relative to one 
%  grammar.  parse_and_gen is the default.  Wrote ale_gen.pl and ale_parse.pl
%  glue.
%  10/5/97 - G. Penn

% Bug corrected: parentheses misplaced when parsing/generating modes were
%  added.
%  11/4/97 - G. Penn

% Added warning for ground atoms in appropriateness declarations.
%  11/4/97 - G. Penn

% Bug corrected: add_to/4 and compile_desc/6 had bad cut in inequation
%  clause.  Replaced with ->.
%  12/5/97 - G. Penn

% Modified edge_assert/8 and edge/2 to use rule-name and dtr info regardless
%  of interpreter setting.
%  12/7/97 - G. Penn

% Stripped out version bannering - if you reload ALE, you get two banners.
% Also made parsing only the startup mode.
%  12/10/97 - G. Penn

% Rewrote match_list/11 so that initial cats> daughters are accessible through
%  Dtrs list to the interpreter.  Also involved adding an e_list check to
%  compile_dtrs and compile_dtrs_rest that now requires goal_list_to_seq
%  conversion.
% 12/10/97 - G. Penn

% Bug corrected:  multi_hash on fsolve/5 must be done regardless of whether
%  +++>/2 exists.
% 12/10/97 - G. Penn

% Bug corrected:  fsolve/5, fun/1 and +++>/2 added to abolish_preds
% 12/10/97 - G. Penn

% Removed unused substring/4.
% 12/11/97 - G. Penn

% ALE now turns character_escapes off.
% 12/11/97 - G. Penn

% compile_iso and compile_check now called from inside compile_extensional.
% 2/1/98 - G. Penn

% Bug corrected: rewrote fsolve/5 (now fsolve/4) to compile further and
%  avoid infinite loops in compile_fun/6.
% 2/1/98 - G. Penn

% Bug corrected: added fail-clause for solve/4 for when no if/2 statements are
%  defined.
% 2/1/98 - G. Penn

% Bug corrected: moved compile_fun/0 to just after compile_sig - constraints
%  must have access to fun/1.
% 2/1/98 - G. Penn

% Translated abolish/2 calls to abolish/1 ISO standard.
% 2/28/98 - G. Penn

% ======================================================================
% ALE 3.1
% ======================================================================

% Eliminated unused edge_dtrs/4 predicate
% 3/18/98 - G. Penn

% Switched order of edge index and left node for 1st-arg. indexing during
%  parsing
% 3/18/98 - G. Penn

% Translated !; to ->; and if/3 wherever possible.
% 3/20/98 - G. Penn

% Bug corrected:  misplaced cut in fun/1 clause of add_to/5
% 3/20/98 - G. Penn

% Bug corrected: misplaced cut in mh_arg/8
% 3/20/98 - G. Penn

% =.. replaced by functor/3 and arg/3 calls except where all args are needed.
% 3/20/98 - G. Penn

% Added missing compile_approp/1
% 3/21/98 - G. Penn

% Bug corrected: misplaced paren in compile_lex/0
% 3/21/98 - G. Penn

% Replaced intermediate files with term-expansion-based compiler.
% 3/21/98 - G. Penn

% Bug corrected: misplaced paren in compile_sub_type/2
% 3/21/98 - G. Penn

% Bug corrected: missing existential quantifier in setof/3 call of compile_fun
% 3/22/98 - G. Penn

% Bug corrected: removed redundant "lexical desc. for W is unsatisfiable" error
% 3/22/98 - G. Penn

% Rewrote lex/4 to use if/3.
% 3/24/98 - G. Penn

% Rearranged compiler code dependencies and abolish/1 calls, so that alec_throw
%  compilation and abolish/1 of compiled predicates is performed as locally
%  as possible.  This restores incremental compilation predicates.
% 3/28/98 - G. Penn

% Changed alec_throw to '.alec_throw' and added touch/1 call to file-reading
%  versions of compile-time predicates to ensure existence of '.alec_throw'
% 3/28/98 - G. Penn

% Added portray_message/1 hook to suppress .alec_throw compilation messages
% 3/28/98 - G. Penn

% Added "multiple constraint declaration error" to compile_cons_act/0.  
%  Added current_predicate check to compile_cons for when cons is not
%  defined.
% 3/30/98 - G. Penn

% Converted ucons/7 and add_to_typecons/6 to compile-time predicates.  Added
%  ct/7 compilation in place of carrying around large list of TypeConsPairs.
% 3/30/98 - G. Penn

% Added 5-place and 6-place versions of ud/4 to build less structure on heap
% 4/5/98 - G. Penn

% Added 7-place version of compile_desc/6 to build less structure on heap.
%  Also added 7-place version of compile_fun/6 and 8-place version of
%  compile_pathval/7.
% 4/5/98 - G. Penn

% Changed fsolve/4 to fsolve/5 - split Ref and SVs to build less structure on
%  heap
% 4/5/98 - G. Penn

% Eliminated :- true in compiled code, and first-arg indexed goal_list_to_seq
% 4/5/98 -  G. Penn

% Replaced conc/3 with append/3 from library(lists).
% 4/9/98 - G. Penn

% Replaced make_seq/2 with goal_list_to_seq/2.
% 4/9/98 - G. Penn

% Disposed of unused make_list/2.
% 4/9/98 - G. Penn

% Replaced member/2, select/3, same_length/2, memberchk/2, reverse/2 with
%  definitions from library(lists).
% 4/9/98 - G. Penn

% Replaced ord_union/3 with definition from library(ordsets).
% 4/9/98 - G. Penn

% Added new clause to add_to/5 and compile_desc/6,7 for fast unification of
% unbound variables
% 4/13/98 - G. Penn

% Added MGSat compilation for map_new_feats_find and map_new_feats_introduced,
%  and for add_to_type and u when adding/unifying on one/two FSs with atomic
%  types.
% 4/12/98 - G. Penn

% Changed add_to_typeact so that Type2 is first argument, in case we need
%  to trap special cases of SVs.
% 4/13/98 - G. Penn

% Changed lexicon compilation from compiling to consulting.  Also added more
%  portray_message hooks to trap consulting messages.
% 4/15/98 - G. Penn

% Added lex_assert/0 and lex_compile/0 directives.  Also added dynamic
%  declaration in asserted case.  Extended option's control to empty
%  categories.
% 4/17/98 - G. Penn

% Added multifile declaration to asserted case for lex/4 and empty_cat/3
%  compilation.
% 4/20/98 - G. Penn

% Created lex_act/6 predicate for lex/4 to call from term_expansion/2 hook for
%  update_lex/1.  Added update_lex/1 (which handles empty cats also), 
%  retract_lex/1, retractall_lex/1, retract_empty/0, and retractall_empty/0.
% 4/20/98 - G. Penn

% Bug corrected: generation code for cats> was calling subtype/2 instead of
%  sub_type/2
% 6/15/98 - G. Penn

% Bug corrected: clause added to ct/7 for when cons/2 is not defined.
% 6/16/98 - G. Penn

% Switched order of number_display/2 clauses and added cut to handle variable
%  first arguments (for interpreted generator) 
% 6/18/98 - G. Penn

% Added export_words/2
% 6/23/98 - G. Penn

% Added rec/5 and rec/2 to enforce description on solution FS
% 6/23/98 - G. Penn

% Added rec_best/2, which produces all of the parses for the first list in a
%  a list of lists of words that has any solutions that match an input Desc,
%  rec_list/2, which produces all of the parses for every list in a 
%  list of lists of words, and rec_list/3, which is like rec_list/2 but
%  collects solutions as fs(FS,Iqs) pairs in a list of lists.
% 6/23/98 - G. Penn

% ALE now turns character escapes on.  Code generation modified to print
%  '\+' and '=\=' correctly.
% 6/23/98 - G. Penn

% Moved approps(Type3,FRs3) call in uact/10 to just before map_feats_unif
%   call - otherwise not needed.
% 6/24/98 - G. Penn

% Moved touch('.alec_throw') calls from compile_XYZ/1 predicates to 
%  compile_XYZ/0 predicates.
% 6/25/98 - G. Penn

% Added default maximal type specs for value restrictions and ext/1 types.
% 6/25/98 - G. Penn

% Removed extra space from "Compiling most general satisfiers..." message
%  and "Compiling sub-types..." message
% 6/29/98 - G. Penn

% Bug corrected: rec_best/2's recursive call was to rec_list/2.
% 6/30/98 - G. Penn

% Added lex and gen prefix operators to match rec, query etc.
% 6/30/98 - G. Penn

% Added domain exception to edge/2 to enforce M=<N.
% 6/30/98 - G. Penn

% Moved mode-specific compilation messages inside parsing/generating checks.
% 6/30/98 - G. Penn

% Rewrote generator.
% 7/1/98 - G. Penn

% Changed name of lex(icon)_assert to lex(icon)_consult.
% 7/2/98 - G. Penn

% Bug corrected:  macro calls could not backtrack in add_to because -> was
%  used instead of if/3
% 7/7/98 - G. Penn

% Bug corrected: value restrictions from autonomous intro/2 declarations 
%  were not generating default maximal type specs.  Line break also added
%  at end of 'assuming' messages.
% 7/7/98 - G. Penn

% Bug corrected: a_ subtype/feature spec error did not check for autonomous
%  intros.  bot feature spec error did not check for autonomous intros.
% 7/16/98 - G. Penn

% Bug corrected: maximal_defaults was not filtering out a_/1 value restrictions
%  or extensional types.
% 7/16/98 - G. Penn

% Bug corrected: turned off adderrs for enforcement of description argument of 
% rec/2,5.
% 7/13/98 - G. Penn

% Bug corrected: missing clauses for =@ in pp_goal/4.
% 7/19/98 - G. Penn

% Bug corrected: missing clause for prolog hooks in mg_sat_goal/4
% 7/19/98 - G. Penn

% Bug corrected: several top-level predicates assumed atomic attached goals
%  when collecting FS's to dereference.  Now they use satisfy_dtrs_goal/6
%  instead of mg_sat_goal/4.
% 7/19/98 - G. Penn

% Split chain_rule/8 and chained/4 into separate phases.
% 7/19/98 - G. Penn

% Removed abolish(generate/6) call from compile_grammar/1 - that is done in
%  compile_grammar_act/0.
% 7/19/98 - G. Penn

% Changed non_chain_rule/8, chained/7 and chain_rule/12 to if_b to keep unification
% cases as first clauses after multi-hashing
% 7/19/98 - G. Penn

% Changed edge access to clause/2 calls - bypasses call stack.
% 7/20/98 - G. Penn

% Changed maximal_defaults so that 'assuming' message prints types w/o carriage
% returns.  Modified bottom_defaults message to something parallel.  
% 7/31/98 - G. Penn

% Changed carriage returns on if_warning messages.
% 7/31/98 - G. Penn

% Bug corrected: fast variable binding could leave SVs unbound in some
%  disjunctive descriptions.
% 8/6/98 - G. Penn

% Bug corrected: clause/2 misspelled in subsumed/7
% 8/11/98 - G Penn

% ======================================================================
% ALE 3.2
% ======================================================================

% Renamed alec_catch_act/2 to alec_catch_hook/2.
% 9/7/98 - G. Penn

% Added multifile declaration for term_expansion/2 and alec_catch_hook/2.
% 9/7/98 - G. Penn

% Bug corrected:  sub_type(Type,Type) clause was matching a_ atoms.  Now use
%  subs/2 directly, rather than type/2.
% 10/24/98 - G. Penn

% Added compile-time analysis of variable binding to eliminate var/1 shallow
%  cuts in generated code where possible.
% 11/19/98 - G. Penn

% Added compile-time analysis of descriptions to eliminate fresh variable 
%  allocation in procedural calls where possible.
% 11/20/98 - G. Penn

% Removed solve/4 meta-interpreter.  Clauses are now compiled into Prolog
%  clauses with their names preceded by 'fs_'.  Also added query_goal/4,
%  query_goal/6 and pp_query_goal/4 for query/1 and gen_lex_close/9 to call, 
%  since there is no longer a close correspondence between preparing a goal 
%  for printing and preparing a goal for calling (actually, there never
%  was - the printing prep. code did not work in some cases for calling 
%  prep.).
% 11/22/98 - G. Penn

% Bug corrected: (3.1.1) maximal_defaults added a sub_def entry for bot
%  if it was used as an appropriate value restriction or as an extensional
%  type.
% 11/22/98 - G. Penn

% Quiet interpreter mode removed.  edge/8 always records daughters.
% 1/24/99 - G. Penn

% Cleaned up edge_assert/8 and pulled no_subsumption/0 check out to add_edge.
% 1/24/99 - G. Penn

% Added upward closure error message.
% 2/5/99 - G. Penn

% Added non-negative error message for edge/2
% 2/6/99 - G. Penn

% Bug corrected: node was unhooked in empty category indices - can be bound 
%  from Left arg. of rule/6.
% 3/6/99 - G. Penn

% Bug corrected: compile_desc/11 was binding its FS variable with Tag-SVs and
%  inequational descriptions, which led to wasted structure on the heap.
% 3/6/99 - G. Penn

% Bug corrected: current_predicate check in empty_cat/7 needed to assert
%  alec_closed_rules for rule compiler.
% 3/7/99 - G. Penn

% Implemented EFD-Closure parsing algorithm.  Repairs ALE's problem with
%  empty category combination, as well as with non-ISO compliance of SICStus 
%  (and probably SWI) with respect to asserted predicates.  Tabulate FSs at
%  compile-time to avoid Tag-SVs copying in compiled code.  Cleaned up fresh
%  argument binding and compile_desc/11's FS binding.
% 3/10/99 - G. Penn

% Implemented on-heap parsing to minimise edge copying.
% 3/10/99 - G. Penn

% Added FS palettes to avoid having to compile large FS's in compiled code.
% 3/11/99 - G. Penn

% Changed sub_type/2 and unify_type/3 compilation to consulting.  Doing the
%  same for approp/3 had net effect of slowing compilation down.  System is
%  slightly slower at run-time, presumably because of match_list list checks.
% 3/11/99 - G. Penn

% Modified on-heap chart to use custom edge/8 structures.
% 4/8/99 - G. Penn

% Removed unused member_ref_eq/2.
% 4/9/99 - G. Penn

% Bug corrected: FS palettes need to save inequation tags.
% 4/9/99 - G. Penn

% Rewrote extensionalisation code.
% 4/14/99 - G. Penn

% Bug corrected: query_goal/7 left Dtrs unbound on disjunctions.
% 4/20/99 - G. Penn

% Bug corrected: mg_sat_goal/5 left Iqs unbound on disjunctions.
% 4/20/99 - G. Penn

% Bug corrected: incorrect spacing for =@ in pp_goal/5.
% 4/20/99 - G. Penn

% Added shallow cuts.
% 4/21/99 - G. Penn

% Bug corrected: match_cat_to_next_cat/9 lost empty cat inequations with cats>
% 5/7/99 - G. Penn

% Bug corrected: non_chain_rule/8 code was being consulted.
% 5/8/99 - G. Penn

% Bug corrected: multi_hash/4 reversed order of clauses with same first-arg
%  index by using accumulator in mh_arg/9.  Changed to mh_arg/10 with diff.
%  list to preserve order
% 5/9/99 - G. Penn

% Rewrote subsumption checking code.
% 5/20/99 - G. Penn

% Bug corrected: mh_arg was not capturing variable arguments before decomposing
%  to match hashed argument position.  Added nonvar/1 check.
% 5/21/99 - G. Penn

% Added two-place shallow cuts.
% 5/22/99 - G. Penn

% Bug corrected: cats> Dtrs were bound to rule Dtrs.
% 5/22/99 - G. Penn

% Bug corrected: changed order of all clauses matching shallow cut args so that
%  they are matched before disjunctions.
% 5/22/99 - G. Penn

% Bug corrected: changed edge/2 to check for M<N, since it doesnt display
%  empty cats.  Also added no_interpreter check.
% 5/22/99 - G. Penn

% Bug corrected: empty/0 didnt print nl after '# of dtrs:' line, and dtr-#
%  option didnt handle continue option properly.
% 5/22/99 - G. Penn

% Changed 't's to empty_assoc/1 calls.
% 5/23/99 - G. Penn

% Bug corrected: match_list_rest was not defined with a Chart argument.
% 5/23/99 - G. Penn

% Bug corrected: placed to_rebuild/1 lookup inside clause call
% 5/23/99 - G. Penn

% Changed compile_subsume to check first for parsing flag.
% 5/23/99 - G. Penn

% Bug corrected: show_type failed if there were constraints, but not on the
%  type shown.
% 5/23/99 - G. Penn

% Added type/1 call to show_type so that it can iterate through types if
%  uninstantiated.
% 5/23/99 - G. Penn

% (ALE 3.2.1) Updated for SICStus 3.8.6 - added discontiguous declarations
%  and changed lexrule compilation to consulting because of 256-variable
%  limit (always was there on paper, but now it's enforced!).
% 12/11/01 - G. Penn

% ======================================================================
% ALE 3.3
% ======================================================================

% Changed deref/3 and deref/4 to allow for delaying (pp_fs and fully_deref 
%  bind Tag).  Eliminated now redundant deref_pp/3.
% 2/23/02 - G. Penn

% Removed Dups thread from duplicates/8 - reference tag itself keeps track
%  of this.  Also replaced Vis thread in both duplicates_ and pp_ predicates
%  with assoc lists, and unwound duplicates_list/6 calls that created their 
%  own list structures.  Added Ref/SVs versions of FS predicates; changed
%  pp_fs(...Col) to pp_fs_col to avoid arity conflicts.
% 2/23/02 - G. Penn

% added when_type/3, when_approp/4, when_eq/3, compile_cond/6 and a 
%  compile_body/7 clause for delaying.
% 2/7/99 - G. Penn

% Bug corrected: trigger variables must be embedded in a shallow-cut to trivally
%  succeed, not fail, when the other disjunct is chosen
% 2/9/99 - G. Penn

% Bug corrected: when_approp/3 was passing an unbound variable to the compiler as
%  the body goal rather than a call/1 predicate.  The compiler filled this in with
%  true.
% 2/9/99 - G. Penn

% Bug corrected: query_goal/4,6 were not stripping prolog/1 wrapper off hooks
%  in executable Goal.
% 3/16/02 - G. Penn

% Modified when_eq/3 so that unification can bind tags without instantiating.
% 3/17/02 - G. Penn

% Changed @=/2 compilation to use compile_descs_fresh/12.
% 3/24/02 - G. Penn

% Added support for built-in =/2 (necessary for complex antecedent constraints).
% 4/29/02 - G. Penn

% Bug corrected: empty_cat/7, fsolve/5, lex/4, and non_chain_rule/8 were using 
%  current_predicate/2 to test for success rather than existence, and were undefined 
%  instead of simply producing failure when user code they relied on did not exist.
% 4/29/02 - G. Penn

% Bug corrected: Rewrote immed_cons/3 and show_cons/2 to display procedural attachments
%  on constraints.
% 4/29/02 - G. Penn

% Bug corrected: duplicates_fs/5 must erase a reference from the Visited AVL before it
%  instantiates it, or else the AVL's order-invariant could be thrown off and other
%  elements become irretrievable.
% 5/1/02 - G. Penn

% Added print-hooks (portray_fs/10), and changed duplicate marking from reference
%  instantiation to a parallel AVL tree.
% 5/3/02 - G. Penn
%
% Bug corrected: query_goal/6 (now 7) was not handling narrowly quantified variables
%  properly.  query_goal/3 now calls query_goal/7.
% 5/15/02 - G. Penn

% Enhanced show_type/1 to display info on join reducibility, join preservation, unary
%  branching and procedural attachments to constraints.  Also added new top-level preds
%  join_reducible/1,3, unary_branch/2, and non_join_pres/2.
% 5/18/02 - G. Penn

% Changed show_clause/1 to display ALE source-level predicates (which may still differ
%  from user source if if/2 clauses aren't facts).  The problem is that variables like X in
%      foo(X) if bar(((X,a);(X,b))).
%  can't be resolved without backtracking through interpretations of the description if a and
%  b are not unifiable.  There are also potential problems with resolving descriptions of
%  co-routined predicate bodies without waiting for the conditionals, and side-effects
%  from prolog/1 hooks.  Eventually, information from predicate control flow analysis
%  should be displayed with show_clause/1.
% 5/18/02 - G. Penn

% Changed alec_closed_rules/1 assertion to individual alec_rule/7 assertions.
%  Changed rule/1 to display goals as in show_clause/1 above, but expanded by
%  EFD-closure.
% 5/18/02 - G. Penn

% Changed lex_rule/1 to display goals as in show_clause/1 above.  Input and output
%  descriptions are still resolved.
% 5/18/02 - G. Penn

% HACK: added consistency checking before unify_type/3 compilation to exploit typically
%  low join density of large signatures.
% 6/6/02 - G. Penn

% Bug corrected: DtrsDesc, and Iqs were unhooked in satisfy_dtrs/7.
% 6/6/02 - G. Penn

% Bug corrected: homomorphism condition warning was not generated in all cases.
% 6/7/02 - G. Penn

% ud/4,5,6 and u/6 modified to exploit symmetry of unification by generating code only
%  for pairs in the standard order.
% 6/7/02 - G. Penn

% approps/2 now compiled.
% 6/14/02 - G. Penn

% References instantiated at run-time in u/6 and add_to_type/5 when constraints present,
%  to avoid copying structure in code area.  Rewrote ct/6, map_cons/6, add_to_typecons/6,
%  ucons/7 and mgsat_cons/6 to use FS rather than Tag and SVs.
% 6/14/02 - G. Penn

% Reindexed ucons/7 and add_to_typecons/6 findall calls on new constrained/1 predicate
%  that tabulates which types are antecedents of constraints.
% 6/14/02 - G. Penn

% Bug corrected: featval/6 can no longer use add_to_typeact/8 because of change in
%  reference instantiation.  Added featval_act/10.
% 6/16/02 - G. Penn

% approps/3 now tabulates length of FRs.
% 6/16/02 - G. Penn

% Rewrote map_feats predicates to use arg/3 rather than =../2 to build SVs terms.  Saves
%  structure on the heap.  Also changed u/6 and add_to_type/5 to if_b/2 predicates since
%  driving off the first argument of unify_type/3 automatically sorts them.
% 6/16/02 - G. Penn

% Rewrote functional description component so that any definite clause can be used as a
%  function provided that it has a 'fun name(-,-,..,+).' declaration to identify the
%  result argument position.  The older 'name(Arg1,...,Argn) +++> Result' now implicitly
%  defines an n+1-ary relation 'name(Arg1,...,Argn,Result) if true.'
% 6/18/02 - G. Penn

% Bug corrected: lex/4 compilation was calling fully_deref_prune/6 after lex_close/10,
%  but lex_rule/8 terminates with a call to it already.
% 6/18/02 - G. Penn

% Bug corrected: ord_add_element/3 and ord_intersect/2 were not loaded by ALE.
% 6/18/02 - G. Penn

% Added run-time lex_goal/4 hook to parser (build/3) and generator (non_chain_rule/8).
% 6/18/02 - G. Penn

% Bug corrected: rule/7 generated no code in the absence of PS rules.  compile_rules_act/0 also
%  modified so that rule/7 compilation will still be made, and current_predicate/2 guards on rule/2
%  added where appropriate.
% 6/18/02 - G. Penn

% Bug corrected: fun/1 added to abolished preds in abolish_preds/0.
% 6/20/02 - G. Penn

% Bug corrected: when_type/3 wasn't handling bot correctly when FS was a_/1 atom - now trap bot
%  and don't delay - when_a_/3 needs to push delay into Prolog level if FS is already a_/1 atom, and
%  when_a_chk/3 needs to decompose delay into Prolog delays if FS is already a_/1 atom.  when_eq/3
%  must decompose identical extensionally typed pairs to fire on time.
% 6/23/02 - G. Penn

% Added restriction that a_/1 value restrictions contain acyclic terms.
% 6/24/02 - G. Penn

% Rewrote query_goal/1,5 mechanism to eliminate redundant code, to handle narrow variables in
%  queries properly, for safety with co-routining, and to provide an entry point (query_cond0/4)
%  for co-routining to the source-level debugger.  Now uses a Zip variable to assemble Args list
%  properly in face of co-routining.
% 6/27/02 - G. Penn

% Bug corrected: query_goal0/6 did not dereference FS before add_to/3 call in =/2 clause.
% 6/27/02 - G. Penn

% Bug corrected: compile_cond_desc/11 assumed that FS was exactly FIntro when condition unblocks -
%  we only know FS's type is subsumed by FIntro.
% 6/27/02 - G. Penn

% Pushed inequations into co-routining layer.
% 6/27/02 - G. Penn

% Bug corrected: query_goal0/6 clause for negation did not call query_goal0/6 recursively
%  with enough anonymous arguments.
% 7/8/02 - G. Penn

% Added pp_residue/7 for printing residues.  Rewrote top-level query/1, rec/1, rec/2, rec_best/2,
%  and rec_list/2 to use it.  rec_list/3 now returns bag of soln/2, where second arg is residue.
%  gen/1 and gen/2 now print initial and final categories, with final category linked by
%  duplicate references to residue.
% 7/25/02 - G. Penn

% Bug corrected: split_emptys_rules/4 was looking for rule/? rather than
%  alec_rule/? terms.
% 7/29/02 - G. Penn

% Declared if_h/1,2 multifile (by popular demand).
% 7/30/02 - G. Penn

% Changed ale_debug/1 assertion in end_of_file expansion to assertz/1 call
%  to preserve order of consulted files.
% 8/14/02 - G. Penn

% Bug corrected: ct/4 was binding RHS variable to Cons goal Goal.
% 8/15/02 - G. Penn

% Bug corrected: Calls to query_goal/1 cannot simply instantiate Zip at the end of
%  the call because some suspensions may later unblock and zip the Args lists together
%  differently or bind NBody differently.  Instead, we should use instantiated Zip to
%  indicate that we don't care about argument lists or pretty-printing goal.  Added
%  query_cond/9 clause for bound Zip variable for these cases, and a var(Zip) check for
%  the old one.
% 8/15/02 - G. Penn

% Removed =@ check in constraint bodies.  There's plenty in the body that could go wrong,
%  and we're not going to check for all of it --- too expensive.
% 8/15/02 - G. Penn

% Bug corrected: variables of functional descriptions were unhooked by findall/3.
% 8/31/02 - G. Penn

% Bug corrected: RHS parsing in ct/4 was missing parentheses around goal/2 operator.
% 9/4/02 - G. Penn

% touch/1 modified to check for readable File before creating - in directories
%  with multiple users and badly set default file permissions, the old way resulted
%  in a write-permission error.  The new way is also a bit faster in a compilation
%  chain with  more than one throw.
% 9/6/02 - G. Penn

% Removed fully_deref/4 call from rec_list/3.  Unclear why it was there and not in the
%  other rec_X predicates, and it complicates the code for residuation.
% 9/6/02 - G. Penn

% Bug corrected: added Residue argument to rec/3 and rec/4 - need this because Chart is
%  now on the heap, and needs to be kept outside the scope of call_residue/2.
% 9/6/02 - G. Penn

% Bug corrected: changed the scope of \+\+ in top-level rec_X predicates
%  to keep the co-routining layer free of chart suspensions on exit by query_proceed/0.
% 9/19/02 - G. Penn

% Bug corrected: nv_replace_hook/5 was missing base case for non-narrow variables.
% 9/21/02 - G. Penn

% Added prolog/2 goals, where first argument is an assoc. list of narrow variable replacements.
%  Now if user wants to replace narrow vars in a hook, he can do it himself, so removed call to
%  nv_replace_hook/3.
% 9/29/02 - G. Penn

% Bug corrected: assoc. lists weren't initialised in gen/1 and gen/2.
% 9/29/02 - G. Penn

% Made FreshNVs binding contingent on var(Zip) in query_cond/9.
% 9/29/02 - G. Penn

% Cleaned up compile_ext/2.
% 10/7/02 - G. Penn

% Bug corrected: retract_lex_one/1 could remove wrong (but unifiable) entry - now uses dynamic
%  clause reference, and checks for dynamic declaration.
% 10/10/02 - G. Penn

% Cleaned up residue printing and added it to remaining predicates.  Now we factor out inequations
%  for printing and subsumption checking.
% 10/10/02 - G. Penn

% rule/1 was finding MGSat of mother before those of daughters - switched to stay closer to 
%  parsing semantics.
% 10/10/02 - G. Penn

% Bug corrected: when_a_/3, when_a_chk/3, when_eq0/3 and ineq_disj/4 were not delaying on nonvar(SVs)
%  - can generate exception or error during fully_deref/4 traversal.
% 10/10/02 - G. Penn

% Bug corrected: build_complex_iqs_act/4 did not handle nonvar keys (happens when some but not all
%  disjuncts in a decomposed inequation fail).
% 10/10/02 - G. Penn

% Bug corrected: resgoal_args/3 missing clause for when_eq0/4.
% 10/10/02 - G. Penn

% Changed inequations from ineq(FS1,FS2,Rest) to ineq(Tag1,SVs1,Tag2,SVs2,Rest) to establish
%  invariant whereby suspended inequations only hold between dereferenced structures.
% 10/10/02 - G. Penn

% Removed inequations from extensionalisation code - we couldn't use them anyway.  FSs that
%  exist only in inequations or other suspended goals are still not extensionalised.
% 10/10/02 - G. Penn

% Bug corrected: function result arguments in fun/1 specs identified by + rather than -.
% 10/11/02 - G. Penn

% Eliminated lex_goal/2 in favour of goal/2 hooks on lexical entries and lexical rules.
% 10/11/02 - G. Penn

% Added portray_unif_failure/6, portray_path_failure/5, portray_feat_failure/4,
%  portray_macro_failure/4, portray_addtype_failure/4, portray_undef_type/4, portray_desc_failure/4
%  portray_featpath_failure/5, portray_edge_discard/9, portray_edge_retract/8, portray_incoming_edge/7
%  portray_edge/8, portray_dtr_edge/8, portray_lex/4, portray_type_info/8, portray_mgsat/4,
%  portray_cat/5, portray_ale_goal/2, portray_ale_macro/5, portray_empty/6, portray_lex_rule/10,
%  portray_ale_clause/2, and portray_rule/4 hooks.
% 10/14/02 - G. Penn

% Added error message for when nullary function looks like type.  Added another error message for
%  when function has more than one result argument specified in the same specification.
% 10/17/02 - G. Penn

% Bug corrected: a_/1 atom identity check was made on nullary functions rather than unary functions.
% 11/2/02 - G. Penn

% Removed term_expansion/2 hook for +++>/2 --- now handled by compile_fun_assert/0 and compile_dcs/2.
% Also added warning for overlapping definitions by +++>/2 and if/2.
% 11/2/02 - G. Penn

% Converted passing of end_of_file/0 in term_expansion/2 hook to failure so that other expansion
%  hooks (such as in CHR) can have a crack.
% 11/2/02 - G. Penn

% Bug corrected: lex/1 called lex/4 instead of lex/3.
% 11/15/02 - G. Penn

% Bug corrected: macro/1 was not instantiating the association list, AssocIn.
% 11/18/02 - G. Penn

% Added Dtrs argument to portray_empty/6 hook.
% 11/22/02 - G. Penn

% Added resgoal_args_wgoal/3 to hunt down residue FSs inside delayed goals.
% 11/22/02 - G. Penn

% Added unintroduced feature check to add_to/3.
% 11/22/02 - G. Penn

% Bug corrected: lazy referencing in add_to_type/3 and u/4 violated invariant assumed in
%  when_approp/3 - new structure values must be either variables, or completely well-formed
%  (including appropriateness).  Reprioritised structure-binding in map_mgsat/1 and created
%  new access predicate bind_mgsat/4 to take care of compile-time binding check.
% 11/24/02 - G. Penn

% Bug corrected: compile_dtrs/19 was not threading PGoals properly in case of final remainder/2
%  daughter.
% 11/27/02 - G. Penn

% Changed cats> list error message to reflect that e_list and ne_list are the two valid types
%  of argument.
% 11/27/02 - G. Penn

% Bug corrected: missing cuts in list cases of pp_desc/8.
% 11/27/02 - G. Penn

% Added resgoal_args_wgoal/3 hooks for ud/2,3,4 and deref/3,4, and pp_res_wgoal/8 hooks for
%  ud/2,3,4 and the query_cond/9 prefix added by non-zipped delayed goals.
% 12/2/02 - G. Penn

% Bug corrected: residue_args/3 call in pp_fs_res_col/4 misnamed Ref as Tag.
% 12/2/02 - G. Penn

% Added resgoal_args_wgoal/3 and pp_res_wgoal/8 hooks for when_type/3, and changed spacing
%  in pp_res_wgoal/8 hooks for ud/2,3,4.
% 12/2/02 - G. Penn

% Bug corrected: Added extra argument to filter_goals/3 to add varlist key to frozen goals, in
%  keeping with the format used by call_residue/2.  It might be possible to get rid of these
%  keys in call_residue/2 ASAP rather than do this, since we aren't using them for anything.
% 12/5/02 - G. Penn

% Added cuts to show_rule_dtrs/7 clauses to eliminate useless choice point.
% 12/5/02 - G. Penn

% mgsat warning in add_to/3 was missing a column argument in pp_fs/9 and
%  pp_iqs/8.
% 12/17/02 - G. Penn

% newline added after ENTRY: to display type more appropriately.
% 2/14/03 - G.. Penn

% Bug corrected: compile_lex_act failed in absence of parsing/0 flag.
% 5/10/03 - G. Penn

% Bug corrected: compiler predicates calling compile_body/10 with FS palettes
%  have to separately retract their FS palettes.  Changed retract_fs_palettes/0
%  to retract_fs_palettes/1 and fspal_ref/1 to fspal_ref/2 for indicating the
%  source.
% 5/10/03 - G. Penn

% Bug corrected: FS palette was unhooking lexical goal variables from lexical
%  entry.  Changed lex/3 to lex/2, and now bind FS at run-time when goal
%  variables are instantiated at compile-time.
% 5/26/03 - G. Penn

% Changed if_error/2 to use exception handler for signature compilation error
%  messages.  Other errors use error_msg/1 for now.
% 6/8/03 - G. Penn

% Changed if_warning/2 and if_warning_else_fail/2 to use print_message/2 facility
%  for signature compilation warning messages.
% 6/8/03 - G. Penn

% Changed check for unknown lexical items to breadth-first - now integrated with
%  reverse_count_lex_check/5 (formerly reverse_count/5).
% 6/9/03 - G. Penn

% Changed rec/4 and rec/5 to tabulate solution indices with solution/1.
% 6/9/03 - G. Penn

% Added write_list/2 with explicit stream reference for ale_warning/1 hooks.
% 6/9/03 - G. Penn

% Declared ext/1 as a prefix operator.
% 7/8/03 - G. Penn

% Bug corrected: compile_ext_sub_assert/0 was being called after alec(iso)
%  and alec(check) phases, which need its ext_sub_structs/6 clauses.
% 7/11/03 - G. Penn

% Changed extensional/1 to dynamic predicate.
% 7/11/03 - G. Penn

% Switched to matrix-based signature compiler.
% 7/16/03 - G. Penn

% Changed map_minimal/3 to map_minimal/2 to use new sig compiler.
% 7/16/03 - G. Penn

% Bug corrected: unsatisfiable lex entry message should issue newline after
%  message, not before.
% 7/25/03 - G. Penn

% Bug corrected: approp/3 should call intro/2 to determine whether to add
%  failure clause - ensure_sub_intro/0 guarantees existence of this pred.
% 7/25/03 - G. Penn

% Bug corrected: implicit_mins/1, implicit_maxs/1 and unary_branch/2 warnings
%  did not have ALE wrapper.
% 7/25/03 - G. Penn

% Added no_lex/0 exception for rec/4,5 when no lexicon exists.
% 7/25/03 - G. Penn

% Exception handling added for run-time rec/1,2, lex/1, rec_list/2 and
%  rec_best/2 calls.
% 7/25/03 - G. Penn

% Updated maximal/1 to new signature compiler.
% 7/29/03 - G. Penn

% Changed matrix-based signature compiler to ZCQ data structure
% 8/5/03 - G. Penn

% Moved call_det/2 here from debugger/interp.pl to replace exactly_once/3
%  implementation.  Changed duplicate_ext/2 to duplicate_ext/1.
% 8/5/03 - G. Penn

% Bug corrected: unary_branch/2 was using immed_subtypes/2 as if it were
%  transitively closed.
% 8/10/03 - G. Penn

% Bug corrected: immed_subtypes/2 and imm_sub_type/2 did not behave properly on a_/1
%  atoms.
% 8/10/03 - G. Penn

% Modified maximal/1 to take variable arguments
% 8/11/03 - G. Penn

% Changed ZCQ representation to manditorily use variables as 0 matrices, and
%  to copy structure during multiplication.  This allows us to implement
%  matrix sum as term unification.
% 8/20/03 - G. Penn

% Bug corrected: now use enumerator on first arg of sub_type/2 to avoid duplicate answers.
% 9/6/03 - G. Penn

% Changed type/1 clauses in compile_cond_desc/11 and query_cond_desc/5 to non_a_type/1 - a_/1
%  atoms are already trapped.
% 9/6/03 - G. Penn

% Changed when_type0/3, when_type_delayed0/4 and when_eq_act/5 to use unify_type/3 rather than
%  sub_type/2, because of new signature compiler.  Also optimised when_type/3 for non-variable
%  arguments, changed treatment of a_/1 atoms slightly in when_eq_act/5, and replaced
%  variable-binding in when_eq/3 with delays.
% 9/6/03 - G. Penn

% Folded constraints into ct/3, and now call enforce_constraints/2 in logic code.
% 9/6/03 - G. Penn

% Bug corrected: feature/1 must call setof/3 outside scope of disjunction between sub-intro
%  and intro declarations.
% 9/7/03 - G. Penn

% Folded deref into new add_to_typed/2,3 and featvald/3,4 predicates in description
%  compilation.
% 9/7/03 - G. Penn

% ud/4,5,6 and u/4 symmetrically closed to speed up unification - next to no
%  change in compile times (earlier problem was with space, now seems to have
%  been corrected by SP 3.10.1).
% 9/7/03 - G. Penn

% Bug corrected: bot + a_/1 atom unification clause not added when symmetric
%  closure was made.
% 9/28/03 - G. Penn

% Bug corrected: edge_act/7 could not handle no answers from query_proceed properly.
% 10/10/03 - G. Penn

% Bug corrected: query_discard_act/11 not updated when edge_act/7 was changed
%  to failure-driven.
% 10/11/03 - G. Penn

% Bug corrected: add_to_typed_a_ was mistyped as add_to_type_ad_ in
%  compile_desc/10.
% 10/15/03 - G. Penn

% Added exceptions ill_cond/1, ill_cond_desc/2, undef_cond_feat/2, undef_feat/1,
% undef_type/1, undef_macro/1, and ill_desc/1.
% 10/26/03 - G. Penn

% Type2 wasn't bound for no_lub/3 exception in unify_type_range/7.
% 11/1/03 - G. Penn

% Bug corrected: base cases of vars_merge/3 predicates were passing mode
%  through instead of changing to tricky.
% 11/10/03 - G. Penn

% Added 3-place and 4-place vesions of ineq/2.
% 11/10/03 - G. Penn

% Bug corrected: compile_body/10 must compile antecedents of shallow cuts
%  and negated goals with CBSafe = false.
% 11/10/03 - G. Penn

% Added new description compiler with implicit variables and hooks for (shortly)
%  adding mode.
% 11/24/03 - G. Penn

% United flags and switches into ale_flag/2,3 predicates.
% 11/24/03 - G. Penn

% Added multifile declarations for flag_modes/2 and ale_flag_msg/3.
% 11/29/03 - G. Penn

% Bug corrected: IVars was being unthreaded by the delay on CBSafe protecting ivar_unseen/7.
%  Pushed delay in to the point in ivar_unseen/7 where CBSafe actually matters so that now
%  only Goals is unthreaded.
% 12/4/03 - G. Penn

% Bug corrected: FSatF was not being registered as seen in feat:val clause of compile_cond_desc/11.
% 12/4/03 - G. Penn

% Bug corrected: SeenFlag was serving double-duty as flag for Var and FS in variable clause
%  of compile_cond_desc/11.
% 12/4/03 - G. Penn

% Added peephole optimizer to description compiler.  Currently, two optimisations are supported:
%   add_type(Path,t1) ---> X
%   add_type(Path,t2) ---> add_type(Path,unify(t1,t2))
% and
%   add_type(Path,t)         ---> X
%   <instr>([...,f|Path],... ---> unchanged, where subtype(t,intro(f))
% 12/7/03 - G. Penn

% Bug corrected: rconvert_stm/5 and variants need cuts in their 0-indexed clauses to eliminate
%  needless choicepoints on sparse (uninstantiated) cases.
% 12/7/03 - G. Penn

% Bug corrected: ->/2 mistyped as =/2 in compile_cond_desc/11.
% 12/7/03 - G. Penn

% Added check for uninstantiated feature to add_to/3, flatten_desc/5 and serial_desc/7.
% 1/7/04 - G. Penn

% Added mode to description compiler.
% 1/11/04 - G. Penn

% Added mode checking to conditional compilation.
% 1/13/04 - G. Penn

% Optimized when_type/3, when_type0/3 and when_type_delayed0/4.
% 1/13/04 - G. Penn

% Modified compile_cond_desc/13 to throw undef_feat/1 exception when
%  unrecognised feature is used in conditional.
% 3/2/04 - G. Penn

% Bug corrected: abolish((when_approp)/3) added to compile_dcs_act.
% 3/22/04 - G. Penn

% Partially optimised when_approp/3 (now when_approp/2) and cleaned up extensional
%  case of when_eq_act/5.
% 3/22/04 - G. Penn

% Bug corrected: a_/1 clause removed from when_approp/2.
% 4/14/04 - G. Penn

% Added positional rule indexing to leftmost daughters of rules (as
%  try_rule/7).
% 4/20/04 - G. Penn

% Added intensional variable to data structure for type-delaying.
% 5/26/04 - G. Penn

% Switched to attributed variables in place of reference chains.
% 6/9/04 - G. Penn

% Rewrote extensionalisation code to correct numerous bugs.
% 6/13/04 - G. Penn

% Switched from explicit ud/2 calls to verify_attributes/2 hooks.
% 6/18/04 - G. Penn

% Removed redundant instantiation of Type in first arg of tfs/1 in add_to_typeact/6 and
%  featval_act/8.
% 6/25/04 - G. Penn

% Moved a_/1 atoms to Prolog terms.  bot-typed feature structures must now only be attributed
%  when delayed upon.
% 6/25/04 - G. Penn

% Moved feature values out of attributes.  Graph colouring minimizes the arity of the resulting term.
% 7/1/04 - G. Penn

% Feature values restricted to the value restriction of the feature's introducer are left unspecified
%  in MGSats, and lazily filled in when variables are bound to them.
% 7/1/04 - G. Penn

% Changed sort_desc_type/9 so that Fill type is bot when the existence of a path must be asserted, but
%  the type at its terminus adds no new information.  Modified generate_instr/8 not to generate an
%  add_to_type goal when Type is bot.
% 7/5/04 - G. Penn

% Bug corrected: marity/2 should not be defined for a_/1 module.
% 7/5/04 - G. Penn

% Bug corrected: mode-related failures in compile_cond_list/10 need to be
%  protected.
% 7/8/04 - G. Penn

% Bug corrected: no_types_defined ALE warning wasn't wrapped with ale/1.
% 7/9/04 - G. Penn

% Bug corrected: compile_cond/9 calls must be protected from mode failure
%  (even when not in disjunctions), because they are equivalent to true/0,
%  not fail/0.  Added cond_failure/2 warning to flag unsatisfiable conditions.
% 7/9/04 - G. Penn

% Bug corrected: when write_term/2 is called within a format/3 call on the
%  user_error stream, write_term/2 must not specify user_error, or else
%  output is printed twice.
% 7/9/04 - G. Penn

% deref/4 now multi-hashed.
% 7/16/04 - G. Penn

% Bug corrected: Useless u/6 clauses created when Type1 has no module, and Type2
%  does have a module, but is not the key for that module.
% 7/16/04 - G. Penn

% Removed attributed variables for maximally typed TFSs.
% 7/16/04 - G. Penn

% Added mgsat flag for offline expansion of MGSats.
% 8/4/04 - G. Penn

% Removed featval compilation - now only used in interpreted descriptions.  Replaced
%  in compiled code with arg/3 calls.  Also now add implicit type promotion from feature
%  paths as explicit instructions during serialisation so that more instructions can be
%  discarded.
% 8/9/04 - G. Penn

% Bug corrected: path_mod/6 now tracks which features must be filled along entire feature path.
% 8/9/04 - G. Penn

% Removed bot translation on add_to_type/4 - first arg is now a type.
% 8/12/04 - G. Penn

% Rewrote add_to/6 to lazily fill introduced feature values.
% 8/12/04 - G. Penn

% Added "unfilling," an optimisation in which the final feature value along a path is not
%  filled if the operation performed by the current instruction would accomplish the same.
% 9/20/04 - G. Penn

% Bug corrected: fss_merge/3 was not labelling tricky FSs as such if one FS list was longer than
%  the other.
% 9/26/04 - G. Penn

% Removed mode-threading from sort_desc/11 (now 10) - it never changes.
% 9/26/04 - G. Penn

% Changed FSs to assoc lists, added mode-checking and added assert_empty_assoc/1 to enforce
%  prohibition on FSs in constraints, if/2 clauses etc.
% 10/11/04 - G. Penn

% Bug corrected: replace_hook_fss_act/10 was recursing on non-TFS attributed variables.
% 10/26/04 - G. Penn

% Made mode checking sensitive to compile-time-bound TFSs.
% 10/28/04 - G. Penn

% Bug corrected: added try_rule/6 clause for when no PS rules exist.
% 3/21/05 - G. Penn

% Changed portray_unif_failure/6 to portray_unif_failure/4.
% 3/21/05 - G. Penn

% Eliminated portray_undef_type/4 and portray_desc_failure/4 --- these can be handled by exceptions
%  undef_type/1 and ill_desc/1.
% 3/28/05 - G. Penn

% Added attribute_goal/2 hook to convert attributes to goals in the tfs/2 and tfs/4 attributed
%  data structures.
% 4/22/05 - G. Penn

% Bug corrected: one of the subsume_type/13 calls in subsume/9 was passing Tag, SVs, ETag and
%  ESVs in the wrong order.
% 4/24/05 - G. Penn

% Bug corrected: subsume/9 is sometimes called by predicates that would not fail on mutual
%  incomparability.  So it now protects its unification checks with \+ \+ to avoid passing
%  their side effects on.
% 4/25/05 - G. Penn

% Decremented arity of portray_edge_discard/9, portray_edge_retract/8, portray_incoming_edge/7
%  portray_dtr_edge/8, portray_path_failure/5, portray_feat_feailure/4, portray_macro_failure/4,
%  portray_addtype_failure/3, portray_featpath_failure/5, portray_lex/4, portray_mgsat/4,
%  portray_cat/5, portray_ale_macro/5, portray_empty/7, portray_lex_rule/10, portray_rule/4
%  and portray_edge/8 for new data structure.
% 5/1/05 - G. Penn

% Added get_vals/2 for interface to pretty-printer.  Really, at this point we should
%  be compiling out recursive calls.
% 5/8/05 - G. Penn

% Added FS fourth argument to when_type_delayed/3 for pretty-printing.  This is probably going
%  to slow delays down, but prob. not by much provided that the delayed goal references this
%  FS anyway.
% 5/8/05 - G. Penn

% Redundant clause for when_type/3 removed from resgoal_args_wgoal/3.
% 5/11/05 - G. Penn

% Bug corrected: retract_fs_palettes/1 call was commented out for PS rules.
% 5/29/05 - G. Penn

% Ported generator and pretty-printer to attributed data structure.
% 5/29/05 - G. Penn

% Added extra argument to portray_fs/10, portray_mgsat/3 and print_fs/9 to communicate context of
%  mgsat types.
% 5/31/05 - G. Penn

% Bug corrected: changed build_iqs/3 to build_iqs_restore_atts/3, which rehooks ALE attributes back
%  onto their variables.  call_residue/2 strips them off.  An alternative would be to fetch the
%  the inequations manually rather than with call_residue/2.
% 5/31/05 - G. Penn

% Added infer_mgsat_type/3 to establish type context for lazy variables in
%  top-level queries.  This requires an implementation of generalise/3 -
%  the dual of unification.
% 5/31/05 - G. Penn

% Built extensionality into attributed data structure, and removed extensionalise/1 and
%  extensionalise_list/1 calls.
% 6/15/05 - G. Penn

% Bug corrected: fs_to_mode/7 could not build mode structures for a_/1 atoms.
% 6/18/05 - G. Penn

% if/3 in macro clause of add_to/2 changed back (see 7/7/98) to shallow cut -
%  backtracking here is inconsistent with the behaviour of the description
%  compiler, in which first matching macro definition is the only one allowed.
%  This kind of default reasoning is preferred because: 1) it doesn't exist
%  elsewhere in ALE descriptions (except in functions with cuts), and 2) macros
%  can expand to disjunctive descriptions when backtracing is required.
% As a result, removed findall/3 from macro clause of infer_mgsat_type/3.
% 7/5/05 - G. Penn

% Bug corrected: added utype_module_pair_visited/2 table to record uncovered-covered
%  pairs for uact/9.  Was doing this before by requiring Type2 = Module2, but this
%  won't work for some non-principal filters depending on the choice of module key.
% 7/5/05 - G. Penn

% Bug corrected: SICStus Prolog discards any attribute in which the first argument
%  is 0.
% 8/11/05 - G. Penn

% Bug corrected: changed operator precedence of cons/2 and other ALE source-code
%  predicates to 1125 - makes it easier to detect bugs when attachments like morphs/2
%  are misplaced, and places them below discontiguous/1 and other compile-time
%  declarations.  Exception is intro/2 - that's 1115, because it can either occur
%  by itself or inside sub/2.  Also removed then/2.
% 9/3/05 - G. Penn

% Added abolish_user_preds/1 hook to abolish_preds/0 and compiler preds.  Can be called
%  with arguments all, sig, cons, grammar, dcs, or fun.  When called with all, the hook
%  must perform the work of the other options, if desired.  Every hook clause is called
%  in a failure-driven loop.
% 2/17/06 - G. Penn

% Added hooks for major compiler stages: compile_gram_hook/0, compile_sig_hook/0,
%  compile_fun_hook/0, compile_cons_hook/0, compile_dcs_hook/0, compile_grammar_hook/0.
%  Every hook clause is called in a failure-driven loop. When compile_gram/0 is called,
%  *all* of these are called; compile_gram_hook/0 is called last.
% 2/17/06 - G. Penn

% Added meta-pred call_all/1, to use with compiler hooks.
% 2/17/06 - G. Penn

% Bug corrected: filter_goals/4 was stripping off trigger goals.
% 2/19/06 - G. Penn

% Added get_feat/3 access predicate.
% 5/7/06 - G. Penn

% Added portray_resgoal/7 hook for printing residuated goals.
% 5/8/06 - G. Penn

% Bug corrected: pathval/7 defined with one extra, unnecessary argument
%  (returning the VType at the end of a given path).
% 5/8/06 - G. Penn

% Bug corrected: frozen_term/2 was hanging on variable terms.
% 6/25/06 - G. Penn

% Spiffed up query_proceed/0.
% 6/26/06 - G. Penn

% Split the use of num/1 as a compile-time index generator and run-time edge
%  counter into two counters, index/1 and edgenum/2.  The second arg of
%  edgenum/2 is an edge limit, controlled through new ale_flag/2 edgelimit.
%  When edge limit is exceeded, an exception is raised to stop chart
%  construction.  Added build_exn/1 to catch this exception.
% 6/26/06 - G. Penn

% Added a clear_hook/0 - clauses called in a failure driven loop.
% 6/26/06 - G. Penn

% Bug corrected: compiler hook predicates must live inside the corresponding
%  _act/0 call.
% 7/12/06 - G. Penn

% Added debugger flag.
% 7/20/06 - G. Penn

% Bug corrected: compile_mgsc_act/0 was abolishing mgsc/7 instead of mgsc/5.
% 7/21/06 - G. Penn

% Bug corrected: for some reason, call_residue/2 isn't trapping the '$put_attributes'/2
%  goals left by rec/1 and lex/1.  This probably has something to do with our use of
%  attribute_goal/2.  Added \+\+ to lex/1 to suppress the printing of these.
% 7/26/06 - G. Penn

% Bug corrected: mode-tracker was carrying around variables from a_/1 atom
%  arguments, even through disjunctions, co-routined code, etc.  Now we
%  copy the term before updating mode.  This loses some information about
%  variable binding (meaning that mode will be a less accurate, but still
%  valid approximation).
% 8/8/06 - G. Penn

% Added chart_init_hook/0 [now chart_init_hook/2].
% 8/13/06 - G. Penn

% Added edge_assert_hook/6.
% 8/27/06 - G. Penn

% Bug corrected: Term-copying solution to 8/8/06 bug correction was updating
%  type/3 abstract machine instructions with updated mode.  Now we generate
%  two instructions: one for filling, and one for the original type.  Also
%  modified the peephole optimizer to combine cases like these only when
%  both types are ground/1 or one type is bot.
% 8/19/06 - G. Penn

% Bug corrected: build_exn/1 was calling raise/1 instead of raise_exception/1.
% 8/30/06 - G. Penn

% Added soln/2 and edgenum/1 (to replace num/1), edge/3, edge/4, edge/5 and
%  edge/7.  Changed print_edgeout/8 to print_asserted_edge_act/8,
%  edge_act/7 to print_asserted_edge_act/7, query_edgeout/8 to query_asserted_edge/8,
%  and write_out/2 to write_parsing_substring/2.
% 9/8/06 - G. Penn

% Bug corrected: query_asserted_edge/8 displayed the 'retract' option even for
%  empty categories (which can't be retracted).
% 9/8/06 - G. Penn

% Added lexical universals (forall/2).
% 9/10/06 - G. Penn

% Bug corrected: need to use ebagof/3 for apply_forall_lex/2 compiler directive in
%  case there are no forall ---> clauses.  Also added current predicate guards to
%  apply_forall_lex/2 and forall_lex/3 directives.
% 9/11/06 - G. Penn

% Added time to compute descriptions to time argument of rec/5.
% 9/13/06 - G. Penn

% Added rule universals (forall/2).
% 11/6/06 - G. Penn

% Bug corrected: rule/1 didn't place \+\+ at a wide enough scope.
% 11/13/06 - G. Penn

% Bug corrected: sort_desc_instr/11 was using sub_type/2 to eliminate code
%  even when the type to be added was an a_/1 atom with uninstantiated variables.
%  In this case, we still need to add the type in order to bind those vars (unless
%  they're singletons, which is an optimization that hasn't been added yet for ALE
%  vars or Prolog vars inside a_/1 atoms - presumably they should be added together).
% 11/15/06 - G. Penn

% Bug corrected: warning/1 postfix operator was defined, but not implemented.
% 11/30/06 - G. Penn

% Bug corrected: map_module_basis/1 could be stumped by the order in which types
%   were considered in building modules.
% 11/30/06 - G. Penn

% Bug corrected: forall_rule/4 missed clause for no forall ... rule when forall ... lex
%   exists.
% 1/23/07 - G. Penn

% Added Index argument to rec/5 (now rec/6) and portray_cat/4 (now portray_cat/5).
% 3/1/07 - G. Penn

% Bug corrected: added guard to forall_lex/3 to check for forall ---> clauses.
% 3/2/07 - G. Penn

% Bug corrected: try_rule/6 was generating choice points for rules that don't compile.
%  Now we multi-hash rule/6 first, tabulate which ones compiled (as rule_compiled/1),
%  and then create choice points only for those in try_rule/6.
% 6/4/07 - G. Penn

% Bug corrected: lexicon clause of try_rule/6 was not using rule_compiled/1.
% 6/7/07 - G. Penn

% Bug corrected: resgoal_args_wgoal/3 and pp_res_wgoal/8 were not filtering out when/2
%  switches, and were not handling arg/3 calls specially.
% 6/7/07 - G. Penn

% Bug corrected: ivars_merge was calling ord_intersection/3 to merge implicit variable
%  stores, but we need a union that performs unification on identically keyed values.
% 6/9/07 - G. Penn

% Bug corrected: compile_body/12 was not properly recovering from subcompilation failures detected
%  by type modes in the case of shallow cuts, disjunctions and negations by failure.
% 7/13/07 - G. Penn

% Added warning messages for subcompilation and DCS clause compilation failures.  Also changed
%  compilation of disjunctions and shallow cuts to recompile with the right context in case
%  of subcompilation failures.
% 7/13/07 - G. Penn

% Added get_edge_ref/6 - a version of get_edge/7 that uses asserted edges rather than the chart copy
%  on the heap.
% 9/11/07 - G. Penn

% Bug corrected: uact/9 was not calling ATGoal when Type2 is moduled and maximal,
%  and Type1 is not moduled.
% 7/7/08 - G. Penn

% Bug corrected: type_noadd/2 (now /3) ande featpath_noadd/3 (now /4) exceptions were not passing
%  the type context to properly render their FS arguments.
% 7/10/08 - G. Penn

% Bug corrected: error_msg/1 should not be called by alex/1.  Defined a new tell_user_error/1
%  for this.
% 7/10/08 - G. Penn

% Added terminate_alex/1 to provide better control over how exception handling terminates.
% 7/10/08 - G. Penn

% Added .alec_throw wrapper to compile_fun/0.  Even though we don't need it, a compile_fun_hook/0
%  might.
% 8/12/08 - G. Penn

% Incorporated subtype-covering constraints and subtypecover compiler flag.  Refactored
%  map_mgsat/1.
% 8/12/08 - G. Penn

% Bug corrected: uact/9 was not sending the proper update through Int1 - when Type2 is moduled and
%  Type1 is not, the corresponding clause of u/6 does not know the resulting type at compile-time.
%  Looks like we have to do a second dereference in this case to look up the result.  The only
%  alternative I see would be to add a result type arg to add_to_type/4.
% 8/18/08 - G. Penn

% Refactored uact/9 again to share common code generated by different cases.
% 8/18/08 - G. Penn

% Bug corrected: missing bot,bot clause in add_to_typeact/5 was causing co-routined predicates
%  to be lost by binding to a bot MGSat that has no attributes.
% 8/19/08 - G. Penn

% Bug corrected: fixed a mistake with PostGoals binding introduced by the refactorization of 8/18/08.
% 8/19/08 - G. Penn

% Bug corrected: generate_apply_forall_rule/8 (now generate_apply_forall_rule/10) was not threading FSs and MFS
%  to track compile-time daughters seen only by variables bound in forall/2 rule statements.
% 8/19/08 - G. Penn

% Bug corrected: "then" compilation of shallow cuts was not preserving state if "if" compilation failed
%  in if-then-else clauses of compile_body/12.
% 8/21/08 - G. Penn

% Bug corrected: goal_list_to_seq/2 must delay on its first argument because ivar_unseen/8 delays
%  its Goal output on CBSafe.
% 8/22/08 - G. Penn

% Bug corrected: subsume_type/14 was not being compiled because multi_hash spec was subsume_type/13.
% 8/28/08 - G. Penn

% Bug corrected: subsume_type/14 wrongly conflated bot and 0 cases - the former does not depend on
%  the value of the context restriction Restr.
% 8/28/08 - G. Penn

% Bug corrected: ivars_merge/3 needs to intersect paths, unifying their implicit variables.  A union
%  does not guarantee that every implicit variable in the AVL has been bound to its path.
% 9/23/08 - G. Penn

% Renamed terminate_alex/1 to recoverable_ale_exception/1, and made this and ale_exception/1 multifile.
% 9/25/08 - G. Penn

% Renamed strip_keys/2 to strip_keys_filter_subrhs/2.
% 1/22/09 - G. Penn

% Bug corrected: add_to_typeact/5 was generating code that could go into infinite loops
% on non-modularized types in presence of constraints that select sub-types.
% 4/22/09 - G. Penn

% Rewrote approp/3 compiler to make a single call to unify_types/2.
% 7/12/09 - G. Penn

% Changed introduce/2 to a compile-time asserted dynamic predicate.
% 7/12/09 - G. Penn

% Rewrote daughter store threading for forall_rule/4 in order to eliminate its add_to/2 call.
% 7/12/09 - G. Penn

% Added wpreds so that Prolog compiler sees more delayed code.
% 7/13/09 - G. Penn

% Added ruleindex flag.
% 7/13/09 - G. Penn

% Added ruleindexscope flag
% 7/13/09 - G. Penn

% Added forall_hook/2 (for PS rules only for now).
% 7/16/09 - G. Penn

% Added Cond and its arguments to (now) portray_lex_rule/10.  Also added RuleName
% and DtrsDesc to (now) portray_rule/5.
% 5/3/10 - M. Lazarov(?), modified by G. Penn

% Bug corrected: missing apply_forall_lex/2 call in term_expansion/2 clause for
%  update_lex/1.
% 7/5/10 - G. Penn

% Added compile_list_access/0.
% 7/5/10 - G. Penn

% Refactored lexicon and lex_rule compilation predicates to use lex_desc_goal/4
%  and add_lex/5.
% 7/5/10 - G. Penn

% Bug corrected: declared write_type/0 and write_feat/0 as operators.
% 8/9/10 - G. Penn

% Bug corrected: must protect empty/0 with a double negation.
% 8/10/10 - G. Penn

% reverse_count_lex_check/5 (now /6) aggregates all of the unknown words first, and
%  then raises all of them as a list in a single exception.  Also changed the ALE
%  exception unk_word/1 to unk_words/1.
% 8/10/10 - G. Penn

% Bug corrected: query_goal was threading description variables to detect duplicates in
%  several cases, as if query/1 portrays descriptions in its output.  It probably should,
%  but does not.  For now, we thread real FS arguments.
% 8/11/10 - G. Penn

% Changed ale_flag/3 to iterate through all ale_flags/1 clauses, which are now multifile.
% 8/12/10 - G. Penn

% Bug corrected: add_to/6 must unify ungrounded a_/1 types even the added type subsumes the FS's.
% 8/12/10 - G. Penn

% Bug corrected: ale/1 should not raise exceptions on description failures.
%  We now toggle the adderrs flag.
% 8/12/10 - G. Penn

% Bug corrected: rule/1 was not taking EFD closure prefixes into account.
% 8/12/10 - G. Penn

% Changed message for adderrs flag to something that does not suggest that this is
%  just a flag that controls pretty-printing.
% 8/12/10 - G. Penn

% Bug corrected: the (remainder(RFS),Rest) case of match_cat_to_next_cat/10 was dropping Rest when
%  RFS is an ne_list.
% 6/10/11 - G. Penn

% Bug corrected: transposed MSVs2/I2 and MSVs1/NewI1 in the < clause of unify_mfs_unif_comp/16.
% 5/21/12 - G. Penn

% Bug corrected: wpred variables were being unhooked because leaf-to-root call paths are not
%  enough to capture external variable dependencies.  Now, we track prior and continuant variables
%  to each call.
% 5/25/12 - G. Penn

% Replaced map_max/3 with unify_types/2 in generalise/3.
% 5/28/12 - G. Penn

% Added access predicates featvald/5 and get_type/3
% 5/30/12 - G. Penn

% Unthreaded Dups and replaced with Inf(ormative) association list for sparse output.  Added
%  sparseoutput ale_flag.
% 6/3/12 - G. Penn

% Bug corrected: a few remaining duplicates/7 calls had not been updated to the new sparse
%  output data structure.
% 7/21/13 - G. Penn

% Bug corrected: apply_forall_lex/2 must precede tabulation of lexical FSs into the palette, because
%  it can further instantiate the data structure.
% 8/1/13 - G. Penn

% Added macro multiple define warnings, as part of a new 'verifying macros' compilation step.  This
%  also cleans up the way macro declarations were handled (formerly in the compiling functions step).
% 3/14/14 - G. Penn

% Bug corrected: base cases of ord_merge/3 were incorrect, leading to unbound implicit variables
%  in some compiled disjunctive descriptions.
% 4/1/14 - G. Penn

% Bug corrected: forall lex rules should be applied to the base lexical entries before they
%  are fed to lexical rules.
% 4/7/14 - G. Penn

% Added support for forall lex_rule clauses, including lexicalize/2, which
%  fuses morphological patterns into a lexical atom.
% 4/8/14 - G. Penn

% Bug corrected: missing cut in morph_chars/3.
% 4/8/14 - G. Penn

% Updated generator with new portray_fs_in_window/4 hook.
% 4/10/14 - G. Penn

% NOTE: must resolve whether to close empty cat's under lexical rules
% Perhaps we should add an option to the interpreter to "go," stopping only
%   at subsumption-based assert/retract decisions
% Add check for cut-free goals in PS rules - they take scope over rule code,
%  and are prohibited in the manual
% Add benchmarking code written for Kathy B.
% Add named empty categories
% Add proc. attachments to lexical entries (and empty cats, macros?)
% Add more compile-time checking of compatibility
%  in things like rules, relations, lexical rules and constraints (things that
%  compile to code instead of FS's).  These should disable with the new user
%  control predicates also.
% Add list (and other) pretty-printer.
% Add statistical scoring mechanism.
% Make mini-interpreter record lexical rule and lexical origins of derived
%  lexical entries in chart
% Add subsumes/2 built-in to relational language/Prolog

% Make sure to reflect these changes in source-level debugger where approp.
% Aggregate type info in descriptions at each node in order to avoid redundant
%  type inferencing in compiled code - prob. other optimizations are possible
%  too, although must be balanced against transparency of description
%  execution.
% Also compile extensionalise further and everywhere else that functor and
%  arg are used
% remove check_inequal
% maybe add assert option to get around hard limit on number of vars. in 
%  compiled predicates - ultimately should do something better like 
%  automatically detecting when limit is exceeded and adding clauses like 
%  add_to_type3 and featval/4.  The hard limit is actually on temporary 
%  variables.
% get rid of compile_desc/6 - probably will have to change DS to do this right
%  in order to get featval to return a split Tag,SVs
% add indexing mechanism for generation lexicon and parsing chart.  Also
%  index first arguments of definite clauses by type.

% RCS banners
% $Id: ale.pl,v 1.9 1998/07/16 16:50:02 gpenn Exp gpenn $
%
% $Log: ale.pl,v $
% Revision 1.9  1998/07/16 16:50:02  gpenn
% 3.1 beta bug patches
%
% Revision 1.7  1998/03/07 18:38:30  gpenn
% Bug corrections, internal notes
% Stripped out version bannering
% mini-interpreter now always carries dtr and rule info
% match_list bug corrected
% more warnings, removed some unused code
% now turns off character_escapes
% placed compile_iso and compile_check under compile_extensional
% translated abolish/2 calls to abolish/1 ISO standard
%
% Revision 1.6  1997/10/23 15:47:45  gpenn
% Added parsing and generating modes.  Still handles only one
% grammar per session.  ale_gen.pl and ale_parse.pl can glue two
% sessions together for translation.
%
% Revision 1.5  1997/09/27 21:43:36  gpenn
% Added edge subsumption w/ interpreter interface, functional
% descriptions, autonomous intro declaration, default declarations
% for maximal types and types immediately subsumed by bottom.
% Also cleaned up interpreter, and modified treatment of atoms to
% allow non-ground terms.
%
% Revision 1.4  1997/06/10 19:07:57  octav
% Added sem_goal> tags.
%
% Revision 1.2  1997/05/05 19:54:00  gpenn
% bug fix of 1.1
%

:- multifile file_search_path/2.
:- dynamic file_search_path/2.
:- prolog_load_context(directory,AleHome),
   assert(file_search_path(ale_home,AleHome)).

:- multifile portray_message/2.
:- dynamic ale_compiling/1, ale_debugging/0, ale_debug/1, lexicon_updating/0.

% SHOULD MAKE THIS MODULE-SPECIFIC
portray_message(warning,no_match(abolish(_))). % suppress abolish/1 warnings
portray_message(warning,ale(Msg)) :-
  format(user_error,'{ALE: Warning: ',[]),
  ale_warning(Msg),
  format(user_error,'}~n',[]),
  flush_output(user_error).

portray_message(informational,M) :-            
  portray_message_inf(M).

:- discontiguous portray_message_inf/1.

portray_message_inf(loading(_Depth,_Mode,AbsFileName)) :-
  ale_compiling(AbsFileName),   % suppress compiler throws
  !.				
portray_message_inf(loaded(_Depth,_Mode,AbsFileName,user,_,_)) :-
  ale_compiling(AbsFileName),
  !.
% for backwards compat with older SICStus versions
portray_message_inf(loading(_,AbsFileName)) :-
  ale_compiling(AbsFileName).
portray_message_inf(loaded(_,AbsFileName,user,_,_)) :-
  ale_compiling(AbsFileName).

term_expansion_eof(Code) :-
  prolog_load_context(file,File),
  (clause(ale_compiling(File),true) -> % current_stream(File,_,S),
                                    % seek(S,-1,current,_), % reset end_of_file
                                    alec_catch(Code)
  ; clause(ale_debugging,true) -> assertz(ale_debug(File)),
                                  fail % Code = end_of_file
  ).

term_expansion_lex(['--->'(WordStart,DescOrGoal),
                    (:- multifile (lex)/2),
                    (:- dynamic (lex)/2)|Code],WordStart,DescOrGoal) :-
  lexicon_updating, secret_noadderrs(OldMode),
  bagof((lex(Word,FS) :- Body),(add_lex(WordStart,DescOrGoal,Word,FS,Goals),
			        goal_list_to_seq(Goals,Body)),Code),
  secret_adderrs(OldMode).

:- use_module(library(ordsets),[ord_union/3,ord_intersection/3,ord_add_element/3,
				ord_intersect/2,ord_subtract/3,ord_union/4]).

:- prolog_flag(version,Version),
   name(Version,VersionName),
   ( VersionName = [83, 73, 67, 83, 116, 117, 115, 32|SICStusVersion]
     -> ( SICStusVersion = [52|_] -> ensure_loaded(ale4diff) % "SICStus 4" 
        ; SICStusVersion = [51|_] -> ensure_loaded(ale3diff) % "SICStus 3"
        )
   ; VersionName = [83,87,73,45,80,114,111,108,111,103|_] % "SWI-Prolog"
     -> true
   ).

:- prolog:'$save_attribute_info'(user).

% the when_type/3 goals delay on the Int var hiding in type attribute - this hook fishes them out
%  for frozen/2 and call_residue/2.  Be careful to call frozen/2 on only the Int var - sometimes there
%  is a Loopback var, too.  The delay var, when it exists, might have suspensions, but this position exists
%  outside the attribute, too, so we'll already have those.
% KNOWN BUG: for some reason, these show up both in the residue and in the top-level
%  when call_residue/2 is used.
%attribute_goal(AttVar,('$put_attributes'(AttVar,Att),IntGoal)) :-
%  '$get_attributes'(AttVar,Att,_),
%  nonvar(Att),
%  functor(Att,tfs,N),  % make sure this is an ALE attribute
%  arg(N,Att,Int),  % N is either 2 or 4
%  frozen(Int,IntGoal).

attribute_goal(AttVar,'$put_attributes'(AttVar,Att)) :-
  '$get_attributes'(AttVar,Att,_).
%  nonvar(Att),
%  functor(Att,tfs,_N).  % make sure this is an ALE attribute
%  arg(N,Att,Int),  % N is either 2 or 4
%  frozen(Int,_IntGoal).

:- multifile if_b/2, if_h/2, if_h/1.

:- discontiguous if_h/1.
:- discontiguous if_h/2.
:- discontiguous if_b/2.

:- dynamic ale_flag/2.

ale_flag(Flags,_,_) :-
  var(Flags),
  !,ale_flags(Flags).
ale_flag(Flag,OldMode,NewMode) :-
  if((ale_flags(Flags),member(Flag,Flags)),
     (clause(ale_flag(Flag,OldMode),true),
      ( var(NewMode) -> raise_exception(instantiation_error(ale_flag(Flag,OldMode,NewMode),3))
      ; OldMode == NewMode -> true
      ; flag_mode(Flag,NewMode) -> retract(ale_flag(Flag,OldMode)),
	                           assert(ale_flag(Flag,NewMode)),
	                           print_message(informational,ale_flag_msg(Flag,NewMode))
      ; flag_modes(Flag,Modes),
        raise_exception(domain_error(ale_flag(Flag,OldMode,NewMode),3,Modes,NewMode))
      )
     ),
     raise_exception(domain_error(ale_flag(Flag,OldMode,NewMode),1,Flags,Flag))).

:- multifile ale_flags/1.
ale_flags([pscompiling,lexicon,psrules,interp,subtest,residue,adderrs,mgsat,edgelimit,debugger,subtypecover,
           ruleindex,ruleindexscope,debuglex,sparseoutput,another]).

flag_mode(edgelimit,Mode) :-
  !,( integer(Mode) -> Mode >= 0
    ; Mode = inf
    ).
flag_mode(Flag,Mode) :-
  flag_modes(Flag,Modes),
  member(Mode,Modes).

:- multifile flag_modes/2.
flag_modes(pscompiling,[parse,generate,parse_and_gen]).
flag_modes(lexicon,[consult,compile]).
flag_modes(psrules,[consult,compile]).
flag_modes(interp,[on,off]).
flag_modes(subtest,[on,off]).
flag_modes(residue,[show,hide]).
flag_modes(adderrs,[on,off]).
flag_modes(mgsat,[online,offline]).
flag_modes(debugger,[on,off]).
flag_modes(subtypecover,[on,off]).
flag_modes(edgelimit,'non-negative integer').
flag_modes(ruleindex,[off,leftmost]).
flag_modes(ruleindexscope,[point,localtree,localresolve]).
flag_modes(debuglex,[on,off]).
flag_modes(sparseoutput,[on,off]).
flag_modes(another,[query,autoconfirm]).

parsing :- ale_flag(pscompiling,Mode),
	   (Mode = parse ; Mode = parse_and_gen).
generating :- ale_flag(pscompiling,Mode),
	   (Mode = generate ; Mode = parse_and_gen).

portray_message_inf(ale_flag_msg(Flag,Mode)) :-
  ale_flag_msg(Flag,Mode,Msg),
  nl(user_error),write(user_error,Msg),
  nl(user_error).

:- multifile ale_flag_msg/3.
ale_flag_msg(pscompiling,parse,'{ALE: compiler will produce code for parsing only}').
ale_flag_msg(pscompiling,generate,'{ALE: compiler will produce code for generation only}').
ale_flag_msg(pscompiling,parse_and_gen,'{ALE: compiler will produce code for parsing and generation}').
ale_flag_msg(lexicon,consult,'{ALE: compiler will consult lexicon}').
ale_flag_msg(lexicon,compile,'{ALE: compiler will compile lexicon}').
ale_flag_msg(psrules,consult,'{ALE: compiler will consult phrase structure rules}').
ale_flag_msg(psrules,compile,'{ALE: compiler will compile phrase structure rules}').
ale_flag_msg(interp,on,'{ALE: chart interpreter is active}').
ale_flag_msg(interp,off,'{ALE: chart interpreter is inactive}').
ale_flag_msg(subtest,on,'{ALE: parser will test edges/empty categories for subsumption}').
ale_flag_msg(subtest,off,'{ALE: parser will not test edges/empty categories for subsumption}'). 
ale_flag_msg(residue,show,'{ALE: blocked goals will be displayed}').
ale_flag_msg(residue,hide,'{ALE: blocked goals will not be displayed}').
ale_flag_msg(adderrs,off,'{ALE: failure to add a description will not generate exceptions}').
ale_flag_msg(adderrs,on,'{ALE: failure to add a description will generate exceptions}').
ale_flag_msg(mgsat,online,'{ALE: most general satisfiers will be computed online}').
ale_flag_msg(mgsat,offline,'{ALE: most general satisfiers will be computed offline}').
ale_flag_msg(debugger,on,'{ALE: source-level debugger is active}') :-
  initialise_ale_sld.
ale_flag_msg(debugger,off,'{ALE: source-level debugger is inactive}').
ale_flag_msg(debuglex,on,'{ALE: source-level debugger will step through lexical rules/entries}') :-
  initialise_ale_sld.
ale_flag_msg(debuglex,off,'{ALE: source-level debugger will not step through lexical rules/entries}').
ale_flag_msg(subtypecover,on,'{ALE: signature compiler will assume subtype covering}') :-
  ensure_loaded(ale_home('stcover.pl')).
  % Really, we should recompile the signature if one has been compiled before this.
ale_flag_msg(subtypecover,off,'{ALE: signature compiler will not assume subtype covering}').
ale_flag_msg(ruleindex,off,'{ALE: compiler will not index phrase structure rules for parser}').
ale_flag_msg(ruleindex,leftmost,'{ALE: compiler will index leftmost daughters of phrase structure rules for parser}').
ale_flag_msg(ruleindexscope,point,'{ALE: compiler will check overlapping categories during indexation}').
ale_flag_msg(ruleindexscope,localtree,'{ALE: compiler will check all categories and goal descriptions of local trees during indexation}').
ale_flag_msg(ruleindexscope,localresolve,'{ALE: compiler will check all categories and execute goals of local trees during indexation}').
ale_flag_msg(sparseoutput,on,'{ALE: only those portions of feature structures that cannot be inferred from appropriateness will be displayed}').
ale_flag_msg(sparseoutput,off,'{ALE: all feature substructures will be displayed regardless of whether they can be inferred from appropriateness}').
ale_flag_msg(another,query,'{ALE: parsing and other commands will ask whether you want to see another solution}').
ale_flag_msg(another,autoconfirm,'{ALE: parsing and other commands will assume you always want to see another solution}').

initialise_ale_sld :- ensure_loaded(ale_home('debugger.pl')).

initialise_ale_flags :-
  assert(ale_flag(interp,off)),
  assert(ale_flag(subtest,off)),
  assert(ale_flag(pscompiling,parse)),
  assert(ale_flag(residue,hide)),
  assert(ale_flag(lexicon,consult)),
  assert(ale_flag(psrules,compile)),
  assert(ale_flag(adderrs,on)),
  assert(ale_flag(mgsat,online)),
  assert(ale_flag(debugger,off)),
  assert(ale_flag(subtypecover,off)),
  assert(ale_flag(edgelimit,inf)),
  assert(ale_flag(ruleindex,leftmost)),
  assert(ale_flag(ruleindexscope,point)),
  assert(ale_flag(debuglex,off)),
  assert(ale_flag(sparseoutput,off)),
  assert(ale_flag(another,query)).

portray_message_inf(ale_deprec(Old,New)) :-
  nl(user_error),
  write(user_error,'{ALE: '),
  write(user_error,Old),
  write(user_error,' is deprecated - use '),
  write(user_error,New),
  write(user_error,'}'),
  nl(user_error).

clear :-
%  retractall(tick(_,_,_)), % DEBUG
  retractall(to_rebuild(_)),
  retractall(solution(_)),
  retractall(edge(_,_,_,_,_,_,_)),
  retractall(parsing(_)),
  clear_edgenum, % edge index
  retractall(go(_)),  % interpreter go flag
  ( current_predicate(clear_hook,clear_hook) -> call_all(clear_hook) ; true).

secret_noadderrs_toggle(Mode) :-
  retract(ale_flag(adderrs,on)) -> Mode = on,
                                   ( assert(ale_flag(adderrs,off))
				   ; retract(ale_flag(adderrs,off)),
				     assert(ale_flag(adderrs,on)),
				     fail
				   )
  ; ( Mode = off
    ; fail
    ).

secret_adderrs_toggle(off).
secret_adderrs_toggle(on) :-
  retract(ale_flag(adderrs,off)),
  assert(ale_flag(adderrs,on))
  ; retract(ale_flag(adderrs,on)),
    assert(ale_flag(adderrs,off)),
    fail.

secret_noadderrs(Mode) :-
  retract(ale_flag(adderrs,on)) -> Mode = on,
                                   assert(ale_flag(adderrs,off))
  ; Mode = off.

secret_adderrs(off).
secret_adderrs(on) :-
  retract(ale_flag(adderrs,off)),
  assert(ale_flag(adderrs,on)).

% ==============================================================================
% Operators
% ==============================================================================

% ------------------------------------------------------------------------------
% SRK Descriptions
% ------------------------------------------------------------------------------
:-op(600,fx,a_).  % formerly 375
:-op(375,fx,@).
:-op(700,xfx,=@).
%:-op(700,xfx,==).
:-op(775,fx,=\=).
%:-op(800,xfy,:).  % now use standard 550
%:-op(1000,xfy,',').
%:-op(1100,xfy,';').

% ------------------------------------------------------------------------------
% Signatures
% ------------------------------------------------------------------------------

:-op(800,xfx,goal).
:-op(1125,xfx,cons). % was 900
:-op(1115,xfx,intro).
:-op(1125,xfx,sub).
:-op(1125,fx,ext).

% ------------------------------------------------------------------------------
% Grammars
% ------------------------------------------------------------------------------
%:-op(1125,xfy,then). - don't know what this was for, but isn't used now.
:-op(1120,xfx,===>).
:-op(1125,xfx,--->).
:-op(1125,xfx,macro).
:-op(1125,xfx,+++>).
:-op(1125,fx,fun).
:-op(1125,fx,empty).
:-op(1125,xfx,rule).
:-op(1125,xfx,lex_rule).
:-op(1115,xfx,morphs).
:-op(1105,xfx,'**>').
:-op(950,xfx,when).
:-op(900,xfx,becomes).
:-op(900,xfx,became).
% 5/1/96 Octav - added operator for semantics/1 predicate
:-op(1125,fx,semantics).

% ------------------------------------------------------------------------------
% Universals
% ------------------------------------------------------------------------------
:-op(1135,xfx,forall).
:-op(1135,xfx,forall_hook).
:-op(1130,xfx,do).

% ------------------------------------------------------------------------------
% Definite Clauses
% ------------------------------------------------------------------------------
:-op(1110,xfx,if).

% ------------------------------------------------------------------------------
% Compiler
% ------------------------------------------------------------------------------
:-op(800,xfx,if_h).
:-op(800,xf,if_h).
:-op(800,xfx,if_b).
:-op(800,xf,if_b).
:-op(800,xfx,if_error).   
:-op(800,xfx,if_warning_else_fail).   
:-op(800,xfx,if_warning).
:-op(800,xfx,new_if_warning_else_fail).   
:-op(800,xfx,new_if_warning).
:-op(800,xf,warning).

% ------------------------------------------------------------------------------
% I/O
% ------------------------------------------------------------------------------
:-op(1125,fx,mgsat).
:-op(1100,fx,macro).
:-op(1100,fx,query).
:-op(1100,fx,rule).
:-op(1100,fx,lex_rule).
:-op(1100,fx,show_clause).
:-op(1100,fx,rec).
:-op(1100,fx,lex).
:-op(1100,fx,gen).
:-op(800,fx,show_type).
:-op(500,fx,write_type).
:-op(500,fx,write_feat).  
:-op(500,fx,no_write_type).
:-op(500,fx,no_write_feat).  


% ==============================================================================
% Type Inheritance and Unification
% ==============================================================================

% Type:<type> sub Types:<type>s intro FRs:<fv>s                             user
% ------------------------------------------------------------------------------
% Types is set of immediate subtypes of Types and FRs is list
% of appropriate features paired with restrictions on values.
% When FRs is not specified, it is equivalent to '[]'.
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% Type:<type> cons Cons:<desc> goal Goal:<goal>                             user
% ------------------------------------------------------------------------------
% Cons is the general description which must be satisfied by all structures of
%  type Type, and Goal is an optional procedural attachment which also must
%  be satisfied when present.  An absent constraint is equivalent to 'bot', 
%  and an absent goal is equivalent to 'true'.
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% type(?Type:<type>)                                                        eval
% ------------------------------------------------------------------------------
% Type is a type.  Enumerated in topological order.
% ------------------------------------------------------------------------------
type(bot).  % KNOWN BUG: this leaves a choice point on calls with bot or a_/1 
type(a_ _). %  atoms
type(T) :- 
  current_predicate(type_num,type_num(_,_)),
  clause(type_num(T,_),true).

bot_trans(bot,0).
bot_trans(bot,bot):- !. % for SICStus-internal reasons, we must allow 0 for bot.
bot_trans(T,T).

zero_trans(0,bot) :- !.
zero_trans(T,T).

% for lazy variables --- we interpret 0 in the context of value restriction R as R.
zero_trans(0,R,R) :- !.
zero_trans(T,_,T).

% ------------------------------------------------------------------------------
% non_a_type(?Type:<type>)                                                  eval
% ------------------------------------------------------------------------------
% Type is a type other than a a_/1 atom.  Enumerated in topological order.
% ------------------------------------------------------------------------------
non_a_type(bot).
non_a_type(T) :-
  non_a_bot_type(T).

non_bot_type(a_ _).
non_bot_type(T) :-
  non_a_bot_type(T).

non_a_bot_type(T) :-
  current_predicate(type_num,type_num(_,_)),
  clause(type_num(T,_),true).

% ------------------------------------------------------------------------------
% immed_subtypes(?Type:<type>, ?SubTypes:<type>s)                           eval
% ------------------------------------------------------------------------------
% SubTypes is set of immediate subtypes of Type (but SubTypes do not cover Type)
% ------------------------------------------------------------------------------
% KNOWN BUG: this assumes there are no chords in the user's sub/2 declaration
immed_subtypes(T,SubTypes) :-
  type(T),
  immed_subtypes_act(T,SubTypes).
  
immed_subtypes_act(a_ X,SubTypes) :-
  !,( ground(X) -> SubTypes = []
    ; when(nonvar(SubTypes),immed_subtypes_a_(SubTypes,X))
    ).
immed_subtypes_act(bot,[(a_ _)|SubTypes]) :-
  !, ( current_predicate(sub,(_ sub _))
     -> ( (bot sub SubTypes intro _) -> true
        ; (bot sub SubTypes) -> true
        ; SubTypes = []
        )
     ; SubTypes = []
     ).
immed_subtypes_act(Type,SubTypes):-
  current_predicate(sub,(_ sub _))
  -> ( (Type sub SubTypes intro _) -> true
     ; (Type sub SubTypes) -> true
     ; SubTypes = []
     )
  ; SubTypes = [].

% immed_subtypes_a_([],_) fails - non_ground a_/1 atoms have infinitely many immed subtypes
immed_subtypes_a_([T|SubTypes],X) :-
  when(nonvar(T),imm_sub_type_a_(T,X)),
  when(nonvar(SubTypes),immed_subtypes_a_(SubTypes,X)).
  
% ------------------------------------------------------------------------------
% imm_sub_type(?Type:<type>, ?TypeSub:<type>)                               eval
% ------------------------------------------------------------------------------
% TypeSub is immediate subtype of Type 
% ------------------------------------------------------------------------------
imm_sub_type(Type,TypeSub):-
  non_a_type(Type),
  immed_subtypes(Type,TypeSubs),
  member(TypeSub,TypeSubs).
imm_sub_type(a_ X,T) :-
  when(nonvar(T),imm_sub_type_a_(T,X)). % cannot enumerate a_/1 atom immediate subtypes

imm_sub_type_a_(a_ Y,X) :-
  variant(X,Y) -> fail  
  ; \+ \+ (term_variables(X,XVars),
           subsumes(X,Y),
           length(XVars,PreLen),
           sort(XVars,PostXVarsList), % the subsumes/2 call may have bound vars
           elim_nonvars(PostXVarsList,PostXVars),
           length(PostXVars,PostLen),
           PostLen =:= PreLen - 1).  % *immediate* subtype => one change is allowed

elim_nonvars([],[]).
elim_nonvars([X|L],Vars) :-
  var(X) -> Vars = [X|LVars], elim_nonvars(L,LVars)
  ; Vars = [].  % because first arg is sorted, nonvars come after vars

% ------------------------------------------------------------------------------
% immed_cons(?Type:<type>, ?Cons:<desc>)                                    eval
% ------------------------------------------------------------------------------
immed_cons(Type,Cons,Goal) :-  
  type(Type),               % KNOWN BUG: ALE WON'T CATCH A CONSTRAINT DEFINED FOR
  (current_predicate(cons,(_ cons _))  %  AN ATOM UNTIL THE COMPILER IS RUN
   -> ((Type cons Cons goal Goal) -> true ; (Type cons Cons), Goal = true)
   ; Cons = none, Goal = none).
  
% ------------------------------------------------------------------------------
% sub_type(Type:<type>, TypeSub:<type>)                                     eval
% ------------------------------------------------------------------------------
% TypeSub is subtype of Type
% ------------------------------------------------------------------------------
sub_type(T,S) :-
  type(T),
  sub_type_ind(T,S).

sub_type_ind((a_ X),S) :-
  !,( var(S) -> S = (a_ X)   % KNOWN BUG: if T is a_/1 atom, S does not
                             %  iterate through its specializations.
    ; (S = (a_ Y)), subsumeschk(X,Y)
    ).  
sub_type_ind(T,S) :-
  unify_type(T,S,S).

% ------------------------------------------------------------------------------
% unify_type(Type1:<type>, Type2:<type>, TypeLUB:<type>)                   mh(1)
% ------------------------------------------------------------------------------
% The least upper bound of Type1 and Type2 is TypeLUB.
% ------------------------------------------------------------------------------
(unify_type(bot,T,T) if_h [type(T)]).  
(unify_type(a_ X,bot,a_ X) if_h).  % a_/1 cases
(unify_type(a_ X,a_ X,a_ X) if_h).
(unify_type(Arg1,Arg2,TypeLUB) if_h) :-
  clause(stmatrix_dim(Dim),true),
  for_loop(1,N1,Dim),
    clause(stmatrix_num(N1,Row1),true),  % for each row of the subtype matrix...
    clause(num_type(N1,Type1),true),
    ( Arg1 = Type1, TypeLUB = Type1,
      ( Arg2 = bot                       % bot case
      ; Arg2 = Type1                     % reflexive case
      )
    ; arg(2,Row1,Row1Rest), functor(Row1Rest,'.',2), % SP4: arg/3 throws exception when 2nd arg is atom
      arg(1,Row1Rest,Next),  % test for subtypes and joins
      N1Plus1 is N1 + 1,
      unify_type_range(N1Plus1,Next,Arg1,Arg2,TypeLUB,Type1,Row1Rest)
    ).

% ------------------------------------------------------------------------------
% unify_type_range(+N:<int>,+Next:<int>,-Arg1:<type>,-Arg2:<type>,-TypeLUB:<type>,
%                  +Type1:<type>,+Row1:<types>s)
% ------------------------------------------------------------------------------
% The least upper bound of Arg1 and Arg2 is TypeLUB, one of Arg1 or Arg2 is
%  Type1, and the other is numbered N or higher in the topological order.
%  Row1 consists of all subtypes of Type1 numbered Next or higher in the
%  topological order.
% This predicate is used to enumerate types that are join-compatible with Type1,
%  by iteratively testing every type numbered between the first and last subtypes
%  of Type1 (in topological order).  Types numbered prior to the first will have
%  already been handled by symmetric closure in their row.  Types numbered after
%  the last cannot be join-compatible, because joins are subtypes, and therefore
%  occur prior to (or equal with) the last.
% ------------------------------------------------------------------------------
unify_type_range(N,N,Arg1,Arg2,TypeLUB,Type1,Row) :-
  !,clause(num_type(N,Type2),true),  % subtype case
  ( TypeLUB = Type2, ( Arg1 = Type1, Arg2 = Type2
                     ; Arg2 = Type1, Arg1 = Type2)
  ; arg(2,Row,RowRest), functor(RowRest,'.',2), arg(1,RowRest,Next),
    NPlus1 is N + 1,
    unify_type_range(NPlus1,Next,Arg1,Arg2,TypeLUB,Type1,RowRest)
  ).
unify_type_range(N2,_Next,Arg1,Arg2,TypeLUB,Type1,Row1) :-
  clause(stmatrix_num(N2,Row2),true),
  ord_intersection(Row1,Row2,RowLUB), % join reduction case
  functor(RowLUB,'.',2), arg(1,RowLUB,NLUB),	% if empty, then fail - not compatible
  clause(num_type(N2,Type2),true),
  ( clause(stmatrix_num(NLUB,RowLUB),true)  % ow. first should be minimal
  -> clause(num_type(NLUB,TypeLUB),true),
     ( Arg1 = Type1, Arg2 = Type2  
     ; Arg1 = Type2, Arg2 = Type1     % symmetric closure
     )
  ; map_minimal(RowLUB,Mins),  % if it isn't minimal, then this is not MSL
    raise_exception(ale(no_lub(Type1,Type2,Mins)))
  ).
unify_type_range(N2,Next,Arg1,Arg2,TypeLUB,Type1,Row) :-
  N2Plus1 is N2 + 1,  % try next element in range
  unify_type_range(N2Plus1,Next,Arg1,Arg2,TypeLUB,Type1,Row).


% ------------------------------------------------------------------------------
% for_loop(+Begin:<int>,-Var,+End:<int>)                                   
% ------------------------------------------------------------------------------
% Iteratively bind Var to every integer between Begin and End (inclusively).
% ------------------------------------------------------------------------------
for_loop(Begin,Begin,_End).
for_loop(Begin,Var,End) :-
  End > Begin,
  NewBegin is Begin + 1,
  for_loop(NewBegin,Var,End).

% ------------------------------------------------------------------------------
% map_minimal(+Ss:<types>, ?SsMin:<types>)                                 
% ------------------------------------------------------------------------------
% SsMin is the list of minimal types of Ss, i.e., every element of SsMin
%  belongs to Ss, and there is no element of Ss that is less than it in the
%  topological order.  Ss must be topological sorted.
% ------------------------------------------------------------------------------
map_minimal([],[]).
map_minimal([N|Ns],[T|Mins]) :-
  clause(num_type(N,T),true),        % assume topological order, so N is min
  clause(stmatrix_num(N,RowN),true), % RowN are the subtypes of N
  ord_subtract(Ns,RowN,NewNs),       % so get rid of them
  map_minimal(NewNs,Mins).

% ------------------------------------------------------------------------------
% unify_types(+Types:<type>s, ?Type:<type>)                                 eval
% ------------------------------------------------------------------------------
% Type is the least upper bound of Types.
% ------------------------------------------------------------------------------
unify_types([],bot).
unify_types([Type|Types],TypeUnif):-
  unify_types(Types,Type,TypeUnif).

% ------------------------------------------------------------------------------
% unify_types(+Types:<type>s, +Type:<type>, ?TypeUnif:<type>)              
% ------------------------------------------------------------------------------
% TypeUnif is unification of set consisting of Types and Type.
% ------------------------------------------------------------------------------
unify_types([],Type,Type).
unify_types([Type|Types],TypeIn,TypeOut):-
  unify_type(Type,TypeIn,TypeMid),
  unify_types(Types,TypeMid,TypeOut).

% ------------------------------------------------------------------------------
% maximal(?Type:<type>)                                                     eval
% ------------------------------------------------------------------------------
% Type is a maximally specific type.
% ------------------------------------------------------------------------------
maximal(Type) :-
  type(Type),
  maximal_act(Type).

maximal_act(a_ X) :- 
  !,ground(X).
% bot is never maximal, because of a_/1 atoms.
maximal_act(Type) :-
  clause(type_num(Type,N),true),
  clause(stmatrix_num(N,Row),true),
  arg(2,Row,[]).

% ------------------------------------------------------------------------------
% join_reducible(?Type)                                                     eval
% join_reducible(?Type,?Type1,?Type2)
% ------------------------------------------------------------------------------
% Type is join_reducible (to Type1 and Type2).
% ------------------------------------------------------------------------------
join_reducible(Type) :-
  \+ \+ join_reducible(Type,_,_).
	
join_reducible(Type,Type1,Type2) :-
  sub_type(Type1,Type),  \+ variant(Type1,Type),
  sub_type(Type2,Type),  \+ variant(Type2,Type),
  unify_type(Type1,Type2,Type).

% ------------------------------------------------------------------------------
% non_join_pres(?Type,?F)                                                   eval
% ------------------------------------------------------------------------------
% Join preservation (appropriateness homomorphism condition) fails at Type for
%  feature F.
% ------------------------------------------------------------------------------
non_join_pres(Type,F) :-
  \+ \+ non_join_pres(Type,F,_,_).

non_join_pres(Type,F,S1,S2) :-
  unify_type(S1,S2,Type),
  approp(F,Type,T3),
  ( approp(F,S1,T1)
  -> ( approp(F,S2,T2)      % F is appropriate to both S1 and S2
     -> unify_type(T1,T2,T1UnifyT2),
        \+sub_type(T3,T1UnifyT2)   % must check with sub_type/2 because 
                                   %   of a_/1 atoms
     ; \+sub_type(T3,T1)    % F is appropriate to S1 only
     )
   ; ( approp(F,S2,T2)      
     -> \+sub_type(T3,T2)   % F is appropriate to S2 only
      ; fail                % F is appropriate to neither - doesn't matter
     )
  ).

% ------------------------------------------------------------------------------
% unary_branch(?T, ?Type)                                                   eval
% ------------------------------------------------------------------------------
% There is a unary branch from T to Type.
% ------------------------------------------------------------------------------
unary_branch(T,Type) :-
  non_a_type(T),
  immed_subtypes(T,[Type]). % Type is the only sub-type of T.

% ------------------------------------------------------------------------------
% generalise(+Type1:<type>,+Type2:<type>,?TypeGen:<type>)
% ------------------------------------------------------------------------------
% The meet of Type1 and Type2
% ------------------------------------------------------------------------------
generalise(bot,a_ _,bot) :- !.
generalise(a_ _,bot,bot) :- !.
generalise(a_ X,a_ Y,a_ Z) :-
  !,term_subsumer(X,Y,Z).
generalise(Type1,Type2,TypeGLB) :-
  findall(TypeLB,(sub_type(TypeLB,Type1),
                  sub_type(TypeLB,Type2)),TypeLBs),
  unify_types(TypeLBs,TypeGLB).

% ------------------------------------------------------------------------------
% extensional(?Sort:<sort)                                               dynamic
% ------------------------------------------------------------------------------
% Sort is an extensional sort.  Extensional sorts must be maximal.
% Created by compile_extensional.
% ------------------------------------------------------------------------------
:- dynamic extensional/1.

% ==============================================================================
% Appropriateness
% ==============================================================================

% ------------------------------------------------------------------------------
% feature(F:<feat>)
% ------------------------------------------------------------------------------
% holds if $F$ is a feature mentioned somewhere in the code
% ------------------------------------------------------------------------------
feature(Feat):-
  setof(F,Type^Subs^R^FRs^( current_predicate(sub,(_ sub _)),
			    (Type sub Subs intro FRs),
                            member(F:R,FRs)
			  ; current_predicate(intro,(_ intro _)),
	                    (Type intro FRs),
			    member(F:R,FRs)
			  ),Feats), % findall/3 plus sort/2 might be faster here
  member(Feat,Feats).

% ------------------------------------------------------------------------------
% restricts(Type:<type>, Feat:<feat>, TypeRestr:<type>)                     eval
% ------------------------------------------------------------------------------
% Type introduces the feature Feat imposing value restriction TypeRestr 
% ------------------------------------------------------------------------------
restricts(Type,Feat,TypeRestr):-
  current_predicate(sub,(_ sub _)),
  (Type sub _ intro FRs),
  member(Feat:TypeRestr,FRs).
restricts(Type,Feat,TypeRestr):-
  current_predicate(intro,(_ intro _)),
  (Type intro FRs),
  member(Feat:TypeRestr,FRs).

% ------------------------------------------------------------------------------
% introduce(?Feat:<feat>, -Type:<type>)                                     eval
% ------------------------------------------------------------------------------
% Type is the most general type appropriate for Feat
% ------------------------------------------------------------------------------
% This is now compiled and asserted by compile_introduce_assert/0.
%introduce(Feat,Type):-
%  setof(N,TypeRestr^T^(restricts(T,Feat,TypeRestr),
%		       clause(type_num(T,N),true)),TypeNums),
%  map_minimal(TypeNums,TypesMin),
%  ( arg(2,TypesMin,[]) -> arg(1,TypesMin,Type)
%  ; raise_exception(ale(feat_intro(Feat,TypesMin)))
%  ).
     
% ------------------------------------------------------------------------------
% approp(Feat:<feat>, Type:<type>, TypeRestr:<type>)                       mh(1)
% ------------------------------------------------------------------------------
% approp(Feat,Type) = TypeRestr
% ------------------------------------------------------------------------------
(approp(Feat,Type,ValRestr) if_h) :-
  setof(TypeRestr,TypeSubs^(sub_type(TypeSubs,Type),
                            restricts(TypeSubs,Feat,TypeRestr)),
        TypeRestrs),
  ( unify_types(TypeRestrs,ValRestr) -> true
  ; raise_exception(ale(upward_closure(Feat,Type,TypeRestrs)))
  ).
  
approp(_,_,_) if_h [fail] :-
  ( current_predicate(sub,(_ sub _)) -> \+ (_ sub _ intro _)
  ; true),
  ( current_predicate(intro,(_ intro _)) -> \+ (_ intro _)
  ; true).

% ------------------------------------------------------------------------------
% approps(Type:<type>, FRs:<feat_val>s)                                     eval
% ------------------------------------------------------------------------------
% FRs is list of appropriateness declarations for Type
% ------------------------------------------------------------------------------
approps(0,[],0) if_b [].  % attributed representation of bot
approps(Type,FRs,N) if_b [] :-
  type(Type),  % ALE WON'T CATCH FEATURES DEFINED FOR ATOMS UNTIL COMPILER RUNS
  esetof(Feat:TypeRestr, approp(Feat,Type,TypeRestr), FRs),
  length(FRs,N).

% ------------------------------------------------------------------------------
% approp_feats(Type:<type>,Fs:<feat>s)
% ------------------------------------------------------------------------------
% Fs is list of appropriate features for Type
% ------------------------------------------------------------------------------
approp_feats(Type,Fs) :-
  type(Type), % ALE WON'T CATCH FEATURES DEFINED FOR ATOMS UNTIL COMPILER RUNS 
  esetof(Feat,TypeRestr^approp(Feat,Type,TypeRestr),Fs).

% ------------------------------------------------------------------------------
% fatomic(?Type:<type>)
% ------------------------------------------------------------------------------
% Type has no appropriate features
% ------------------------------------------------------------------------------
fatomic(Type) :-
  approps(Type,[],_0).

% ==============================================================================
% Feature Structure Unification
% ==============================================================================

% ------------------------------------------------------------------------------
% ud(FS1:<fs>, FS2:<fs>, IqsIn:<ineq>s, IqsOut:<ineq>s)                     eval
% ------------------------------------------------------------------------------
% unifies FS1 and FS2 (after dereferencing); 
% ------------------------------------------------------------------------------
%ud(FS,FS).

verify_attributes(FS1,FS2,PostGoals) :-
  '$get_attributes'(FS1,TFS1,Type1),
  (var(FS2) -> '$get_attributes'(FS2,TFS2,Type2),
%               tick(Type1,Type2), % DEBUG
               u(Type1,Type2,TFS1,TFS2,FS2,PostGoals)
  ; %get_type(FS2,Type2),  % DEBUG
    %tick(Type1,Type2),
    u(Type1,FS2,TFS1,_,FS2,PostGoals)
  ).

tick(T1,T2) :- % DEBUG
  ( retract(tick(T1,T2,N)) -> NewN is N + 1
  ; NewN = 1
  ),
  assert(tick(T1,T2,NewN)).

% deref
deref(FS,TFS,Type,PosOrFS) if_b [var(FS),!,PosOrFS = FS,'$get_attributes'(PosOrFS,TFS,Type)].
deref(a_ X,_,a_ X,_) if_b [].
deref(FS,TFS,Type,PosOrFS) if_b SubGoals :-
  clause(marity(Module,Arity),true),
  functor(FS,Module,Arity),
  ( maximal(Module) -> Type = Module, TFS = FS, SubGoals = []
  ; arg(1,FS,PosOrFS), SubGoals = [( var(PosOrFS) -> '$get_attributes'(PosOrFS,TFS,Type)
				   ; functor(PosOrFS,Type,_), TFS = FS
				   )]
  ).

% ------------------------------------------------------------------------------
% u(SVs1:<svs>,SVs2:<svs>,Ref1:<ref>,Ref2:<ref>,IqsIn:<ineq>s,
%   IqsOut:<ineqs>)                                                        mh(2)
% ------------------------------------------------------------------------------
% compiles typed version of the Martelli and Montanari unification
% algorithm for dereferenced feature structures Ref1-SVs1 and Ref2-SVs2 
% ------------------------------------------------------------------------------
u(0,N2,TFS1,TFS2,FS2,PostGoals) if_b PreGoals:-
  type(Type2), Type3 = Type2, % handle 0-clauses separately to avoid discontiguities under multi_hash/4
  uact(Type3,TFS1,TFS2,FS2,bot,Type2,N2,PreGoals,PostGoals).
u(_,_,_,_,_,_) if_b _ :- retractall(utype_module_pair_visited(_,_)), fail.
u(Type1,N2,TFS1,TFS2,FS2,PostGoals) if_b PreGoals:-
  unify_type(Type1,Type2,Type3),
  atom(Type1),  % a_/1 handled by Prolog (but it could be Type2 when bot is delayed)
  uact(Type3,TFS1,TFS2,FS2,Type1,Type2,N2,PreGoals,PostGoals).
%u(a_ X,a_ X,_,_,_,_,[]) if_b [].     % must put this here b/c of if_b/2.
   % don't need to delete or copy attributes here - FS2 always wins with verify_attributes/3.
%u(a_ X,0,TFS1,tfs(_0,Int2),_,FS2,[Int2 = (a_ X)]) if_b ['$put_attributes'(FS2,TFS1)].
   % this one now either calls no hook, or calls a hook with the arguments in reverse order

% ------------------------------------------------------------------------------
% uact(Type3,SVs1,SVs2,Ref1,Ref2,Type1,Type2,IqsIn,IqsOut,SubGoals)
% ------------------------------------------------------------------------------
% SubGoals is list of goals required to unify Ref1-SVs1 and Ref2-SVs2,
% where Ref1-SVs1 is of type Type1, Ref2-SVs2 is of type Type2 and
% Type1 unify Type2 = Type3
% ------------------------------------------------------------------------------
uact(a_ X,tfs(_botorNew,Int1),_,_,bot,(a_ X),(a_ X),[],[Int1 = (a_ X)]) :- !.
   % don't need to delete or copy attributes here - FS2 always wins with verify_attributes/3.
uact(Type2,TFS1,_TFS2,_FS2,Type1,Type2,N2,PreGoals,PostGoals):-  % both Type1 and Type2 belong to a module
  clause(tmodule(Type1,_),true), clause(tmodule(Type2,_),true),
  maximal(Type2),  % bot can never be maximal because of a_/1 atoms
  !, ( clause(extensional(Type2),true) -> functor(N2,Type2,0)  
     ; functor(N2,Type2,1), arg(1,N2,_Intensional)             
     ),
  TFS1 = tfs(_,_,_Delay1,Int1),
  PreGoals = [],
  PostGoals = [Int1=Type2].
uact(Type3,TFS1,TFS2,FS2,Type1,Type2,N2,PreGoals,PostGoals):-  % both Type1 and Type2 belong to a module
  % As a result, what the hook is really unifying are the TypePos's of these two FSs, since they have the atts
  clause(tmodule(Type1,_),true), clause(tmodule(Type2,_),true),
  !,Type2 = N2,  % Type2 cannot be bot
  functor(TFS1,tfs,4), arg(4,TFS1,Int1),
  functor(TFS2,tfs,4), arg(4,TFS2,Int2),
  ( Type1 == Type2 -> PreGoals = [], Int1 = Int2, PostGoals = []
  ; Type2 == Type3 -> functor(W,Type2,1), arg(1,W,Int2), arg(3,TFS1,Delay1), arg(3,TFS2,Delay2),
                      PreGoals = [], PostGoals = [Int1=W]
  ; Type1 == Type3 -> functor(W,Type1,1), arg(1,W,Int1), arg(3,TFS1,Delay1), arg(3,TFS2,Delay2),
                      PreGoals = ['$put_attributes'(FS2,TFS1)],
                      PostGoals = [Int2=W]
  ; ( maximal(Type3) -> ( clause(extensional(Type3),true) -> functor(FS3,Type3,0)
  		        ; functor(FS3,Type3,1), arg(1,FS3,_Intensional)
		        ),
                        PreGoals = ['$delete_attributes'(FS2), FS2 = FS3],
                        ConsGoalsRest = [Int1 = Type3, Int2 = Int1],
                        UGoals = [(Delay1=max)|FeatGoals]
    ; TFS3 = tfs(Type3,LoopBack2,Delay2,Int3),
      PreGoals = ['$put_attributes'(FS2,TFS3)],
      functor(W,Type3,1), arg(1,W,Int3),
      ConsGoalsRest = [Int1 = W, Int2 = Int1],
      UGoals = FeatGoals
    ),
    arg(2,TFS2,LoopBack2), arg(3,TFS2,Delay2), arg(3,TFS1,Delay1),
    PostGoals = [DelayedGoal],
    approps(Type1,FRs1,_), approps(Type2,FRs2,_), approps(Type3,FRs3,_),
    map_feats_unif(FRs1,FRs2,FRs3,LoopBack2,FeatGoals,ConsGoals),
    ucons(Type3,Type2,Type1,ConsTypes),
    ( ConsTypes == []
    ->	( ale_flag(subtypecover,on)
	->  ( clause(deranged_maps(Type3,_),true)
	    -> ConsGoals = [stc_maps_init(Type3,LoopBack2)|ConsGoalsRest]
	    ; ConsGoals = ConsGoalsRest
	    )
	; ConsGoals = ConsGoalsRest
	)
    ; ( ale_flag(subtypecover,on)
      -> ( clause(deranged_maps(Type3,_),true)
	 -> ConsGoals = [enforce_constraints(ConsTypes,LoopBack2),
		         stc_maps_init(Type3,LoopBack2)|ConsGoalsRest]
% add deranged type map-checks to code stream after cons/2 constraints - shouldn't use
%  cons/2 itself because only resulting type's maps need to be checked, i.e. no inheritance
	 ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
	 )
      ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
      )
    ),
    goal_list_to_seq(UGoals,DelayedGoal)
  ).
uact(_Type3,TFS1,TFS2,_,Type1,Type2,N2,PreGoals,PostGoals) :-  % Type2 belongs to a module, but not Type1
  clause(tmodule(Type2,Module2),true),  % N2 bears the name of this module -- this is all we can see
  !,                                    % if Type1 has no module, until we look at the first arg.
  ( clause(utype_module_pair_visited(Type1,Module2),true) % So throw away all but the key, Module2.
  -> fail  % already generated a clause for this - backtrack
  ; clause(marity(Module2,Arity2),true),  
    functor(N2,Module2,Arity2), arg(1,N2,TypePos2),
    PreGoals = [deref_type_pos(TypePos2,TFS2,T2,Int2)|PreGoalsRest],
    (Type1 == bot -> PreGoalsRest = [], % all we need here is to update the interrupt on FS1 with Int2
	             PostGoals = [utype_module_throw_interrupt(Int1,T2,Int2)]
      % HACK: really, we should be looking for any type that subsumes every element of this module's basis,
      % not just bot
    ; name(Type1,Type1Name),
      append("add_to_type_",Type1Name,RelName), name(Rel,RelName),
      ATGoal =.. [Rel,T2,TFS2,TypePos2],
      PreGoalsRest = [ATGoal],
		% if nonvar(TypePos2), then T2 is maximal, so add_to_type trivially succeeds or fails.
      PostGoals = [utype_module_deref_throw_int(TypePos2,Int1)] % Even when T2 is maximal, W will have 
    ),           % a singleton var argument -- cheaper than conditionally binding PostGoals at run-time
    TFS1 = tfs(_,Int1),
    assert(utype_module_pair_visited(Type1,Module2))
  ).
uact(Type3,TFS1,TFS2,FS2,Type1,Type2,N2,PreGoals,PostGoals) :-  % neither Type1 nor Type2 belongs to a module
  bot_trans(Type2,N2),
  TFS1 = tfs(_,Int1), TFS2 = tfs(_,Int2),
  ( Type1 == Type2 -> Int1 = Int2, PreGoals = [], PostGoals = []
  ; Type2 == Type3 -> functor(W,Type2,1), arg(1,W,Int2), PreGoals = [], PostGoals = [Int1 = W]
  ; Type1 == Type3 -> functor(W,Type1,1), arg(1,W,Int1), PreGoals = ['$put_attributes'(FS2,TFS1)],
                      PostGoals = [Int2 = W]
  ; functor(W,Type3,1), arg(1,W,Int3),  % Even if Type3 is maximal, right thing to do is fetch MGSat.
    PreGoals = ['$delete_attributes'(FS2),bind_mgsat(Type3,FS2,Int3),Int2 = W],
    PostGoals = [Int1 = Int2]
  ).

utype_module_deref_throw_int(TypePos2,Int1) :-
  deref_type_pos(TypePos2,_,Type2,Int2),
  utype_module_throw_interrupt(Int1,Type2,Int2).

deref_type_pos(TypePos,TFS,Type,Int) :-
  var(TypePos) -> '$get_attributes'(TypePos,TFS,Type), arg(4,TFS,Int)
  ; functor(TypePos,Type,_).

utype_module_throw_interrupt(Int1,Type2,Int2) :-
  functor(W,Type2,1), arg(1,W,Int2),
  Int1 = W.


% ------------------------------------------------------------------------------
% ucons(Type:<type>,ExclType1:<type>,ExclType2:<type>,Tag:<ref>,SVs:<sv>s,
%       IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% Enforce the constraint for Type, and for all supersorts of Type, excluding
%  ExclType1 and ExclType2, on Tag-SVs
% ------------------------------------------------------------------------------
ucons(Type,ET1,ET2,ConsTypes) :-
  findall(T,(clause(constrained(T),true),
             sub_type(T,Type), % find set of types whose constraints must be
             \+sub_type(T,ET1), %  satisfied
             \+sub_type(T,ET2)),ConsTypes).
%  map_cons(ConsTypes,FS,SubGoals,[]).

% ------------------------------------------------------------------------------
% ct(Type:<type>,Tag:<ref>,SVs:<sv>s,Goals:<goal>s,Rest:<goal>s,IqsIn:<ineq>s,
%    IqsOut,<ineq>s)
% ------------------------------------------------------------------------------
% Goals, with tail Rest, are the compiled goals of the description (and
%  clause) attached to Type, enforced on feature structure Tag-SVs
% ------------------------------------------------------------------------------
:- dynamic constrained/1.
%ct(_Type,_FS,Rest,Rest,Iqs,Iqs) if_b [fail] :-  
%  \+ current_predicate(cons,(_ cons _)),
%  !.
ct(Type,FS,Types) if_b Goals :-  % HACK: prob. should assert these as facts
  empty_avl(VarsIn),
  empty_avl(EMFS),
  empty_avl(NVs),
  empty_avl(FSsIn),
  empty_avl(EMode),
  (Type cons RHS),
  initialise_mode([],EMode,ModeIn,EMFS,MFSIn),
  assert_mode(type(Type),[],ModeIn,MFSIn,MFSMid),
  ( nonvar(RHS), RHS = (Cons goal Goal) ->
    compile_desc(Cons,FS,Goals,GoalsMid2,[],serial,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,
		 ModeIn,_,MFSMid,MFSMid2,NVs),
    term_variables(Cons,ConsVars),
    compile_body(Goal,GoalsMid2,[enforce_constraints(Types,FS)],serial,VarsMid,_,
		 FSPal,FSsMid,FSsOut,MFSMid2,_,NVs,ConsVars,[]),
    assert_empty_avl(FSsOut),
%    build_fs_palette(FSsOut,FSPal,Goals,GoalsMid,ct),
    assert(constrained(Type))
  ; compile_desc(RHS,FS,Goals,[enforce_constraints(Types,FS)],[],serial,VarsIn,_,
		 FSPal,FSsIn,FSsOut,ModeIn,_,MFSMid,_,NVs),
    assert_empty_avl(FSsOut),
%    build_fs_palette(FSsOut,FSPal,Goals,GoalsMid,ct),
    assert(constrained(Type))
  ).
% ct(_Type,FS,Rest,Rest,Iqs,Iqs) if_b [].    % all other types

enforce_constraints([],_).
enforce_constraints([T|CTypes],FS) :-
  ct(T,FS,CTypes).

assert_empty_avl(Assoc) :-
  empty_avl(Assoc).  % KNOWN BUG: should raise an exception when this fails.

% ------------------------------------------------------------------------------
% map_cons(Types:<type>s,Tag:<ref>,SVs:<sv>s,IqsIn:<ineq>s,IqsOut:<ineq>s,
%          SubGoals:<goal>s,SubGoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% Given a set of types, strings together the goals and inequations for them.
% ------------------------------------------------------------------------------
%map_cons([],_,_,Iqs,Iqs,Goals,Goals).
%map_cons([Type|Types],Tag,SVs,IqsIn,IqsOut,SubGoals,SubGoalsRest) :-
%  ct(Type,Tag,SVs,SubGoals,SubGoalsMid,IqsIn,IqsMid),
%  map_cons(Types,Tag,SVs,IqsMid,IqsOut,SubGoalsMid,SubGoalsRest).
%map_cons([],_,Goals,Goals).
%map_cons([T|ConsTypes],FS,Goals,GoalsRest) :-
%  ct(T,FS,Goals,GoalsMid),
%  map_cons(ConsTypes,FS,GoalsMid,GoalsRest).

% ------------------------------------------------------------------------------
% map_feats_eq(FRs:<feat>s,Vs1:<fs>s,Vs2:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s,
%              Goals:<goal>s)
% ------------------------------------------------------------------------------
% Vs1 and Vs2 set to same length as FRs and a subgoal added to Goals
% to unify value of each feature;
% ------------------------------------------------------------------------------
map_feats_eq(N,N,_,_,SubGoals,SubGoals) :- !.
map_feats_eq(I,N,TFS1,TFS2,[V1=V2|SubGoals],SubGoalsRest) :-
  NewI is I + 1, arg(NewI,TFS1,V1), arg(NewI,TFS2,V2),
  map_feats_eq(NewI,N,TFS1,TFS2,SubGoals,SubGoalsRest).


% ------------------------------------------------------------------------------
% map_feats_subs(FRs1:<feat>s, FRs2:<feat>s, Vs1:<fs>s, Vs2:<fs>s, 
%                IqsIn:<ineq>s, IqsOut:<ineq>s, Goals:<goal>s) 
% ------------------------------------------------------------------------------
% Vs1 and Vs2 set to same length as FRs1 and FRs2 and a subgoal 
% added to Goals for each shared feature;  
% ------------------------------------------------------------------------------
map_feats_subs([],_,_,_,_,_,SubGoals,SubGoals).
map_feats_subs([F:_|FRs1],FRs2,TFS1,I1,TFS2,I2,[V1=V2|SubGoals],
	       SubGoalsRest) :-
  arg(I1,TFS1,V1), NewI1 is I1 + 1,
  map_feats_find(F,FRs2,V2,TFS2,I2,FRs2Out,NewI2),
  map_feats_subs(FRs1,FRs2Out,TFS1,NewI1,TFS2,NewI2,SubGoals,SubGoalsRest).

% ------------------------------------------------------------------------------
% map_feats_find(F:<feat>, FRs:<feat>s, V:<fs>, Vs:<fs>s, 
%                FRsOut:<feat>s, VsOut:<fs>s)
% ------------------------------------------------------------------------------
% if F is the Nth element of FRs then V is the Nth element of Vs;
% FRsOut and VsOut are the rest (after the Nth) of FRs and Vs
% ------------------------------------------------------------------------------
map_feats_find(F,[F2:_|FRs],V,TFS,I,FRsOut,NewI) :-
  ( F == F2 -> arg(I,TFS,V), NewI is I + 1, FRsOut = FRs
  ; IMid is I + 1,
    map_feats_find(F,FRs,V,TFS,IMid,FRsOut,NewI)
  ).

% ------------------------------------------------------------------------------
% map_feats_unif(FRs1:<feat>s,FRs2:<feat>s,FRs3:<feat>s,Vs1:<fs>s,Vs2:<fs>s,
%                 Vs3:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s,Goals:<goal>s,
%                 GoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% Vs1, Vs2 and Vs3 set to same length as Feats1, FRs2 and FRs3;
% a subgoal's added to Goals for each feature shared in FRs1 and FRs2;  
% feats shared in Vs1,Vs2 and Vs3 passed; new Vs3 entries are created
% ------------------------------------------------------------------------------
map_feats_unif([],FRs2,FRs3,FS,Goals,GoalsRest):-
  map_new_feats(FRs2,FRs3,FS,Goals,GoalsRest).
map_feats_unif([F1:R1|FRs1],FRs2,FRs3,FS,Goals,GoalsRest):-
  map_feats_unif_ne(FRs2,F1,R1,FRs1,FRs3,FS,Goals,GoalsRest).

map_feats_unif_ne([],F1,R1,FRs1,FRs3,FS,Goals,GoalsRest):-
  map_new_feats([F1:R1|FRs1],FRs3,FS,Goals,GoalsRest).
map_feats_unif_ne([F2:R2|FRs2],F1,R1,FRs1,FRs3,FS,Goals,GoalsRest):-
  compare(Comp,F1,F2),
  map_feats_unif_act(Comp,F1,F2,R1,R2,FRs1,FRs2,FRs3,FS,Goals,GoalsRest).

map_feats_unif_act(=,F1,_F2,R1,R2,FRs1,FRs2,FRs3,FS,Goals,GoalsRest):-
  unify_type(R1,R2,R1UnifyR2),
  map_new_feats_find(F1,R1UnifyR2,FRs3,FS,FRs3Out,Goals,GoalsMid),
  map_feats_unif(FRs1,FRs2,FRs3Out,FS,GoalsMid,GoalsRest).
map_feats_unif_act(<,F1,F2,R1,R2,FRs1,FRs2,FRs3,FS,Goals,GoalsRest):-
  map_new_feats_find(F1,R1,FRs3,FS,FRs3Out,Goals,GoalsMid),
  map_feats_unif_ne(FRs1,F2,R2,FRs2,FRs3Out,FS,GoalsMid,GoalsRest).
map_feats_unif_act(>,F1,F2,R1,R2,FRs1,FRs2,FRs3,FS,Goals,GoalsRest):-
  map_new_feats_find(F2,R2,FRs3,FS,FRs3Out,Goals,GoalsMid),
  map_feats_unif_ne(FRs2,F1,R1,FRs1,FRs3Out,FS,GoalsMid,GoalsRest).

% ------------------------------------------------------------------------------
% map_new_feats(FRs:<feat>s, FRsNew:<feat>s, Vs:<fs>s, VsNew:<fs>s, 
%               IqsIn:<ineq>s,IqsOut:<ineq>s,Gs:<goal>s,GsRest:<goal>s)
% ------------------------------------------------------------------------------
% FRs and FRsNew must be instantiated in alpha order where
% FRs is a sublist of NewFs;
% create Vs and VsNew where Vs and VsNew share a value if the
% feature in Fs and NewFs matches up, otherwise VsNew gets a fresh
% minimum feature structure (_-bot(_)) for a value;
% all necessary value coercion is also performed
% ------------------------------------------------------------------------------
map_new_feats([],FRsNew,FS,SubGoals,SubGoalsRest):-
  map_new_feats_introduced(FRsNew,FS,SubGoals,SubGoalsRest).
map_new_feats([Feat:TypeRestr|FRs],FRsNew,FS,SubGoals,SubGoalsRest):-
  map_new_feats_find(Feat,TypeRestr,FRsNew,FS,FRsNewLeft,SubGoals,SubGoalsMid),
  map_new_feats(FRs,FRsNewLeft,FS,SubGoalsMid,SubGoalsRest).

% ------------------------------------------------------------------------------
% map_new_feats_find(Feat,TypeRestr,FRs,V,Vs,FRs2,Vs2,IqsIn,IqsOut,
%                    SubGoals,SubGoalsRest)
% ------------------------------------------------------------------------------
% finds Feat value V in Vs, parallel to FRs, with restriction TypeRestr on V, 
% with FRs2 being left over;  carries out coercion on new feature values
% with SubGoals-SubGoalsRest being the code to do this
% ------------------------------------------------------------------------------
map_new_feats_find(Feat,TypeRestr,[Feat2:TypeRestrNew|FRs],
                   FS,FRsNew,SubGoals,SubGoalsRest):-
  ( Feat == Feat2 -> FRsNew = FRs,    
                     ( sub_type_ind(TypeRestrNew,TypeRestr) -> SubGoals = SubGoalsRest
                     ; clause(fcolour(Feat,K,Module),true),
		       clause(marity(Module,Arity),true),
		       functor(FS,Module,Arity), arg(K,FS,V),
		       SubGoals = [Goal|SubGoalsRest],
                       ((TypeRestrNew = a_ X) -> Goal = add_to_typed_a_(V,X)
                       ; name(TypeRestrNew,TypeRestrNewName),
			 append("add_to_typed_",TypeRestrNewName,RelName), name(Rel,RelName),
                         functor(Goal,Rel,1), arg(1,Goal,V)
                       )
                     )
  ; clause(fcolour(Feat2,K,Module),true),
    clause(marity(Module,Arity),true),
    functor(FS,Module,Arity), arg(K,FS,V),
    SubGoals = [bind_mgsat(TypeRestrNew,V,_)|SubGoalsMid],
    map_new_feats_find(Feat,TypeRestr,FRs,FS,FRsNew,SubGoalsMid,SubGoalsRest)
  ).

% ------------------------------------------------------------------------------
% map_new_feats_introduced(FRs,Vs,IqsIn,IqsOut,SubGoals,SubGoalsRest)
% ------------------------------------------------------------------------------
% instantiates Vs to act as values of features in FRs;  SubGoals contains
% type coercions necessary so that Vs satisfy constraints in FRs
% ------------------------------------------------------------------------------
map_new_feats_introduced([],_,Rest,Rest).
map_new_feats_introduced([F:TypeRestr|FRs],FS,SubGoals,SubGoalsRest):-
 clause(fcolour(F,K,Module),true),
 clause(marity(Module,Arity),true),
 functor(FS,Module,Arity), arg(K,FS,V),
 SubGoals = [bind_mgsat(TypeRestr,V,_)|SubGoalsMid],
 map_new_feats_introduced(FRs,FS,SubGoalsMid,SubGoalsRest).

bind_mgsat(Type,FS,Int) if_b SubGoals :-
  clause(mgsc(Type,FS,Int,SubGoals,[]),true).

bind_mgsat_offline(Type,FS,Int,ResidueSeq) :-
  bind_mgsat(Type,FS,Int),
  residuate_term(FS,ResidueSeq).  % SP4: must preserve mgsat residues

% ==============================================================================
% Lexical Rules
% ==============================================================================

% ------------------------------------------------------------------------------
% lex_rule(WordIn,TagIn,SVsIn,WordOut,TagOut,SVsOut,IqsIn,IqsOut)          mh(0)
% ------------------------------------------------------------------------------
% WordOut with category TagOut-SVsOut can be produced from
% WordIn with category TagIn-SVsIn by the application of a single
% lexical rule;  TagOut-SVsOut is fully dereferenced on output;
% Words are converted to character lists and back again
% ------------------------------------------------------------------------------
lex_rule(WordIn,FSIn,GoalIn,WordOut,FSOut,GoalPriorVs,GoalOut,Link) if_h SubGoals :-
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(NVs),
  empty_avl(EMFS),
  ( (LexRuleName lex_rule DescOrGoalIn **> DescOrGoalOut morphs Morphs),
    Cond = true
  ; (LexRuleName lex_rule DescOrGoalIn **> DescOrGoalOut if Cond morphs Morphs)
  ),
  lex_desc_goal(DescOrGoalIn,DescIn,_,GoalIn),
  lex_desc_goal(DescOrGoalOut,DescOut,true,GoalOut),
  term_variables(DescIn,DescInVars),
  term_variables(DescOut,DescOutVars),
  prior_cont_vars(GoalOut,GoalVars),
  prior_cont_vars(Cond,CondVars),
  ord_union(DescInVars,DescOutVars,DescVars),
  ord_union(CondVars,DescVars,GoalPriorVs),
  ( ord_intersect(GoalVars,DescOutVars) -> Link = link
  ; ord_intersect(CondVars,DescOutVars) -> Link = link
  ; Link = nolink
  ),
  empty_avl(EMode),
  genindex(In),
  initialise_mode(In,EMode,ModeIn,EMFS,MFSIn),
  compile_desc(DescIn,FSIn,SubGoals,SubGoalsRest1,In,
               serial,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSIn,MFSMid,NVs),
  term_variables(Morphs,MorphsVars),
  ord_union(DescOutVars,MorphsVars,ContVsCond),
  compile_body(Cond,SubGoalsRest1,SubGoalsMid,serial,VarsMid,
               VarsMid2,FSPal,FSsMid,FSsMid2,MFSMid,MFSMid2,NVs,DescInVars,ContVsCond),
  genindex(Out),
  initialise_mode(Out,EMode,ModeIn2,MFSMid2,MFSMid3),
  empty_avl(EAssoc),  
  compile_desc_act(DescOut,EAssoc,ImplicitVars,SubGoalsMid,SubGoalsMid2,Out,
		   serial,VarsMid2,_,FSPal,FSsMid2,FSsOut,ModeIn2,_ModeOut,MFSMid3,_MFSOut,NVs),
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(Out,Out,ImplicitVars,FS,_,SubGoalsMid2,[morph(Morphs,WordIn,WordOut,SelectedInPattern,SelectedOutPattern)
%         ,write(user_error,_LexRuleName),write(user_error,' '),write(user_error,WordOut),  % DEBUG
%	  nl(user_error), flush_output(user_error)
						    |SubGoalsRest2]),
  FS = fs(FSOut),
  generate_apply_forall_lex_rule(LexRuleName,FSIn,FSOut,SelectedInPattern,SelectedOutPattern,SubGoalsRest2,[]),
  assert_empty_avl(FSsOut).
%  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsFinal,lex_rule).

% ------------------------------------------------------------------------------
% morph(Morphs,WordIn,WordOut)
% ------------------------------------------------------------------------------
% converst WordIn to list of chars, performs morph_chars using Morphs
% and then converts resulting characters to WordOut
% ------------------------------------------------------------------------------
morph(Morphs,WordIn,WordOut,
      SelectedInPattern,SelectedOutPattern):-  % need to instantiate Word even if
  name(WordIn,CodesIn),                       %  X becomes X - do we want this?
  make_char_list(CodesIn,CharsIn), 
  morph_chars(Morphs,CharsIn,CharsOut,SelectedInPattern,SelectedOutPattern),
  make_char_list(CodesOut,CharsOut),
  name(WordOut,CodesOut).

% lexicalize(+,?): convert an instantiated Pattern to a Word.
lexicalize(Pattern,Word) :-
  morph_pattern(Pattern,Chars),
  make_char_list(Codes,Chars),
  name(Word,Codes).

% ------------------------------------------------------------------------------
% morph_chars(Morphs:<seq(<morph>)>, 
%             CharsIn:<list(<char>)>, CharsOut:<list(<char>)>)
% ------------------------------------------------------------------------------
% applies first pattern rewriting in Morphs that matches input CharsIn
% to produce output CharsOut;  CharsIn should be instantiated and
% CharsOut should be uninstantiated for sound result
% ------------------------------------------------------------------------------
morph_chars((Morph,Morphs),CharsIn,CharsOut,SelectedInPattern,SelectedOutPattern):-
  !,( morph_template(Morph,CharsIn,CharsOut,SelectedInPattern,SelectedOutPattern) 
    -> true
     ; morph_chars(Morphs,CharsIn,CharsOut,SelectedInPattern,SelectedOutPattern)
    ).
morph_chars(Morph,CharsIn,CharsOut,SelectedInPattern,SelectedOutPattern):-
  morph_template(Morph,CharsIn,CharsOut,SelectedInPattern,SelectedOutPattern).

% ------------------------------------------------------------------------------
% morph_template(Morph:<morph>, CharsIn:<chars>, CharsOut:<chars>)
% ------------------------------------------------------------------------------
% applies tempalte Morph to CharsIn to produce Chars Out;  first
% breaks Morph into an input and output pattern and optional condition
% ------------------------------------------------------------------------------
morph_template((PattIn becomes PattOut),CharsIn,CharsOut,PattIn,PattOut):-
  morph_pattern(PattIn,CharsIn),
  morph_pattern(PattOut,CharsOut).
morph_template((PattIn becomes PattOut when Cond),CharsIn,CharsOut,PattIn,PattOut):-
  morph_pattern(PattIn,CharsIn),
  call(Cond),
  morph_pattern(PattOut,CharsOut).

bind_morph_template((AtomsIn became AtomsOut),PattIn,PattOut) :-
  bind_morph_pattern(PattIn,AtomsIn),
  bind_morph_pattern(PattOut,AtomsOut).

% ------------------------------------------------------------------------------
% morph_pattern(Patt:<pattern>,Chars:<list(<char>)>)
% ------------------------------------------------------------------------------
% apply pattern Patt, which is sequence of atomic patterns,
% to list of characters Chars, using append/3 to deconstruct Chars
% ------------------------------------------------------------------------------
morph_pattern(Var,CharsIn):-
  var(Var),  
  !, Var = CharsIn.
morph_pattern((AtPatt,Patt),CharsIn):-
  !, make_patt_list(AtPatt,List),
  append(List,CharsMid,CharsIn),
  morph_pattern(Patt,CharsMid).
morph_pattern(AtPatt,CharsIn):-
  make_patt_list(AtPatt,CharsIn).

bind_morph_pattern((AtPatt,Patt),(AtAtom,Atoms)) :-
  !,bind_morph_pattern(AtPatt,AtAtom),
  bind_morph_pattern(Patt,Atoms).
bind_morph_pattern([C|Cs],Atom) :-
  !,make_char_list(Codes,[C|Cs]),
  name(Atom,Codes).
bind_morph_pattern(AtPatt,AtAtom) :-
  atomic(AtPatt),
  AtAtom = AtPatt.

% ------------------------------------------------------------------------------
% make_patt_list(AtPatt:<atomic_pattern>,List:<list(<char>)>)
% ------------------------------------------------------------------------------
% turns an atomic pattern AtPatt, either a variable, list of characters
% or atom into a list of characters (or possibly a variable);  List
% should not be instantiated
% ------------------------------------------------------------------------------
make_patt_list(Var,Var):-
  var(Var),
  !.
make_patt_list([H|T],[H|TOut]):-
  !, make_patt_list(T,TOut).
make_patt_list([],[]):-
  !.
make_patt_list(Atom,CharList):-
  atom(Atom),
  name(Atom,Name),
  make_char_list(Name,CharList).

% ------------------------------------------------------------------------------
% make_char_list(CharNames:<list(<ascii>)>, CharList:<list(<char>)>)
% ------------------------------------------------------------------------------
% turns list of character ASCII codes and returns list of corresponding
% characters
% ------------------------------------------------------------------------------
make_char_list([],[]).
make_char_list([CharName|Name],[Char|CharList]):-
  name(Char,[CharName]),
  make_char_list(Name,CharList).

generate_apply_forall_lex_rule(LexRuleName,FSIn,FSOut,PatternIn,PatternOut,SubGoals,SubGoalsRest) :-
  guarded_forall_lex_rule(_,_,_,_,_,_)
  -> SubGoals = [apply_forall_lex_rule(LexRuleName,FSIn,FSOut,PatternIn,PatternOut)|SubGoalsRest]
  ; guarded_forall_lex_rule_hook(_,_,_,_,_,_)
  -> SubGoals = [apply_forall_lex_rule(LexRuleName,FSIn,FSOut,PatternIn,PatternOut)|SubGoalsRest]
  ; SubGoalsRest = SubGoals.

guarded_forall_lex_rule(N,LR,In,Out,M,B) :-
  current_predicate(forall,(_ forall _)), (N forall LR lex_rule In **> Out morphs M do B).
guarded_forall_lex_rule_hook(N,LR,In,Out,M,B) :-
  current_predicate(forall_hook,(_ forall_hook _)), (N forall_hook LR lex_rule In **> Out morphs M do B).

apply_forall_lex_rule(_,_,_,_,_) if_b [true] :-
  \+ guarded_forall_lex_rule(_,_,_,_,_,_),
  \+ guarded_forall_lex_rule_hook(_,_,_,_,_,_),
  !.
apply_forall_lex_rule(LexRuleName,FSIn,FSOut,PatternIn,PatternOut) if_b Goals :-
  ebagof(forall_lex_rule(Name,LRParm,FSInParm,FSOutParm,PattInParm,PattOutParm),
         LR^I^O^M^B^(( guarded_forall_lex_rule(Name,LR,I,O,M,B)
                     ; guarded_forall_lex_rule_hook(Name,LR,I,O,M,B)
                     ),
                    LRParm = LexRuleName, FSInParm = FSIn, FSOutParm = FSOut, PattInParm = PatternIn,
                    PattOutParm = PatternOut),Goals).

forall_lex_rule(_,_,_,_,_,_) if_b [true] :-
  \+ guarded_forall_lex_rule(_,_,_,_,_,_),
  \+ guarded_forall_lex_rule_hook(_,_,_,_,_,_),
  !.
forall_lex_rule(_,_,_,_,_,_) if_b _ :-
  findall(Name,guarded_forall_lex_rule(Name,_,_,_,_,_),Names,NamesRest),
  findall(Name,guarded_forall_lex_rule_hook(Name,_,_,_,_,_),NamesRest),
  has_duplicates(Names),
  append(_,[Name|Rest],Names), member_eq(Name,Rest),
  raise_exception(ale(forall_lex_rule_dup(Name))).
forall_lex_rule(Name,LRName,FSIn,FSOut,PatternIn,PatternOut) if_b Goals :-
  empty_avl(ENVs),
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(EMFS),
  ( guarded_forall_lex_rule(Name,LRArg,DescIn,DescOut,Morphs,Body)
  ; guarded_forall_lex_rule_hook(Name,LRArg,DescIn,DescOut,Morphs,Body)
  ),
  desc_varfs_desc([DescIn|DescOut],[],DescVars,[],_,[],ENVs),
  sort(DescVars,SortedDescVars),
  list_to_nv_unseen(SortedDescVars,DescNVs),
  term_variables(Morphs,MorphVars),
  sort([PatternIn,PatternOut|MorphVars],PriorVs),
  compile_body((prolog(LRName=LRArg) -> when((FSIn=DescIn,FSOut=DescOut),
                                             (prolog(bind_morph_template(Morphs,PatternIn,PatternOut)),
                                              Body)) 
               ; true),
               Goals,[],serial,VarsIn,_,_,FSsIn,_,EMFS,_,DescNVs,PriorVs,[]).

% ==============================================================================
% Rounds-Kasper Logic
% ==============================================================================

% ------------------------------------------------------------------------------
% add_to(Phi:<desc>, Tag:<tag>, SVs:<svs>, IqsIn:<ineq>s, IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% Info in Phi is added to FSIn (FSIn already derefenced);
% ------------------------------------------------------------------------------
add_to(Desc,FS) :-
%  write(user_error,'user predicate add_to/2 has been called'), nl(user_error),  % DEBUG
%  flush_output(user_error),
  deref(FS,TFS,Type,AttPos),
  on_exception(ale(Exception),add_to(Desc,FS,Type,TFS,AttPos,bot),
	       alex(Exception)).

%add_to(Desc,FS,MGType) :-
%  deref(FS,TFS,Type,AttPos),
%  unify_type(Type,MGType,VType),
%  on_exception(ale(Exception),add_to(Desc,FS,Type,TFS,AttPos,VType),
%	       alex(Exception)).

add_to(X,FS2,_Type2,_TFS2,_AttPos2,VType2) :-
  var(X),
  !, % '$get_attributes'(X,TFS1,Type1),
%  ( Type1 == 0 -> (X = FS2)
  if((X=FS2,  %call_u(Type1,Type2,TFS1,TFS2,X,FS2),
      deref(FS2,TFS2Mid,Type2Mid,AttPos2Mid),  % HACK: way to may deref/4 calls here - VType is often bot
      add_to_type(VType2,Type2Mid,TFS2Mid,AttPos2Mid)),	
     true,  % the only way X could be unattributed var is if X has type bot, and VType2=bot
     (ale_flag(adderrs,off) -> fail
     ; raise_exception(ale(fsvar_noadd(X,FS2)))
     )).
%).
add_to([],FS,Type,TFS,AttPos,VType):-
  !, add_to(e_list,FS,Type,TFS,AttPos,VType).
add_to([H|T],FS,Type,TFS,AttPos,VType):-
  !, add_to((hd:H,tl:T),FS,Type,TFS,AttPos,VType).
add_to(Path1 == Path2,FS,Type,TFS,AttPos,VType) :-  % FS could be var if Path1=Path2=[]
  !, pathval(Path1,FS,AttPos,Type,TFS,FSAtPath1,VType),
  deref(FS,TFSMid,TypeMid,AttPosMid),
  pathval(Path2,FS,AttPosMid,TypeMid,TFSMid,FSAtPath2,VType),
  if(FSAtPath1=FSAtPath2,   % call_u(TypeAtPath1,TypeAtPath2,TFSAtPath1,TFSAtPath2,FSAtPath1,FSAtPath2),
     true,
     (ale_flag(adderrs,off) -> fail
     ; raise_exception(ale(path_noadd(Path1,Path2,FS)))
     )).
add_to(=\= Desc,FS,Type,TFS,AttPos,VType):-
  !,add_to_type(VType,Type,TFS,AttPos),  % dif/2 may not catch a type incompatibility if FS is left unfilled
  add_to(Desc,FS2,bot,tfs(bot,_Int2),FS2,bot), % no need to attach since only functions would delay
  dif(FS,FS2).                                 %  on Int2, and they re-dereference.

add_to(Feat:Desc,FS,Type,TFS,AttPos,VType):-  % after this, FS definitely is not a var
  !,                                              % - featval will add VType
  ( var(Feat) -> raise_exception(ale(feat_notatom(Feat,Feat:Desc)))
  ; approp(Feat,_,_) -> true
  ; raise_exception(ale(undef_feat(Feat)))
  ),
  if(featval(Feat,FS,Type,TFS,AttPos,FSatFeat,VType,FVType), 
     (deref(FSatFeat,TFSatFeat,TypeatFeat,AttPosFeat),
      add_to(Desc,FSatFeat,TypeatFeat,TFSatFeat,AttPosFeat,FVType)),
     ( ale_flag(adderrs,off) -> fail
     ; raise_exception(ale(feat_noadd(Feat,FS)))
     )).
add_to((Desc1,Desc2),FS,Type,TFS,AttPos,VType):-
  !, add_to(Desc1,FS,Type,TFS,AttPos,VType),
  deref(FS,TFS2,Type2,AttPos2),
  add_to(Desc2,FS,Type2,TFS2,AttPos2,VType).
add_to((Desc1;Desc2),FS,Type,TFS,AttPos,VType):-
  !, 
  ( add_to(Desc1,FS,Type,TFS,AttPos,VType)
  ; add_to(Desc2,FS,Type,TFS,AttPos,VType)
  ).
add_to(@ MacroName,FS,Type,TFS,AttPos,VType):-
  !, 
  ( (MacroName macro Desc) -> add_to(Desc,FS,Type,TFS,AttPos,VType)
  ; raise_exception(ale(macro_noadd(MacroName,FS)))
  ).
%add_to(bot,_,_,_,_,VType,VType) :- !.  % An alternative would be to zero-translate types in Type clause below
add_to(X,FS2,_Type2,_TFS2,_AttPos2,VType2) :-
  functor(X,Module,Arity),  % X is an instantiated feature structure
  clause(marity(Module,Arity),true),
  !,
  if((X=FS2,   %call_u(Type1,Type2,TFS1,TFS2,X,FS2),
      deref(FS2,TFS2Mid,Type2Mid,AttPos2Mid),
      add_to_type(VType2,Type2Mid,TFS2Mid,AttPos2Mid)),
     true,  % FS2 can't be a var after unification with X
     (ale_flag(adderrs,off) -> fail
     ; raise_exception(ale(fsvar_noadd(X,FS2)))
     )).
add_to(Type,FS,FSType,TFS,AttPos,VType):-
  type(Type),
  !,
  ( (ground(Type), sub_type(Type,VType)) -> true
    % if Type is not ground, then a_/1 atom might need to bind its argument vars
  ; if((unify_type(Type,VType,AddType),
	add_to_type(AddType,FSType,TFS,AttPos)),
       true,
       (ale_flag(adderrs,off) -> fail
       ; raise_exception(ale(type_noadd(Type,FS,VType)))
       ))
  ).
add_to(FunDesc,FS,Type,TFS,AttPos,VType) :-   % complex function constraints
  functor(FunDesc,Functor,FunArity),
  FunDesc =.. [_|FunDescArgs],
  clause(fun_spec(Functor,FunArity,_),true),
  !, name(Functor,FunName),
  append("fs_",FunName,RelName),
  name(Rel,RelName),
  clause(fun_spec(Functor,FunArity,ResArg),true),
  PreLen is ResArg - 1, PostLen is FunArity - ResArg + 1,
  length(PreArgs,PreLen), length(PostArgs,PostLen),
  append(PreArgs,PostArgs,FunArgs),
  append(PreArgs,[FS|PostArgs],RelArgs),
  Goal =.. [Rel|RelArgs],
  add_to_type(VType,Type,TFS,AttPos),  % must fill FS before passing to function
  mg_sat_list(FunDescArgs,FunArgs),
  call(Goal).
add_to(Atom,_FS,_Type,_TFS,_AttPos,_) :-
  atomic(Atom),
  !,
  raise_exception(undef_type(Atom)).
add_to(Desc,_FS,_Type,_TFS,_AttPos,_) :-
  raise_exception(ill_desc(Desc)).

% add_to_list(Descs:<desc>s,FSs:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
%  add each description in Descs to the respective FS in FSs
% ------------------------------------------------------------------------------
%add_to_list([],[]).
%add_to_list([Desc|Descs],[FS|FSs]) :-
%  deref(FS,TFS,Type,AttPos),
%  add_to(Desc,FS,Type,TFS,AttPos,bot),
%  add_to_list(Descs,FSs).

% add_to_fresh(Descs:<desc>s,FSs:<fs>s,IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
%  same as add_to_list, but instantiates the FS's first to bottom
% ------------------------------------------------------------------------------
%add_to_fresh([],[]).
%add_to_fresh([Desc|Descs],[FS|FSs]) :-
%%  TFS = tfs(bot,_Int),
%%  '$put_attributes'(FS,TFS),
%  add_to(Desc,FS,0,tfs(0,_Int),FS),
%  add_to_fresh(Descs,FSs).

% ------------------------------------------------------------------------------
% pathval(P:<path>,TagIn:<tag>,SVsIn:<svs>,TagOut:<tag:,SVsOut:<svs>,
%         IqsIn:<ineq>s,IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% TagOut-SVsOut is the undereferenced value of dereferenced TagIn-SVsIn
% at path P
% ------------------------------------------------------------------------------
pathval([],FS,_AttPos,_Type,_TFS,FS,_VType).
pathval([Feat|Path],FS,AttPos,Type,TFS,FSOut,VType):-
  if(featval(Feat,FS,Type,TFS,AttPos,FSMid,VType,FVType),
     (deref(FSMid,TFSMid,TypeMid,AttPosMid),
      pathval(Path,FSMid,AttPosMid,TypeMid,TFSMid,FSOut,FVType)),
     (ale_flag(adderrs,off) -> fail
     ; raise_exception(ale(featpath_noadd(Feat,Path,FS,VType)))
     )).

featval(Feat,FS,Type,TFS,AttPos,FeatVal,VType,FVType) :-
  clause(introduce(Feat,FIntro),true),
  unify_type(VType,FIntro,AddType),
  add_to_type(AddType,Type,TFS,AttPos),
  clause(fcolour(Feat,K,_),true),
  arg(K,FS,FeatVal),
  approp(Feat,FIntro,FVType).

featvald(F,FS,VType,FeatVal,FVType) :-
  deref(FS,TFS,Type,AttPos),
  featval(F,FS,Type,TFS,AttPos,FeatVal,VType,FVType).

% ------------------------------------------------------------------------------
% add_to_type(Type:<type>,SVs:<svs>,Ref:<ref>,IqsIn:<ineq>s,
%             IqsOut:<ineq>s)                                              mh(2)
% ------------------------------------------------------------------------------
% adds Type to Ref-SVs -- arranged so that it can be compiled
% ------------------------------------------------------------------------------
add_to_type(Type1,N2,TFS2,AttPos2) if_b SubGoals :-  % unify_type/3 sorts by Type1 - cheaper to
  unify_type(Type1,Type2,Type3), %  drive off Type1 and not use if_h/2 than to
  bot_trans(Type2,N2),
  add_to_typeact(Type2,Type3,TFS2,AttPos2,SubGoals). % drive off Type2 and save some calls to
                                                     % approps/2 below.

% ------------------------------------------------------------------------------
% add_to_typeact(Type2,Type3,Type1,SVs,Ref,IqsIn,IqsOut,SubGoals)
% ------------------------------------------------------------------------------
% SubGoals is code to add type Type1 to Ref-SVs of type Type2, with
% result being of Type3
% ------------------------------------------------------------------------------

% HACK: Should rewrite this (and add_to_typed/1) to remove some unnecessary deref calls.
add_to_typeact(a_ X,a_ X,_,_,[]) :- !.
add_to_typeact(bot,bot,_,_,[]) :- !.
  % This clause protects bot FSs from the last clause, which would sever the connection to any
  %  of its delays since the bot MGSat has no attributes.
add_to_typeact(bot,a_ X,tfs(_botorNew,Int2),FS2,['$delete_attributes'(FS2), FS2 = (a_ X), Int2 = (a_ X)]) :- !.
add_to_typeact(Type2,Type3,TFS2,TypePos2,SubGoals):-
  clause(tmodule(Type2,_),true),
  !,
  ( Type2 == Type3 -> SubGoals = []  % this must be the case when Type2 is maximal
  ; maximal(Type3) -> TFS2 = tfs(_,LoopBack2,Delay2,Int2),
                      ( clause(extensional(Type3),true) -> functor(FS3,Type3,0)
		      ; functor(FS3,Type3,1), arg(1,FS3,_Intensional)
		      ),
                      SubGoals = ['$delete_attributes'(TypePos2),TypePos2 = FS3,Delay2 = max|FeatGoals],
                      approps(Type2,FRs2,_), approps(Type3,FRs3,_),
                      map_new_feats(FRs2,FRs3,LoopBack2,FeatGoals,ConsGoals),
                      add_to_typecons(Type3,Type2,ConsTypes),
                      ( ConsTypes == []
		      -> ( ale_flag(subtypecover,on)
			 -> ( clause(deranged_maps(Type3,_),true)
			    -> ConsGoals = [stc_maps_init(Type3,LoopBack2)|ConsGoalsRest]
			    ; ConsGoals = ConsGoalsRest
			    )
			 ; ConsGoals = ConsGoalsRest
			 )
                      ; ( ale_flag(subtypecover,on)
			-> ( clause(deranged_maps(Type3,_),true)
			   -> ConsGoals = [enforce_constraints(ConsTypes,LoopBack2),
					   stc_maps_init(Type3,LoopBack2)|ConsGoalsRest]
			   ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
			   )
			; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
			)
                      ),
                      ConsGoalsRest = [Int2 = Type3]
  ; TFS2 = tfs(_,LoopBack2,Delay2,Int2),
    functor(W,Type3,1), arg(1,W,Int3),
    TFS3 = tfs(Type3,LoopBack2,Delay2,Int3),
    SubGoals = ['$put_attributes'(TypePos2,TFS3)|FeatGoals],
    approps(Type2,FRs2,_), approps(Type3,FRs3,_),
    map_new_feats(FRs2,FRs3,LoopBack2,FeatGoals,ConsGoals),
    add_to_typecons(Type3,Type2,ConsTypes),
    ( ConsTypes == []
    -> ( ale_flag(subtypecover,on)
       -> ( clause(deranged_maps(Type3,_),true)
	  -> ConsGoals = [stc_maps_init(Type3,LoopBack2)|ConsGoalsRest]
	  ; ConsGoals = ConsGoalsRest
	  )
       ; ConsGoals = ConsGoalsRest
       )
    ; ( ale_flag(subtypecover,on)
      -> ( clause(deranged_maps(Type3,_),true)
	 -> ConsGoals = [enforce_constraints(ConsTypes,LoopBack2),
		         stc_maps_init(Type3,LoopBack2)|ConsGoalsRest]
	 ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
	 )
      ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
      )
    ),
    ConsGoalsRest = [Int2 = W]
  ).
add_to_typeact(Type2,Type3,TFS2,FS2,SubGoals) :-
  ( Type2 == Type3 -> SubGoals = []  % need to check this to avoid infinite loops on
  ; functor(W,Type3,1), arg(1,W,Int3),  %  constraints that select subtypes.
    functor(TFS2,tfs,2), arg(2,TFS2,Int2),
    SubGoals = ['$delete_attributes'(FS2), bind_mgsat(Type3,FS2,Int3), Int2 = W]
  ).

% ------------------------------------------------------------------------------
% add_to_typecons(Type:<type>,ExclType:<type>,Tag:<ref>,SVs:<sv>s,
%                 IqsIn:<ineq>s,IqsOut:<ineq>s,SubGoals:<goal>s)
% ------------------------------------------------------------------------------
% Enforce the constraint for Type, and for all supersorts of Type, excluding
%  those in the ideal of ExclType, on Tag-SVs
% ------------------------------------------------------------------------------

add_to_typecons(Type,ET,ConsTypes) :-
  findall(T,(clause(constrained(T),true),
             sub_type_ind(T,Type),	% find set of types whose constraints
             \+sub_type_ind(T,ET)),ConsTypes). %  must be satisfied
%  map_cons(ConsTypes,FS,SubGoals,[]).
% this map_cons is the same as the one for ucons

% ------------------------------------------------------------------------------
% featval(F:<feat>,SVs:<SVs>,Ref:<ref>,V:<fs>,
%         IqsIn:<ineq>s,IqsOut:<ineq>s)                                    mh(1)
% ------------------------------------------------------------------------------
% Ref-SVs value for feature F is V -- may involve coercion; 
% Ref-SVs is fully dereferenced;  V may not be
% ------------------------------------------------------------------------------
%featval(F,N,TFS,AttPos,V) if_h SubGoals:-
%  introduce(F,TypeIntro),
%  unify_type(TypeIntro,Type,ResType),
%  bot_trans(Type,N),
%  featval_act(Type,ResType,TFS,AttPos,SubGoals,F,V).
     % actually seems to pay to recompute this rather than compile featval
     % add_to_type code in one shot
%  deref(RefOut,SVs,_NewTag,NewSVs),
%  NewSVs =.. [_ResType|Vs],   % don't have to worry about atoms as long as
%  approps(ResType,FRs,_),       %  TypeIntro can't be bot (i.e. bot has no features)
%  find_featval(F,FRs,Vs,V).

% like add_to_typeact/5, but returns the value of F too.
%featval_act(Type2,Type3,FSOrTFS2,TypePos2,SubGoals,F,V):-
%  clause(tmodule(Type2,_),true),
%  !, clause(fcolour(F,K,_),true),
%  ( maximal(Type2) -> SubGoals = [arg(K,FSOrTFS2,V)]
%  ; Type2 == Type3 -> FSOrTFS2 = tfs(_,LoopBack2,Delay2,Int2),
%                      SubGoals = [arg(K,LoopBack2,V)]
%  ; maximal(Type3) -> FSOrTFS2 = tfs(_,LoopBack2,Delay2,Int2),
%                      functor(FS3,Type3,1), arg(1,FS3,Delay2),
%                      SubGoals = ['$delete_attributes'(TypePos2), TypePos2 = FS3|FeatGoals],
%                      approps(Type2,FRs2,_), approps(Type3,FRs3,_),
%                      map_new_feats(FRs2,FRs3,LoopBack2,FeatGoals,ConsGoals),
%                      add_to_typecons(Type3,Type2,ConsTypes),
%                      ( ConsTypes == [] -> ConsGoals = ConsGoalsRest
%                      ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
%		      ),
%                      ConsGoalsRest = [Int2 = Type3, arg(K,LoopBack2,V)]      
%  ; FSOrTFS2 = tfs(_,LoopBack2,Delay2,Int2),
%    functor(W,Type3,1), arg(1,W,Int3),
%    TFS3 = tfs(Type3,LoopBack2,Delay2,Int3),
%    SubGoals = ['$put_attributes'(TypePos2,TFS3)|FeatGoals],
%    approps(Type2,FRs2,_), approps(Type3,FRs3,_),
%    map_new_feats(FRs2,FRs3,LoopBack2,FeatGoals,ConsGoals),
%    add_to_typecons(Type3,Type2,ConsTypes),
%    ( ConsTypes == [] -> ConsGoals = ConsGoalsRest
%    ; ConsGoals = [enforce_constraints(ConsTypes,LoopBack2)|ConsGoalsRest]
%    ),
%    ConsGoalsRest = [Int2 = W, arg(K,LoopBack2,V)]
%  ).
%featval_act(_Type2,Type3,TFS2,FS2,SubGoals,F,V) :-
%  functor(W,Type3,1), arg(1,W,Int3),
%  functor(TFS2,tfs,2), arg(2,TFS2,Int2),
%  clause(fcolour(F,K,_),true),
%  SubGoals = ['$delete_attributes'(FS2), bind_mgsat(Type3,FS2,Int3), Int2 = W, arg(K,FS2,V)].


%fs_at_pos([],F,_,_) :-
%  error_msg((nl,write('unrecognised feature '),write(F))).
%fs_at_pos([F:_|_],F,Pos,Pos) :- !.
%fs_at_pos([_:_|FRs],F,Cur,Pos) :-
%  Next is Cur + 1,
%  fs_at_pos(FRs,F,Next,Pos).

% ------------------------------------------------------------------------------
% find_featval(Feat,FRs,Vs,V)
% ------------------------------------------------------------------------------
% V is element of Vs same distance from front as F:_ is from front of FRs
% ------------------------------------------------------------------------------
%find_featval(F,[F:_TypeRestr|_],[V|_Vs],V):-!.
%find_featval(F,[_|FRs],[_|Vs],V):-
%  find_featval(F,FRs,Vs,V).

% ------------------------------------------------------------------------------
% iso(FS1:<fs>, FS2:<fs>)
% ------------------------------------------------------------------------------
% determines whether structures FS1 and FS2 are isomorphic;
% not currently used, but perhaps necessary for inequations
% ------------------------------------------------------------------------------
%iso(FS1,FS2):-
%  iso_seq(iso(FS1,FS2,done)).

% ------------------------------------------------------------------------------
% iso_seq(FSSeq:<fs_seq>)
% ------------------------------------------------------------------------------
% takes structure <fs_seq> consisting of done/0 or iso(FS1,FS2,Isos)
% representing list of isomorphisms.  makes sure that all are isomorphic
% ------------------------------------------------------------------------------
%iso_seq(done).
%iso_seq(iso(FS1,FS2,Isos)):-
%  '$get_attributes'(FS1,TFS1,Type1),
%  '$get_attributes'(FS2,TFS2,Type2),
%  iso_seq_act(FS1,FS2,Type1,Type2,TFS1,TFS2,Isos).

%iso_seq_act(FS1,FS2,Type1,Type2,TFS1,TFS2,Isos) :-
%  ( (FS1 == FS2)
%    -> iso_seq(Isos)
%     ; ('$delete_attributes'(FS2),
%	FS2 = FS1,
%        iso_sub_seq(Type1,Type2,TFS1,TFS2,Isos))).

%iso_sub_seq(a_ X,a_ Y,_,_,Isos) if_h [X==Y,iso_seq(Isos)]. % ext. like Prolog
%iso_sub_seq(Sort,Sort,TFS1,TFS2,Isos) if_h SubGoal :-
%  clause(extensional(Sort),true),
%  \+ (Sort = a_ _),
%  approps(Sort,_,A), N is A + 1, Arity is N + 1,
%  functor(TFS1,tfs,Arity), arg(Arity,TFS1,Int1),
%  functor(TFS2,tfs,Arity), arg(Arity,TFS2,Int2),
%  new_isos(N,TFS1,TFS2,Int1,Int2,Isos,SubGoal).

%new_isos(1,_,_,Int1,Int2,Isos,[iso_seq(Isos),Int1 = Int2]) :-
%  !.
%new_isos(N,TFS1,TFS2,Int1,Int2,Isos,SubGoal) :-
%  arg(N,TFS1,V1),
%  arg(N,TFS2,V2),
%  NewN is N-1,
%  new_isos(NewN,TFS1,TFS2,Int1,Int2,iso(V1,V2,Isos),SubGoal).

% ------------------------------------------------------------------------------
% extensionalise(Ref:<ref>, SVs:<svs>, Iqs:<iqs>)
%-------------------------------------------------------------------------------
% search for extensional types which should be unified in Tag-SVs, and its
%  inequations, and do it.  Extensional types are assumed to be maximal.
%-------------------------------------------------------------------------------
%extensionalise(FS) :-
%  ext_act(fs(FS,fsdone),edone,[]).

%ext_act(fs(FS,FSs),ExtQ,IntQ) :-
%  deref(FS,TFS,Type,_),
%  check_pre_traverse(Type,TFS,FS,ExtQ,IntQ,FSs).
%ext_act(fsdone,_,_).  % KNOWN BUG - FSs in suspended goals only are not extensionalised.

%extensionalise_list(FSList) :-
%  list_to_fss(FSList,FSs),
%  ext_act(FSs,edone,[]).

%list_to_fss([],fsdone).
%list_to_fss([FS|FSList],fs(FS,FSs)) :-
%  list_to_fss(FSList,FSs).

%check_pre_traverse(Type,TFS,FS,ExtQ,IntQ,FSs) if_b [!,traverseQ(ExtQ,FS,Type,TFS,FSs,ExtQ,IntQ)] :-
%  clause(extensional(Type),true).
%check_pre_traverse(Type,TFS,FS,ExtQ,IntQ,FSs) if_b
%  [check_post_traverse_occurs(Type,TFS,FS,cdone,ExtQ,IntQ,FSs)].

%check_post_traverse_occurs(Type,TFS,FS,Checks,ExtQ,IntQ,FSs) :-
%  member_eq(FS,IntQ) -> check_post_traverse_next(Checks,ExtQ,IntQ,FSs)
%  ; check_post_traverse(Type,TFS,Checks,ExtQ,[FS|IntQ],FSs).
			   
%check_post_traverse(Type,TFS,Checks,ExtQ,IntQ,FSs) if_b [!,SubGoal] :-
%  esetof(T,E^(clause(extensional(E),true),non_a_type(E),sub_type(T,E)),QueueTypes0),
%  check_post_traverse_approp(QueueTypes0,CloseTypes),
%  ord_subtract(QueueTypes0,CloseTypes,CheckTypes),
%  ord_union([0,bot,(a_ _)],QueueTypes0,QueueTypes),
%  approps(Type,FRs,N), N \== 0, Arity is N + 2, functor(TFS,tfs,Arity),
%  check_post_traverse_act(FRs,2,TFS,QueueTypes,CheckTypes,FSs,NewFSs,Checks,NewChecks),
%  ( NewChecks \== Checks -> SubGoal = check_post_traverse_next(NewChecks,ExtQ,IntQ,NewFSs)
%  ; NewFSs \== FSs -> SubGoal = ext_act(NewFSs,ExtQ,IntQ)
%  ; fail
%  ).
%check_post_traverse(_,_,Checks,ExtQ,IntQ,FSs) if_b
%  [check_post_traverse_next(Checks,ExtQ,IntQ,FSs)].
  
%check_post_traverse_act([],_,_,_,_,FSs,FSs,Checks,Checks).
%check_post_traverse_act([_:R|FRs],N,TFS,QueueTypes,CheckTypes,FSsIn,FSsOut,ChecksIn,ChecksOut) :-
%  NewN is N + 1, arg(N,TFS,V),
%  ( memberchk(R,QueueTypes) -> check_post_traverse_act(FRs,NewN,TFS,QueueTypes,CheckTypes,fs(V,FSsIn),
%						       FSsOut,ChecksIn,ChecksOut)
%  ; memberchk(R,CheckTypes) -> check_post_traverse_act(FRs,NewN,TFS,QueueTypes,CheckTypes,FSsIn,FSsOut,
%						       check(V,ChecksIn),ChecksOut)
%  ; check_post_traverse_act(FRs,NewN,TFS,QueueTypes,CheckTypes,FSsIn,FSsOut,ChecksIn,ChecksOut)
%  ).

%check_post_traverse_next(cdone,ExtQ,IntQ,FSs) :-
%  ext_act(FSs,ExtQ,IntQ).
%check_post_traverse_next(check(FS,Checks),ExtQ,IntQ,FSs) :-
%  '$get_attributes'(FS,TFS,Type),
%  check_post_traverse_occurs(Type,TFS,FS,Checks,ExtQ,IntQ,FSs).

%check_post_traverse_approp(CheckTypesInit,CheckTypes) :-
%  esetof(T,F^C^(member(C,CheckTypesInit),approp(F,T,C)),AppropTypes),
%  ord_union(CheckTypesInit,AppropTypes,CheckTypesMid,NewCheckTypes),
%  check_post_traverse_approp_act(NewCheckTypes,CheckTypesMid,CheckTypes).

%check_post_traverse_approp_act([],CheckTypes,CheckTypes).
%check_post_traverse_approp_act([_|_],CheckTypesMid,CheckTypes) :-
%  check_post_traverse_subtype(CheckTypesMid,CheckTypes).

%check_post_traverse_subtype(CheckTypesInit,CheckTypes) :-
%  esetof(T,C^(member(C,CheckTypesInit),sub_type(T,C)),SuperTypes),
%  ord_union(CheckTypesInit,SuperTypes,CheckTypesMid),
%  check_post_traverse_approp(CheckTypesMid,CheckTypes).

% ------------------------------------------------------------------------------
% traverseQ(ExtQRest:<ext>s,ExtQ:<ext>s,Ref:<ref>,SVs:<svs>,FSs:<fs>s,
%           Ineqs:<ineq>s,Iqs:<iq>s)
% ------------------------------------------------------------------------------
% Add Ref-SVs to the extensionality queue, ExtQ.  Only ExtQRest remains to
% traverse (ExtQ is the head).  If the difference is unbound, then add Ref-SVs
% to the end.  If the first element on the difference is the same FS as
% Ref-SVs, then no need to add.  If the first element can be extensionally
% identified with Ref-SVs, then stop looking, since now Ref-SVs is the same as
% that FS.  If none of these, then go on to the next element.
% ------------------------------------------------------------------------------
%traverseQ(edone,FS,Type,TFS,FSs,ExtQ,IntQ) :-
%  check_post_traverse(Type,TFS,cdone,ext(FS,Type,TFS,ExtQ),IntQ,FSs).
%traverseQ(ext(EFS,EType,ETFS,ERest),FS,Type,TFS,FSs,ExtQ,IntQ) :-
%   EFS == FS -> ext_act(FSs,ExtQ,IntQ)
% ; iso_seq_act(FS,EFS,Type,EType,TFS,ETFS,done) -> check_post_traverse(Type,TFS,cdone,ExtQ,IntQ,FSs)
% ; traverseQ(ERest,FS,Type,TFS,FSs,ExtQ,IntQ).

% ------------------------------------------------------------------------------
% match_list(Sort:<type>,Vs:<vs>,Tag:<var>,SVs:<svs>,Right:<int>,N:<int>,
%            Dtrs:<ints>,DtrsRest:<var>,NextRight:<int>,Chart:<chart>,
%            IqsIn:<iqs>,IqsOut:<iqs>)
% ------------------------------------------------------------------------------
% Run-time predicate compiled into rules.  Matches a list of cats in Chart,
%  specified by Sort(Vs), to span an edge to OldRight, the first of which is 
%  Tag-SVs, which spans to Right.  Also matches an edge for the next category 
%  of the current rule to use (necessary because an initial empty-list cats 
%  matches nothing).
% ------------------------------------------------------------------------------
match_list(Sort,ListFS,HdPos,TlPos,FS,Right,N,[N|DtrsMid],DtrsRest,Chart,NextRight,
	   DtrStore,DtrStoreRest) :-
  sub_type(ne_list,Sort),
  !, arg(HdPos,ListFS,FS), % no need to fill this - intro restr is bot
  arg(TlPos,ListFS,TlFS),  % no need to fill this - list and bot are both invalid.
  add_to_store(DtrStore,FS,DtrStoreMid),
  deref(TlFS,_,TlSort,_),
  match_list_rest(TlSort,TlFS,HdPos,TlPos,Right,NextRight,DtrsMid,DtrsRest,Chart,
		  DtrStoreMid,DtrStoreRest).

match_list(Sort,_,_,_,_,_,_,_,_,_,_,_,_) :-
  error_msg((nl,write('error: cats> value with sort, '),write(Sort),
            write(' is not a valid argument (e_list or ne_list)'))).

% ------------------------------------------------------------------------------
% match_list_rest(Sort<type>,Vs:<vs>,Right:<int>,NewRight:<int>,
%                 DtrsRest:<ints>,DtrsRest2:<var>,Chart:<chart>,IqsIn:<iqs>,
%                 IqsOut:<iqs>)
% ------------------------------------------------------------------------------
% same as match_list, except edge spans from Right to NewRight, and no
%  matches for the next category are necessary
% ------------------------------------------------------------------------------
match_list_rest(Sort,_,_,_,Right,Right,DtrsRest,DtrsRest,_,Store,Store) :- 
  sub_type(e_list,Sort),
  !.
match_list_rest(Sort,ListFS,HdPos,TlPos,Right,NewRight,[N|DtrsRest],DtrsRest2,Chart,
		DtrStore,DtrStoreRest) :-
  sub_type(ne_list,Sort),
  !, arg(HdPos,ListFS,HdFS), % no need to fill this - intro restr is bot
  get_edge(Right,Chart,N,MidRight,HdFS,_,_),
  arg(TlPos,ListFS,TlFS),    % no need to fill this - list and bot are both invalid.
  add_to_store(DtrStore,HdFS,DtrStoreMid),
  deref(TlFS,_,TlSort,_),
  match_list_rest(TlSort,TlFS,HdPos,TlPos,MidRight,NewRight,DtrsRest,DtrsRest2,Chart,
		  DtrStoreMid,DtrStoreRest).
match_list_rest(Sort,_,_,_,_,_,_,_,_,_,_) :-
  error_msg((nl,write('error: cats> value with sort, '),write(Sort),  % KNOWN BUG: may report bot on 
            write(' is not a valid argument (e_list or ne_list)'))).  %  unfilled value when real type is list.

generate_apply_forall_rule(DtrStore,MotherFSVar,RuleName,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,PGoals,PGoalsRest) :-
  guarded_forall_rule(_,_,_,_,_)
  -> generate_apply_forall_rule_act(DtrStore,MotherFSVar,RuleName,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,
                               PGoals,PGoalsRest)
  ; guarded_forall_rule_hook(_,_,_,_,_)
  -> generate_apply_forall_rule_act(DtrStore,MotherFSVar,RuleName,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,
                               PGoals,PGoalsRest)
  ; PGoalsRest = PGoals, FSsOut = FSsIn, MFSOut = MFSIn.

generate_apply_forall_rule_act(DtrStore,MotherFSVar,RuleName,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,
                               PGoals,PGoalsRest) :-
  DtrStore = [CompileTimeDtrs | RunTimeDtrs],
  ( ale_lists_defined -> CombinedStore = ArgStore ; CombinedStore = (a_ ArgStore) ),
  bind_dtrs(CompileTimeDtrs,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,ArgStore,RunTimeDtrs,PGoals,
	    [apply_forall_rule(CombinedStore,MotherFSVar,RuleName)|PGoalsRest]).

guarded_forall_rule(N,R,M,D,B) :-
  current_predicate(forall,(_ forall _)), (N forall R rule M ===> D do B).
guarded_forall_rule_hook(N,R,M,D,B) :-
  current_predicate(forall_hook,(_ forall_hook _)), (N forall_hook R rule M ===> D do B).

apply_forall_rule(_,_,_) if_b [true] :-
  \+ guarded_forall_rule(_,_,_,_,_),
  \+ guarded_forall_rule_hook(_,_,_,_,_),
  !.
apply_forall_rule(Dtrs,MotherFS,RuleName) if_b Goals :-
%  ( ale_lists_defined -> Goals = [add_to(DtrStore,Dtrs)|GoalsMid]
%  ; Dtrs = (a_ DtrStore), GoalsMid = Goals
%  ),
  ebagof(forall_rule(Name,DSParm,MFSParm,RParm),M^D^R^B^(( guarded_forall_rule(Name,R,M,D,B)
                                                         ; guarded_forall_rule_hook(Name,R,M,D,B)
                                                         ),
					                 MFSParm = MotherFS, DSParm = Dtrs,
						         RParm = RuleName),Goals).

forall_rule(_,_,_,_) if_b [true] :-
  \+ guarded_forall_rule(_,_,_,_,_),
  \+ guarded_forall_rule_hook(_,_,_,_,_),
  !.
forall_rule(_,_,_,_) if_b _ :-
  findall(Name,guarded_forall_rule(Name,_,_,_,_),Names,NamesRest),
  findall(Name,guarded_forall_rule_hook(Name,_,_,_,_),NamesRest),
  has_duplicates(Names),
  append(_,[Name|Rest],Names), member_eq(Name,Rest),
  raise_exception(ale(forall_rule_dup(Name))).
forall_rule(Name,Dtrs,MotherFS,RuleName) if_b Goals :-
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(EMFS),
  empty_avl(ENVs),
  ( guarded_forall_rule(Name,RNArg,MDesc,DtrsDesc,Body)
  ; guarded_forall_rule_hook(Name,RNArg,MDesc,DtrsDesc,Body)
  ),
  desc_varfs_desc([MDesc|DtrsDesc],[],DescVars,[],_,[],ENVs),
  sort(DescVars,SortedDescVars),
  list_to_nv_unseen(SortedDescVars,DescNVs),
  compile_body((prolog(RuleName=RNArg) -> when((MotherFS=MDesc,Dtrs=DtrsDesc),Body) ; true),
	       Goals,[],serial,VarsIn,_,_,FSsIn,_,EMFS,_,DescNVs,[],[]).

add_to_store(Store,Head,Tail) if_b [] :-
  ale_lists_defined -> clause(fcolour(hd,HdPos,_),true),
                       clause(fcolour(tl,TlPos,_),true),
                       bind_mgsat(ne_list,Store,_),
                       arg(HdPos,Store,Head),
                       arg(TlPos,Store,Tail)
 ; Store = [Head|Tail].

add_to_store(Store,Head) if_b [] :-
  ale_lists_defined -> clause(fcolour(hd,HdPos,_),true),
                       clause(fcolour(tl,TlPos,_),true),
                       bind_mgsat(ne_list,Store,_),
                       arg(HdPos,Store,Head),
                       arg(TlPos,Store,Tail),
                       bind_mgsat(e_list,Tail,_)
 ; Store = [Head].

terminate_store(Store) if_b [] :-
  ale_lists_defined -> bind_mgsat(e_list,Store,_)
 ;  Store = [].

suspend_cats(DtrStoreList,TailFS,ContinuationList) :-
  when(nonvar(DtrStoreList),suspend_cats_act(DtrStoreList,TailFS,ContinuationList)).
suspend_cats_act([],TailFS,[]) :-
  deref(TailFS,TFS,Type,AttPos),
  add_to_type(e_list,Type,TFS,AttPos).
suspend_cats_act([FS|Rest],TailFS,ContinuationList) :-
  deref(TailFS,TFS,Type,AttPos),
  ( add_to([FS|NewTailFS],TailFS,Type,TFS,AttPos,list),
    suspend_cats(Rest,NewTailFS,ContinuationList)
  ; add_to_type(e_list,Type,TFS,AttPos),
    ContinuationList = [FS|Rest]
  ).

list_to_store(X,Store) :-
  var(X),
  !, ( ale_lists_defined -> suspend_store_ale(X,Store)
     ; suspend_store_prolog(X,Store)
     ).
list_to_store([],Store) :- terminate_store(Store).
list_to_store([Head|Tail],Store) :-
  add_to_store(Store,Head,StoreRest),
  list_to_store(Tail,StoreRest).

suspend_store_prolog(X,Store) :-
  when(nonvar(Store),suspend_store_prolog_act(Store,X)).
suspend_store_prolog_act([],[]).
suspend_store_prolog_act([Head|Tail],[Head|Rest]) :-
  suspend_store_prolog(Rest,Tail).

suspend_store_ale(X,Store) :-
  ale(when(Store=(e_list;ne_list),prolog(suspend_store_ale_act(Store,X)))).
suspend_store_ale_act(Store,X) :-
  get_type(Store,Type),
  ( sub_type(ne_list,Type) -> clause(fcolour(hd,HdPos,_),true),
                              arg(HdPos,Store,FS),
                              X = [FS|Rest],
                              clause(fcolour(tl,TlPos,_),true),
                              arg(TlPos,Store,Tail),
                              suspend_store_ale(Rest,Tail)
  ; % sub_type(e_list,Type),
    X = []
  ).

ale_lists_defined :-
  sub_type(list,e_list), sub_type(list,ne_list),
  approps(e_list,[],_0),
  approp(hd,ne_list,bot), approp(tl,ne_list,list).

% ==============================================================================
% Chart Parser
% ==============================================================================

% ------------------------------------------------------------------------------
% rec(+Ws:<word>s, ?FS:<tfs>, -Residue:<res>)
% ------------------------------------------------------------------------------
% Ws can be parsed as category FS (with inequations); Residue
%  uninstantiated to start.
% ------------------------------------------------------------------------------
:- dynamic num/1, to_rebuild/1, solution/1, edge/7, parsing/1, edgenum/2.

rec(Ws,FS,Residue) :-  
  rec(Ws,FS,bot,Residue).
	
%  clear,
%  assert(parsing(Ws)),
%  ( current_predicate(lex,lex(_,_))
%  -> reverse_count_lex_check(Ws,[],WsRev,0,Length),
%     CLength is Length - 1,
%     functor(Chart,chart,CLength),
%     build(WsRev,Length,Chart),
%     retract(to_rebuild(Index)),
%     call_residue((clause(edge(Index,0,Length,FS,_,_),true)
%%		   ,extensionalise(FS)
%		  ),Residue),
%     assert(solution(Index))
%  ; raise_exception(ale(no_lex))
%  ).

% Maybe should reindex asserted edges on right node to make this search a little faster.

% ------------------------------------------------------------------------------
% rec(+Ws:<word>s, ?FS:<tfs>, ?Desc:<desc>, -Residue:<res>)
% ------------------------------------------------------------------------------
% Like rec/3, but FS also satisfies description, Desc.
% ------------------------------------------------------------------------------
rec(Ws,FS,Desc,Residue) :-
  rec(Ws,FS,Desc,Residue,_,_).

rec(Ws,FS,Desc,Residue,Index) :-
  rec(Ws,FS,Desc,Residue,_,Index).

rec(Ws,FS,Desc,Residue,Time,Index) :-
  clear,
  assert(parsing(Ws)),
  ( current_predicate(lex,lex(_,_))
  -> reverse_count_lex_check(Ws,[],WsRev,0,Length,[]),
     rec_chart_init(Length,Chart),
     statistics(walltime,_),
     on_exception(Exception,build(WsRev,Length,Chart),build_exn(Exception)),
     statistics(walltime,[_,BuildTime]),
     retract(to_rebuild(Index)),
     call_residue((clause(edge(Index,0,Length,FS,FSRes,_,_),true),
                   call(FSRes),
                   (Desc == bot -> DescTime = 0
		   ; secret_noadderrs_toggle(Mode),
		     statistics(walltime,_),
                     add_to(Desc,FS),
		     statistics(walltime,[_,DescTime]),
                     secret_adderrs_toggle(Mode)
		   )
		  ),FS,Residue),
     Time is BuildTime + DescTime,
     assert(solution(Index))
  ; raise_exception(ale(no_lex))
  ).

rec_chart_init(Length,Chart) :-
  CLength is Length - 1,
  functor(Chart,chart,CLength),
  ( current_predicate(chart_init_hook,chart_init_hook(_,_)) -> call_all(chart_init_hook(Length,Chart)) ; true).

% ------------------------------------------------------------------------------
% build(Ws:<word>s, Right:<int>, Chart:<chart>)
% ------------------------------------------------------------------------------
% fills in inactive edges of chart from beginning to Right using 
% Ws, representing words in chart in reverse order.  Chart is the functor
% 'chart' of arity equal to the length of the input string (which is thus
%  bounded at 255).
% ------------------------------------------------------------------------------
build([W|Ws],Right,Chart):-
  RightMinus1 is Right - 1,
% write(user_error,RightMinus1),nl(user_error), % DEBUG
% flush_output(user_error), % DEBUG
  (
% empty_cat(N,Right,Tag,SVs,Iqs,_,_),
%    rule(Tag,SVs,Iqs,Right,Right,empty(N,Right))
%  ;
    lex(W,FS),
%    lex_goal(_-(a_ W),Tag-SVs),
    add_edge(RightMinus1,Right,FS,[],lexicon,Chart)
  ; ( RightMinus1 =:= 0
      -> true
       ; rebuild_edges(Edges),
         arg(RightMinus1,Chart,Edges),
         build(Ws,RightMinus1,Chart)
    )
  ).
%build([],_):-
%  empty_cat(N,0,Tag,SVs,Iqs,_,_),
%  rule(Tag,SVs,Iqs,0,0,empty(N,0)).
build([],_,_).

% build_exn/1: exception handler for build/3.  This traps exceptions that terminate
%  chart construction but not parsing.
build_exn(ale(edgelimit_exceeded(Limit))) :-
  !,print_message(warning,ale(edgelimit_exceeded(Limit))).
build_exn(Exception) :-
  raise_exception(Exception).

% ------------------------------------------------------------------------------ 
% rebuild_edges(Edges:<edge>s)
% ------------------------------------------------------------------------------
% Copy non-looping edges asserted into the database in the most recent pass 
%  (all of the edges from the most recent node) into an edge/7 structure on 
%  the heap for inclusion into the chart.  Copying them once now means that we 
%  only copy an edge once in total rather than every time a rule asks for it.
%  We can do this because we have closed the rules under prefixes of empty 
%  categories; so we know that no edge will be needed until closure at the next
%  node begins.
% ------------------------------------------------------------------------------
rebuild_edges(Edges) :-
  retract(to_rebuild(Index))
  -> clause(edge(Index,_,R,FS,ERes,D,RN),true),
     call(ERes), % SP4: reattach residue to edge FS
     Edges = edge(Index,R,FS,D,RN,EdgesRest),
     rebuild_edges(EdgesRest)
   ; Edges = nomore.

% ------------------------------------------------------------------------------
% add_edge_deref(Left:<int>, Right:<int>, Tag:<var_tag>, SVs:<svs>, 
%                Iqs:<ineq>s,Dtrs:<fs>s,RuleName,Chart:<chart>)             eval
% ------------------------------------------------------------------------------
% adds dereferenced category Tag-SVs,Iqs as inactive edge from Left to Right;
% check for any rules it might start, then look for categories in Chart
% to complete those rules
% ------------------------------------------------------------------------------
%add_edge_deref(Left,Right,Tag,SVs,Dtrs,RuleName,Chart):-
%  fully_deref(Tag,SVs,TagOut,SVsOut),
%  (ale_flag(subtest,off)
%  -> (edge_assert(Left,Right,TagOut,SVsOut,Dtrs,RuleName,N)
%     -> try_rule(RuleName,TagOut,SVsOut,Left,Right,N,Chart))
%   ; (subsumed(Left,Right,TagOut,SVsOut,Dtrs,RuleName)
%     -> fail
%      ; (edge_assert(Left,Right,TagOut,SVsOut,Dtrs,RuleName,N)
%        -> try_rule(RuleName,TagOut,SVsOut,Left,Right,N,Chart)))).

%add_edge_deref(Left,Right,FS,Dtrs,RuleName,Chart):-
%  deref(FS,Tag,SVs),
%  fully_deref(Tag,SVs,TagOut,SVsOut),
%  (ale_flag(subtest,off)
%  -> (edge_assert(Left,Right,TagOut,SVsOut,Dtrs,RuleName,N)
%     -> try_rule(RuleName,TagOut,SVsOut,Left,Right,N,Chart))
%   ; (subsumed(Left,Right,TagOut,SVsOut,Dtrs,RuleName)
%     -> fail
%      ; (edge_assert(Left,Right,TagOut,SVsOut,Dtrs,RuleName,N)
%        -> try_rule(RuleName,TagOut,SVsOut,Left,Right,N,Chart)))).

add_edge(Left,Right,FSOut,Dtrs,RuleName,Chart):-
  (ale_flag(subtest,off)
  -> (edge_assert(Left,Right,FSOut,Dtrs,RuleName,N)
     -> try_rule(RuleName,FSOut,Left,Right,N,Chart))
   ; (subsumed(Left,Right,FSOut,Dtrs,RuleName)
     -> fail
      ; (edge_assert(Left,Right,FSOut,Dtrs,RuleName,N)
        -> try_rule(RuleName,FSOut,Left,Right,N,Chart)))).

clear_index :-
  retractall(index(_)),
  asserta(index(0)).
  
clear_edgenum :-
  retractall(edgenum(_,_)),
  ale_flag(edgelimit,Limit),
  asserta(edgenum(0,Limit)).

genindex(N) :-
  retract(index(N)),
  NewN is N+1,
  asserta(index(NewN)).

gen_edgenum(N) :-
  retract(edgenum(N,Limit)),
  NewN is N + 1,
  asserta(edgenum(NewN,Limit)),
  ( Limit \== inf, NewN > Limit -> raise_exception(ale(edgelimit_exceeded(Limit))) % SP4: no built-in repn of infinity
  ; true
  ).

soln(X,N) :-
   SolnModes = [index,indices,num],
   if(member(X,SolnModes),
      soln_act(X,N),
      raise_exception(domain_error(soln(X,N),1,SolnModes,X))).
soln_act(index,I) :- clause(solution(I),true).
soln_act(indices,Is) :- findall(I,soln_act(index,I),Is).
soln_act(num,N) :- soln_act(indices,Is),length(Is,N).

% Should probably add these:
% soln(tfs,FS): w/ or w/o residue?
% soln(time,T): maybe charttime?

gen_emptynum(N) :-
  retract(emptynum(N)),
  NewN is N-1,
  asserta(emptynum(NewN)).

count_edges(N):-
  setof(edge(M,X,Y,Z,R,D,RN),edge(M,X,Y,Z,R,D,RN),Es),
  length(Es,N).

% try_rule
try_rule(_,_,_,_,_,_) if_b [fail] :-
  \+ clause(alec_rule(_,_,_,_,_,_,_,_,_),true),
  !.
try_rule(_,_,_,_,_,_) if_b [fail] :-
  \+ clause(rule_compiled(_),true),
  !.
try_rule(_,FS,Left,Right,N,Chart) if_b [rule(_,FS,Left,Right,N,Chart)] :-
  ale_flag(ruleindex,off),
  !.
try_rule(BottomName,FS,Left,Right,N,Chart) if_b
         [rule(TopName,FS,Left,Right,N,Chart)] :-
  secret_noadderrs_toggle(_),		 
  clause(rule_compiled(TopName),true),
  clause(alec_rule(TopName,TopDaughters,_,TopMother,TopRes,_,_,TopDtrStoreList,TopDtrStoreRest),true),
  call(TopRes),
  clause(rule_compiled(BottomName),true),
  clause(alec_rule(BottomName,BottomDaughters,_,BottomMother,BottomRes,_,_,BotDtrStoreList,BotDtrStoreRest),true),
  call(BottomRes),
% write(TopName), write(' '), write(BottomName), nl, flush_output, % DEBUG
  \+ \+ ((ale_flag(ruleindexscope,point) -> true ; try_rule_dtrs(BottomDaughters,BotDtrStoreRest)),
         add_to(BottomMother,FS,bot,tfs(bot,_),FS,bot), % Bottom mother is compatible with leftmost top dtr
         (ale_flag(ruleindexscope,localresolve) -> list_to_store(BotDtrStoreList,BotDtrStore),
                                               apply_forall_rule(BotDtrStore,FS,BottomName)
         ; true),
         deref(FS,TFS,Type,AttPos),
         try_rule_dtrs(TopDaughters,FS,Type,TFS,AttPos,TopDtrStoreRest),
         (ale_flag(ruleindexscope,point) -> true ; add_to(TopMother,TopFS,bot,tfs(bot,_),TopFS,bot)),
         (ale_flag(ruleindexscope,localresolve) -> list_to_store(TopDtrStoreList,TopDtrStore),
                                               apply_forall_rule(TopDtrStore,TopFS,TopName)
         ; true)).
try_rule(lexicon,FS,Left,Right,N,Chart) if_b
         [rule(_,FS,Left,Right,N,Chart)].
% clause(alec_rule(DtrsName,_,_,_,_,_,_,_),true).
% could try to distill a satisfier from lexicon to match against Dtrs

try_rule_dtrs((cat> Dtr),FS,Type,TFS,AttPos,[FS]) :-
  add_to(Dtr,FS,Type,TFS,AttPos,bot).
try_rule_dtrs((sem_head> Dtr),FS,Type,TFS,AttPos,[FS]) :-
  add_to(Dtr,FS,Type,TFS,AttPos,bot).
try_rule_dtrs((cats> Cats),FS,_Type,_TFS,_AttPos,[FS|DtrStoreRest]) :-
  add_to(Cats,LFS,bot,tfs(bot,_),LFS,bot),
  deref(LFS,LTFS2,LType2,LAttPos),
  add_to_type(ne_list,LType2,LTFS2,LAttPos),  % leftmost daughter is head of this list
  clause(fcolour(hd,HdPos,_),true),
  arg(HdPos,LFS,FS),  % no need to fill this - intro restr is bot
  ( ale_flag(ruleindexscope,point) -> true
  ; clause(fcolour(tl,TlPos,_),true),
    arg(TlPos,LFS,TailFS),
    try_rule_dtrs(remainder(TailFS),DtrStoreRest)).
try_rule_dtrs(remainder(RFS),FS,_Type,_TFS,_AttPos,[FS|DtrStoreRest]) :-
  deref(RFS,RTFS,RType,RAttPos),
  add_to_type(ne_list,RType,RTFS,RAttPos),  % leftmost daughter is head of this list
  clause(fcolour(hd,HdPos,_),true),
  arg(HdPos,RFS,FS),  % no need to fill this - intro restr is bot
  ( ale_flag(ruleindexscope,point) -> true
  ; clause(fcolour(tl,TlPos,_),true),
    arg(TlPos,RFS,TailFS),
    try_rule_dtrs(remainder(TailFS),DtrStoreRest)).
try_rule_dtrs(((cat> Dtr),DtrsRest),FS,Type,TFS,AttPos,[FS|DtrStoreRest]) :-
  !, add_to(Dtr,FS,Type,TFS,AttPos,bot),
  ( ale_flag(ruleindexscope,point) -> true
  ; try_rule_dtrs(DtrsRest,DtrStoreRest)).
try_rule_dtrs(((sem_head> Dtr),DtrsRest),FS,Type,TFS,AttPos,[FS|DtrStoreRest]) :-
  !, add_to(Dtr,FS,Type,TFS,AttPos,bot),
  ( ale_flag(ruleindexscope,point) -> true
  ; try_rule_dtrs(DtrsRest,DtrStoreRest)).
try_rule_dtrs(((cats> Cats),Rest),FS,Type,TFS,AttPos,DtrStoreList) :-
  !, add_to(Cats,LFS,bot,tfs(bot,_),LFS,bot),
  deref(LFS,LTFS2,LType2,LAttPos),
  ( add_to_type(e_list,LType2,LTFS2,LAttPos),  % otherwise leftmost daughter occurs later
    try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)
  ; add_to_type(ne_list,LType2,LTFS2,LAttPos),  % leftmost daughter is head of list if non-empty
    clause(fcolour(hd,HdPos,_),true),
    arg(HdPos,LFS,FS), % no need to fill this - intro restr is bot
    ( ale_flag(ruleindexscope,point) -> true
    ; DtrStoreList = [FS|DtrStoreRest],
      clause(fcolour(tl,TlPos,_),true),
      arg(TlPos,LFS,TailFS),
      try_rule_dtrs((remainder(TailFS),Rest),DtrStoreRest))
  ).
try_rule_dtrs((remainder(RFS),Rest),FS,Type,TFS,AttPos,DtrStoreList) :-
  !, deref(RFS,RTFS,RType,RAttPos),
  ( add_to_type(e_list,RType,RTFS,RAttPos),  % otherwise leftmost daughter occurs later
    try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)
  ; add_to_type(ne_list,RType,RTFS,RAttPos),  % leftmost daughter is head of this list if non-empty
    clause(fcolour(hd,HdPos,_),true),
    arg(HdPos,RFS,FS), % no need to fill this - intro restr is bot
    ( ale_flag(ruleindexscope,point) -> true
    ; DtrStoreList = [FS|DtrStoreRest],
      clause(fcolour(tl,TlPos,_),true),
      arg(TlPos,RFS,TailFS),
      try_rule_dtrs((remainder(TailFS),Rest),DtrStoreRest))
  ).
try_rule_dtrs((goal> GoalDesc,Rest),FS,Type,TFS,AttPos,DtrStoreList) :-
  !, ( ale_flag(ruleindexscope,point) -> try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)
     ; ale_flag(ruleindexscope,localresolve) -> query_goal(GoalDesc), try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)
     ; try_rule_goal_args(GoalDesc),
       try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)).
try_rule_dtrs((sem_goal> GoalDesc,Rest),FS,Type,TFS,AttPos,DtrStoreList) :-
     ( ale_flag(ruleindexscope,point) -> try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)
     ; ale_flag(ruleindexscope,localresolve) -> query_goal(GoalDesc), try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)
     ; try_rule_goal_args(GoalDesc),
       try_rule_dtrs(Rest,FS,Type,TFS,AttPos,DtrStoreList)).

% this version is never called when ale_flag(ruleindexscope,point)
try_rule_dtrs((cat> Dtr),[FS]) :-
  add_to(Dtr,FS,bot,tfs(bot,_),FS,bot).
try_rule_dtrs((sem_head> Dtr),[FS]) :-
  add_to(Dtr,FS,bot,tfs(bot,_),FS,bot).
try_rule_dtrs((cats> Cats),DtrStoreList) :-
  add_to(Cats,LFS,bot,tfs(bot,_),LFS,bot),
  get_type(LFS,LType2),
  ( sub_type(ne_list,LType2) -> clause(fcolour(hd,HdPos,_),true),
                                arg(HdPos,LFS,FS),  % no need to fill this - intro restr is bot
                                DtrStoreList = [FS|DtrStoreRest],  % leftmost daughter is head of this list
                                clause(fcolour(tl,TlPos,_),true),
                                arg(TlPos,LFS,TailFS),
                                try_rule_dtrs(remainder(TailFS),DtrStoreRest)
  ; sub_type(e_list,LType2) ->  DtrStoreList = []
  ; ale_flag(ruleindexscope,localresolve) -> suspend_cats(DtrStoreList,LFS,[])
  ; true).
try_rule_dtrs(remainder(RFS),DtrStoreList) :-
  get_type(RFS,RType),
  ( sub_type(ne_list,RType) -> clause(fcolour(hd,HdPos,_),true),
                               arg(HdPos,RFS,FS),  % no need to fill this - intro restr is bot
                               DtrStoreList = [FS|DtrStoreRest],
                               clause(fcolour(tl,TlPos,_),true),
                               arg(TlPos,RFS,TailFS),
                               try_rule_dtrs(remainder(TailFS),DtrStoreRest)
  ; sub_type(e_list,RType) -> DtrStoreList = []
  ; ale_flag(ruleindexscope,localresolve) -> suspend_cats(DtrStoreList,RFS,[])
  ; true).
try_rule_dtrs((goal> GoalDesc),[]) :-
  !, ( ale_flag(ruleindexscope,localresolve) -> query_goal(GoalDesc)
     ; try_rule_goal_args(GoalDesc)
     ).
try_rule_dtrs((sem_goal> GoalDesc),[]) :-
  !, ( ale_flag(ruleindexscope,localresolve) -> query_goal(GoalDesc)
     ; try_rule_goal_args(GoalDesc)
     ).
try_rule_dtrs(((cat> Dtr),DtrsRest),[FS|DtrStoreRest]) :-
  !, add_to(Dtr,FS,bot,tfs(bot,_),FS,bot),
  try_rule_dtrs(DtrsRest,DtrStoreRest).
try_rule_dtrs(((sem_head> Dtr),DtrsRest),[FS|DtrStoreRest]) :-
  !, add_to(Dtr,FS,bot,tfs(bot,_),FS,bot),
  try_rule_dtrs(DtrsRest,DtrStoreRest).
try_rule_dtrs(((cats> Cats),Rest),DtrStoreList) :-
  !, add_to(Cats,LFS,bot,tfs(bot,_),LFS,bot),
  get_type(LFS,LType2),
  ( sub_type(ne_list,LType2) -> clause(fcolour(hd,HdPos,_),true),
                                arg(HdPos,LFS,FS), % no need to fill this - intro restr is bot
                                DtrStoreList = [FS|DtrStoreRest],
                                clause(fcolour(tl,TlPos,_),true),
                                arg(TlPos,LFS,TailFS),
                                try_rule_dtrs((remainder(TailFS),Rest),DtrStoreRest)
  ; sub_type(e_list,LType2) -> try_rule_dtrs(Rest,DtrStoreList)
  ; ale_flag(ruleindexscope,localresolve) -> suspend_cats(DtrStoreList,LFS,DtrStoreRest),
                                         try_rule_dtrs(Rest,DtrStoreRest)
  ; true).
try_rule_dtrs((remainder(RFS),Rest),DtrStoreList) :-
  !, get_type(RFS,RType),
  ( sub_type(ne_list,RType) -> clause(fcolour(hd,HdPos,_),true),
                                arg(HdPos,RFS,FS), % no need to fill this - intro restr is bot
                                DtrStoreList = [FS|DtrStoreRest],
                                clause(fcolour(tl,TlPos,_),true),
                                arg(TlPos,RFS,TailFS),
                                try_rule_dtrs((remainder(TailFS),Rest),DtrStoreRest)
  ; sub_type(e_list,RType) -> try_rule_dtrs(Rest,DtrStoreList)
  ; ale_flag(ruleindexscope,localresolve) -> suspend_cats(DtrStoreList,RFS,DtrStoreRest),
                                         try_rule_dtrs(Rest,DtrStoreRest)
  ; true).
try_rule_dtrs((goal> GoalDesc,Rest),DtrStoreList) :-
  !, ( ale_flag(ruleindexscope,localresolve) -> query_goal(GoalDesc), try_rule_dtrs(Rest,DtrStoreList)
     ; try_rule_goal_args(GoalDesc),
       try_rule_dtrs(Rest,DtrStoreList)).
try_rule_dtrs((sem_goal> GoalDesc,Rest),DtrStoreList) :-
     ( ale_flag(ruleindexscope,localresolve) -> query_goal(GoalDesc), try_rule_dtrs(Rest,DtrStoreList)
     ; try_rule_goal_args(GoalDesc),
       try_rule_dtrs(Rest,DtrStoreList)).

try_rule_goal_args(\+(_)) :- !.  % if it succeeds, goal could still fail; if it fails, \+ succeeds.
try_rule_goal_args(prolog(_)) :-  !.  % Prolog hooks are scary - assume they will succeed
try_rule_goal_args(prolog(_,_)) :- !.
try_rule_goal_args(!) :- !.
try_rule_goal_args(fail) :- !,fail.
try_rule_goal_args(when(_,_)) :-  !. % guard could fail, then this succeeds
try_rule_goal_args((G1,G2)) :-
  !, try_rule_goal_args(G1),
  try_rule_goal_args(G2).
try_rule_goal_args((G1;G2)) :-
  !, ( try_rule_goal_args(G1)
     ; try_rule_goal_args(G2)
     ).
try_rule_goal_args((IfG -> ThenG ; ElseG)) :-
  !, ( try_rule_goal_args((IfG,ThenG))
     ; try_rule_goal_args(ElseG)
     ).
try_rule_goal_args((IfG -> ThenG)) :-
  !, try_rule_goal_args((IfG,ThenG)).
try_rule_goal_args(AtGD) :-
  AtGD =.. [_|ArgDescs],
  mg_sat_list(ArgDescs,_).

% ------------------------------------------------------------------------------
% get_edge(Left:<int>,Chart:<chart>,Index:<int>,Right:<int>,Tag:<ref>,
%          SVs:<svs>,EdgeIqs:<iqs>,Dtrs:<int>s,RuleName:<atom>)
% ------------------------------------------------------------------------------
% Retrieve an edge from the chart, which means either an empty category
% or one of the non-empty edges in Chart
% ------------------------------------------------------------------------------

get_edge(Right,_,empty(N,Right),Right,FS,Dtrs,RuleName) :-
  empty_cat(N,Right,FS,Dtrs,RuleName).
get_edge(Left,Chart,N,Right,FS,Dtrs,RuleName) :-
  Chart \== chart,  % SP4: arg/3 throws exception on atoms, so we need a guard
  arg(Left,Chart,Edges),
  edge_member(Edges,N,Right,FS,Dtrs,RuleName).
%  clause(edge(Left,N,Right,Tag,SVs,EdgeIqs,Dtrs,RuleName),true).

edge_member(edge(I,R,F,D,RN,Edges),N,Right,FS,Dtrs,RuleName) :-
  I = N, R = Right, F = FS, D = Dtrs, RN = RuleName
 ; edge_member(Edges,N,Right,FS,Dtrs,RuleName).  

% get_edge_ref(+Index,?Left,?Right,?FS,?DtrNums,?RuleName)
get_edge_ref(empty(N,Right),Right,Right,FS,DtrNums,RuleName) :-
  !,empty_cat(N,Right,FS,DtrNums,RuleName).
get_edge_ref(N,Left,Right,FS,DtrNums,RuleName) :-
  clause(edge(N,Left,Right,FS,Res,DtrNums,RuleName),true),
  call(Res).
  
% ------------------------------------------------------------------------------
% subsumed(Left:<int>,Right:<int>,FS:<tfs>,Dtrs:<int>s,RuleName)
% ------------------------------------------------------------------------------
% Check if any edge spanning Left to Right subsumes FS, the feature
%  structure of the candidate edge, or vice versa.  Succeeds based on whether
%  or not FS is subsumed - but all edges subsumed by FS are also
%  retracted.
% ------------------------------------------------------------------------------
subsumed(Left,Right,FS,Dtrs,RuleName) :-
  clause(to_rebuild(EI),true),
  clause(edge(EI,Left,Right,EFS,ERes,_,_),true), %this may have >1 soln
  call(ERes),
  empty_avl(H),
  empty_avl(K),
  frozen_term(FS,Frozen),
  frozen_term(EFS,EFrozen),
  filter_iqs(Frozen,Iqs,_),  % don't use other suspensions in subsumption calculation
  filter_iqs(EFrozen,EIqs,_),
  subsume(s(FS,EFS,bot,sdone),<,>,LReln,RReln,H,K,Iqs,EIqs),
  subsumed_act(RReln,LReln,EI,FS,Dtrs,RuleName,Left,Right).

subsumed_act(>,LReln,EI,FS,Dtrs,RuleName,Left,Right) :- %edge subsumes
  !,edge_discard(LReln,EI,FS,Dtrs,RuleName,Left,Right). % candidate 
subsumed_act(#,<,EI,FS,Dtrs,RuleName,Left,_) :- % candidate 
  edge_retract(Left,EI,FS,Dtrs,RuleName).       % subsumes edge
% subsumed_act(#,#,_,_,_,_,_,_) fails

% subsume(Ss,LeftRelnIn,RightRelnIn,LeftRelnOut,RightRelnOut,H,K,Iqs1,Iqs2)
% ------------------------------------------------------------------------------
% LeftRelnOut is bound to < if LeftRelnIn is not # and there exists a 
%  subsumption morphism, H (see Carpenter, 1992, p. 41) from FS1 to 
%  FS2, for every s(FS1,FS2,Restr,_) in Ss, and from the 
%  inequations in Iqs1 to those in Iqs2.  Otherwise, LeftRelnOut is bound to 
%  #.  RightRelnOut is bound to > if RightRelnIn is not #, and
%  a subsumption morphism, K, exists in the reverse direction, and is bound
%  otherwise to #.  It is expected that inequations irrelevant to the FS's in the
%  s-structures will have been pruned off.  If either FS1 or FS2 is uninstantiated
%  and unbound, they are interpreted to be of type Restr --- this saves us the
%  trouble of filling in lazy variables.
% ------------------------------------------------------------------------------
subsume(sdone,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs) :-
  subsume_iqs(Iqs,LRelnIn,LRelnOut,H),  % as a last resort, try to
  subsume_iqs(EIqs,RRelnIn,RRelnOut,K).  % disprove subsumption using ineqs
subsume(s(FS,EFS,Restr,Ss),LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs) :-
  avl_fetch(FS,H,HFS)
  -> (avl_fetch(EFS,K,KFS)  % first try to disprove subsumption using 
     -> (KFS == FS          %  observed structure sharing at current roots
        -> (HFS == EFS
           -> ((LRelnIn == #,RRelnIn == #)
              -> LRelnOut = #,RRelnOut = #  % we can quit once we show this
               ; subsume(Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs)
              )
            ; LRelnOut = #,
              (RRelnIn == #
              -> RRelnOut = #
               ; subsume(Ss,#,RRelnIn,#,RRelnOut,H,K,Iqs,EIqs)
              )
           )
         ; RRelnOut = #,
           (HFS == EFS
           -> (LRelnIn == #
              -> LRelnOut = #
               ; subsume(Ss,LRelnIn,#,LRelnOut,#,H,K,Iqs,EIqs)
              )
            ; LRelnOut = #, RRelnOut = #
           )
        )
     ; LRelnOut = #,
       (RRelnIn == #
       -> RRelnOut = #
        ; get_type(FS,Type), get_type(EFS,EType),
	  subsume_type(Type,EType,FS,EFS,Restr,Ss,#,RRelnIn,#,RRelnOut,H,K,Iqs,EIqs)
       )
    )
  ; (avl_fetch(EFS,K,KFS)
    -> RRelnOut = #,
       (LRelnIn == #
       -> LRelnOut = #
        ; get_type(FS,Type), get_type(EFS,EType),
	  subsume_type(Type,EType,FS,EFS,Restr,Ss,LRelnIn,#,LRelnOut,#,H,K,Iqs,EIqs)
       )
     ; get_type(FS,Type), get_type(EFS,EType),
       subsume_type(Type,EType,FS,EFS,Restr,Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs)
    ).

% next try to disprove subsumption using type information at root node
subsume_type(Type,EType,FS,EFS,_Restr,Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs)
  if_b [!,
       (LRelnIn == # -> LRelnOut = #, H = NewH
       ; avl_store(FS,H,EFS,NewH)
       ),
       (RRelnIn == # -> RRelnOut = #, K = NewK
       ; avl_store(EFS,K,FS,NewK)
       ),
       subsume(Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,NewH,NewK,Iqs,EIqs)] :-
  Type = 0,
  EType = 0.
subsume_type(Type,EType,FS,EFS,Restr,Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs)
  if_b [!,
       ( variant(Restr,EType) ->  (LRelnIn == # -> LRelnOut = #, H = NewH
				  ; avl_store(FS,H,EFS,NewH)
				  ),
	                          (RRelnIn == # -> RRelnOut = #, K = NewK
				  ; avl_store(EFS,K,FS,NewK)
				  ),
	                          subsume(NewSs,LRelnIn,RRelnIn,LRelnOut,RRelnOut,NewH,NewK,Iqs,EIqs)
       ; % sub_type(Restr,EType),
	 RRelnOut = #,
         (LRelnIn == # -> LRelnOut = #
	 ; avl_store(FS,H,EFS,NewH),
	   subsume(Ss,LRelnIn,#,LRelnOut,#,NewH,K,Iqs,EIqs)
	 )
      %; sub_type(EType,Restr) cannot happen - Restr is some feature's introduced value restr.
      %; LRelnOut = #, RRelnOut = # cannot happen either - all values are subsumed by MGSat(Restr)
       )] :-
  type(EType),
  ( clause(tmodule(EType,EModule),true)
  -> clause(marity(EModule,EArity),true),
     functor(EFS,EModule,EArity)
  ; true
  ),
  approps(EType,EFRs,_),
  append_s_lazy_right(EFRs,EFS,Ss,NewSs),
  Type = 0.
subsume_type((a_ X),EType,FS,EFS,Restr,Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs)
  if_b [!,
       ( variant(Restr,(a_ X)) ->  (LRelnIn == # -> LRelnOut = #, H = NewH
				 ; avl_store(FS,H,EFS,NewH)
				 ),
	                         (RRelnIn == # -> RRelnOut = #, K = NewK
				 ; avl_store(EFS,K,FS,NewK)
				 ),
	                         subsume(Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,NewH,NewK,Iqs,EIqs)
       ; % sub_type(Restr,(a_ X)),
	 LRelnOut = #,
         (RRelnIn == # -> RRelnOut = #
	 ; avl_store(EFS,K,FS,NewK),
	   subsume(Ss,#,RRelnIn,#,RRelnOut,H,NewK,Iqs,EIqs)
	 )
      %; sub_type(Type,Restr) cannot happen - Restr is some feature's introduced value restr.
      %; LRelnOut = #, RRelnOut = # cannot happen either - all values are subsumed by MGSat(Restr)
       )] :-
  EType = 0.
subsume_type((a_ _),EType,FS,EFS,_Restr,Ss,_LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs)
  if_b [!, LRelnOut = #,
        ( RRelnIn == # -> RRelnOut = #
	; avl_store(EFS,K,FS,NewK),
	  subsume(Ss,#,RRelnIn,#,RRelnOut,H,NewK,Iqs,EIqs)
	)
       ] :-
  EType = bot.
subsume_type((a_ X),(a_ Y),FS,EFS,_,Ss,LRelnIn,RRelnIn,LRelnOut,
             RRelnOut,H,K,Iqs,EIqs) if_b [!,(subsumeschk(X,Y)   % this is all variant/2
                                            -> (subsumeschk(Y,X) % does anyway
                                               -> ((LRelnIn == # 
                                                   -> LRelnOut = #, H = NewH
                                                    ; avl_store(FS,H,EFS,NewH)
                                                   ),
                                                   (RRelnIn == # 
                                                   -> RRelnOut = #, K = NewK
                                                    ; avl_store(EFS,K,FS,NewK)
                                                   ),
                                                   subsume(Ss,LRelnIn,RRelnIn,
                                                           LRelnOut,RRelnOut,NewH,NewK,Iqs,EIqs)
                                                  )
                                               ; RRelnOut = #,
                                                 (LRelnIn == #
                                                 -> LRelnOut = #
                                                  ; avl_store(FS,H,EFS,NewH),
                                                    subsume(Ss,LRelnIn,#,LRelnOut,#,NewH,K,Iqs,EIqs)
                                                 )
                                               )
                                            ; (subsumeschk(Y,X)
                                              -> LRelnOut = #,
                                                 (RRelnIn == #
                                                 -> RRelnOut = #
                                                  ; avl_store(EFS,K,FS,NewK),
                                                    subsume(Ss,#,RRelnIn,#,RRelnOut,H,NewK,Iqs,EIqs)
                                                 )
                                               ; LRelnOut = #, RRelnOut = #
                                              )
                                            )].
subsume_type((a_ _),_,_,_,_,_,_,_,#,#,_,_,_,_) if_b [!].
subsume_type(Type,EType,FS,EFS,Restr,Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,
             H,K,Iqs,EIqs) if_b SubGoals :-
  non_a_type(Type),
  approps(Type,FRs,_),
  ( clause(tmodule(Type,Module),true)
  -> clause(marity(Module,Arity),true),
     functor(FS,Module,Arity)
  ; true  % and so FRs = []
  ),
  subsume_type_act(Type,FRs,EType,FS,EFS,Restr,Ss,LRelnIn,RRelnIn,
                   LRelnOut,RRelnOut,H,K,Iqs,EIqs,SubGoals).

subsume_type_act(Type,FRs,EType,FS,EFS,Restr,Ss,LRelnIn,RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs,
		 [!,
		  ( variant(Restr,Type) -> (LRelnIn == # -> LRelnOut = #, H = NewH
					   ; avl_store(FS,H,EFS,NewH)
					   ),
		                           (RRelnIn == # -> RRelnOut = #, K = NewK
					   ; avl_store(EFS,K,FS,NewK)
					   ),
	                                   subsume(NewSs,LRelnIn,RRelnIn,LRelnOut,RRelnOut,NewH,NewK,
						   Iqs,EIqs)
		  ; % sub_type(Restr,Type),
		    LRelnOut = #,
		    (RRelnIn == # -> RRelnOut = #
		    ; avl_store(EFS,K,FS,NewK),
	              subsume(Ss,#,RRelnIn,#,RRelnOut,H,NewK,Iqs,EIqs)
		    )
                 %; sub_type(Type,Restr) cannot happen - Restr is some feature's introduced value restr.
                 %; LRelnOut = #, RRelnOut = # cannot happen either - all values are subsumed by MGSat(Restr)
		  )]) :-
  EType = 0,
  append_s_lazy_left(FRs,FS,Ss,NewSs).
subsume_type_act(Type,FRs,EType,FS,EFS,_,Ss,LRelnIn,RRelnIn,
                 LRelnOut,RRelnOut,H,K,Iqs,EIqs,[!,(LRelnIn == # 
                                                   -> LRelnOut = #, H = NewH
                                                    ; avl_store(FS,H,EFS,NewH)
                                                   ),
                                                   (RRelnIn == # 
                                                   -> RRelnOut = #, K = NewK
                                                    ; avl_store(EFS,K,FS,NewK)
                                                   ),
                                                   subsume(NewSs,LRelnIn,
                                                           RRelnIn,LRelnOut,RRelnOut,
                                                           NewH,NewK,Iqs,EIqs)]) :-
  Type = EType,
  ( clause(tmodule(EType,EModule),true)
  -> clause(marity(EModule,EArity),true),
     functor(EFS,EModule,EArity)
  ; true
  ),
  append_s(FRs,FS,EFS,Ss,NewSs).
subsume_type_act(Type,FRs,EType,FS,EFS,_,Ss,LRelnIn,_RRelnIn,LRelnOut,RRelnOut,H,K,Iqs,EIqs,
                 [!,RRelnOut = #,
                  (LRelnIn == #
                  -> LRelnOut = #
                   ; avl_store(FS,H,EFS,NewH),
                     subsume(NewSs,LRelnIn,#,LRelnOut,#,NewH,K,Iqs,EIqs)
                  )]) :-
  sub_type(Type,EType), EType \== Type,
  ( clause(tmodule(EType,EModule),true)
  -> clause(marity(EModule,EArity),true),
     functor(EFS,EModule,EArity)
  ; true
  ),
  append_s(FRs,FS,EFS,Ss,NewSs).
subsume_type_act(Type,_,EType,FS,EFS,_,Ss,_LRelnIn,RRelnIn,
                 LRelnOut,RRelnOut,H,K,Iqs,EIqs,[!,LRelnOut = #,
                                                   (RRelnIn == #
                                                   -> RRelnOut = #
                                                    ; avl_store(EFS,K,FS,NewK),
                                                      subsume(NewSs,#,RRelnIn,
                                                              #,RRelnOut,H,NewK,Iqs,EIqs)
                                                   )]) :-
  sub_type(EType,Type), EType \== Type, % EType \== 0 because 0 is not indexed in sub_type/2
  approps(EType,EFRs,_),
  ( clause(tmodule(EType,EModule),true)
  -> clause(marity(EModule,EArity),true),
     functor(EFS,EModule,EArity)
  ; true
  ),
  append_s(EFRs,FS,EFS,Ss,NewSs).
subsume_type_act(_,_,_,_,_,_,_,_,_,#,#,_,_,_,_,[]).
                 % still need 1 arg to multi-hash

subsume_iqs([],Reln,Reln,_).
subsume_iqs([Iq|Iqs],RelnIn,RelnOut,H) :-
  RelnIn == # -> RelnOut = #
   ; subsume_iq(Iq,RelnIn,RelnMid,H), % make sure image of each conjunct 
     subsume_iqs(Iqs,RelnMid,RelnOut,H). % holds in image FS

subsume_iq(ineq(FS1,FS2),RelnIn,RelnOut,H) :-
  (avl_fetch(FS1,H,EFS1) -> Test1 = EFS1 ; Test1 = FS1), % test which inequated FSs have an image
  (avl_fetch(FS2,H,EFS2) -> Test2 = EFS2 ; Test2 = FS2), % if no image, use the inequated FS itself
  ( \+ \+ (Test1 = Test2) -> RelnOut = #  % negated image of conjunct is
                                          % satisfied by image FS, so no subsumption morphism exists.
  % KNOWN BUG - this test may produce side effects
  ; RelnOut = RelnIn  % image of conjunct is 
                      % implicitly encoded in the image FS (since 
                      % unifying the images of the inequated FSs failed).
  ).

% ------------------------------------------------------------------------------
% append_s(FRs,FS,EFS,Ss,NewSs)
% ------------------------------------------------------------------------------
% NewSs is Ss plus in-order pairs of common feature values from FS and EFS
%  in s-structures.
% ------------------------------------------------------------------------------
append_s([],_,_,Ss,Ss).
append_s([F:_|FRs],FS,EFS,Ss,s(V,EV,Restr,NewSs)) :-
  clause(introduce(F,FIntro),true),
  approp(F,FIntro,Restr),
  clause(fcolour(F,K,_),true),
  arg(K,FS,V), arg(K,EFS,EV),
  append_s(FRs,FS,EFS,Ss,NewSs).

append_s_lazy_left([],_,Ss,Ss).
append_s_lazy_left([F:_|FRs],FS,Ss,s(V,_,IntroR,NewSs)) :-
  clause(introduce(F,FIntro),true),
  approp(F,FIntro,IntroR),
  clause(fcolour(F,K,_),true),
  arg(K,FS,V),
  append_s_lazy_left(FRs,FS,Ss,NewSs).

append_s_lazy_right([],_,Ss,Ss).
append_s_lazy_right([F:_|FRs],EFS,Ss,s(_,EV,IntroR,NewSs)) :-
  clause(introduce(F,FIntro),true),
  approp(F,FIntro,IntroR),
  clause(fcolour(F,K,_),true),
  arg(K,EFS,EV),
  append_s_lazy_right(FRs,EFS,Ss,NewSs).

append_keyed_lists([],[]).
append_keyed_lists([_-List|KLs],Flat) :-
  append(List,Rest,Flat),
  append_keyed_lists(KLs,Rest).

% edge_discard(LReln:<var>/#,I:<int>,FS:<tfs>,Iqs:<ineq>s,
%              Dtrs:<int>s,RuleName,Left:<int>,Right:<int>)
% ------------------------------------------------------------------------------
% Discard edge FS, with inequations Iqs, daughters Dtrs, created by rule
%  RuleName, because it is subsumed by the edge with index I.  If LReln is a
%  variable, then the two are equal - otherwise, LReln is #, which indicates
%  strict subsumption.
% ------------------------------------------------------------------------------
edge_discard(_,_,_,_,_,_,_) :-
  ale_flag(interp,off),
  !.
edge_discard(LReln,I,FS,Dtrs,RuleName,Left,Right) :-
  length(Dtrs,ND),
  !, (ale_flag(residue,show) -> frozen_term(FS,Frozen) ; Frozen = []),
  print_edge_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Frozen).

print_edge_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
 ((current_predicate(portray_edge_discard,portray_edge_discard(_,_,_,_,_,_,_,_)),
   portray_edge_discard(LReln,I,Left,Right,FS,RuleName,ND,Res)) -> true
 ; nl,pp_fs_res(FS,Res),
   nl,write('Edge created for category above:'),
%  nl,write('     index: '),write(I),
   nl,write('      from: '),write(Left),write(' to: '),write(Right),
   nl,write('    string: '),write_parsing_substring(Left,Right),
   nl,write('      rule: '),write(RuleName),
   nl,write(' # of dtrs: '),write(ND),nl,
   print_edge_discard_act(LReln,I),nl
 ),
 query_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res).

print_edge_discard_act(<,I) :-
  !,nl,write('is equal to an existing edge, index:'),write(I),write('.').
print_edge_discard_act(#,I) :-
  nl,write('is subsumed by an existing edge, index:'),write(I),write('.').

query_discard(_,_,_,_,_,_,_,_,_) :-
  go(_),
  !.
query_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  nl,write('Action(noadd,continue,break,dtr-#,existing,abort)? '),
  nl,read(Response),
  query_discard_act(Response,LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res).

query_discard_act(noadd,_,_,_,_,_,_,_,_,_) :- !.
query_discard_act(continue,_,_,_,_,_,_,_,_,_) :- 
  !,fail.
query_discard_act(break,LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  !,break,
  print_edge_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res).
query_discard_act(dtr-D,LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  nth_index(Dtrs,D,DI,DLeft,DRight,DFS,DDtrs,DRule,DResidue),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DResidue),
  print_edge_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res).
query_discard_act(existing,LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  call_with_residue(clause(edge(I,Left,Right,EFS,ERes,EDtrs,ERuleName),true),ERes,CallResidue),
  !, ( print_asserted_edge_act(I,Left,Right,EFS,EDtrs,ERuleName,CallResidue)
     ; print_edge_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res)
     ).
query_discard_act(abort,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_discard_act(_,LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  query_discard(LReln,I,Left,Right,FS,Dtrs,RuleName,ND,Res).

% edge_retract(Left:<int>,I:<int>,FS:<tfs>,Iqs:<ineq>s,Dtrs:<int>s,
%              RuleName:<atom>)
% ------------------------------------------------------------------------------
% Retract edge with index I because it is subsumed by Tag-SVs, with inequations
%  Iqs, daughters Dtrs, created by rule RuleName
% ------------------------------------------------------------------------------
edge_retract(Left,I,_,_,_) :-
  ale_flag(interp,off),
  retract(to_rebuild(I)),
  retract(edge(I,Left,_,_,_,_,_)),
  !,fail.     % failure-drive through all subsumed edges

edge_retract(Left,I,FS,Dtrs,RuleName) :-
  !,call_with_residue(clause(edge(I,Left,Right,EFS,ERes,EDtrs,ERuleName),true),ERes,CallResidue),
  length(EDtrs,NED),
  print_edge_retract(I,Left,Right,EFS,EDtrs,ERuleName,NED,CallResidue,FS,Dtrs,RuleName).

print_edge_retract(I,Left,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName) :-
 ((current_predicate(portray_edge_retract,portray_edge_retract(_,_,_,_,_,_,_)),
   portray_edge_retract(I,Left,Right,EFS,ERuleName,NED,ERes)) -> true
 ; nl,pp_fs_res(EFS,ERes),
   nl,write('Edge created for category above:'),
   nl,write('     index: '),write(I),
   nl,write('      from: '),write(Left),write(' to: '),write(Right),
   nl,write('    string: '),write_parsing_substring(Left,Right),
   nl,write('      rule: '),write(ERuleName),
   nl,write(' # of dtrs: '),write(NED),nl,
   nl,write('is subsumed by an incoming edge.'),nl
 ),
 query_retract(Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName).

query_retract(Left,I,_,_,_,_,_,_,_,_,_) :-
  go(_),
  retract(edge(I,Left,_,_,_,_,_,_)),
  retract(to_rebuild(I)),
  !,fail.
query_retract(Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName) :-
  nl,write('Action(retract,continue,break,dtr-#,incoming,abort)? '),
  nl,read(Response),
  query_retract_act(Response,Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName).
query_retract_act(retract,Left,I,_,_,_,_,_,_,_,_,_) :-
  retract(edge(I,Left,_,_,_,_,_)),
  retract(to_rebuild(I)),
  !,fail.
query_retract_act(remain,_,_,_,_,_,_,_,_,_,_,_) :-
  !,fail.
query_retract_act(continue,_,_,_,_,_,_,_,_,_,_,_) :-
  !.
query_retract_act(break,Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName) :-
  !,break,
  print_edge_retract(I,Left,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName).
query_retract_act(dtr-D,Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName) :-
  nth_index(EDtrs,D,DI,DLeft,DRight,DFS,DDtrs,DRule,DResidue),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DResidue),
  print_edge_retract(I,Left,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName).
query_retract_act(incoming,Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName) :-
  !,length(Dtrs,ND),
  (ale_flag(residue,show) -> frozen_term(FS,Frozen) ; Frozen = []),
  ( print_incoming_edge(Left,Right,FS,Dtrs,RuleName,ND,Frozen)
   -> true
    ; print_edge_retract(I,Left,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName)).
query_retract_act(abort,_,_,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_retract_act(_,Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName) :-
  query_retract(Left,I,Right,EFS,EDtrs,ERuleName,NED,ERes,FS,Dtrs,RuleName).

print_incoming_edge(Left,Right,FS,Dtrs,RuleName,ND,Res) :-
 ((current_predicate(portray_incoming_edge,portray_incoming_edge(_,_,_,_,_,_)),
   portray_incoming_edge(Left,Right,FS,RuleName,ND,Res)) -> true
 ; nl,pp_fs_res(FS,Res),
   nl,write('Incoming Edge: '),
   nl,write('      from: '),write(Left),write(' to: '),write(Right),
   nl,write('    string: '),write_parsing_substring(Left,Right),
   nl,write('      rule:  '),write(RuleName),
   nl,write(' # of dtrs: '),write(ND),nl
 ),
 query_incoming_edge(Left,Right,FS,Dtrs,RuleName,ND,Res).

query_incoming_edge(Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  nl,write('Action(noadd,dtr-#,existing,abort)?' ),
  nl,read(Response),
  query_incoming_act(Response,Left,Right,FS,Dtrs,RuleName,ND,Res).
query_incoming_act(noadd,_,_,_,_,_,_,_) :-
  !.
query_incoming_act(existing,_,_,_,_,_,_,_) :-
  !,fail.
query_incoming_act(abort,_,_,_,_,_,_,_) :-
  !,abort.
query_incoming_act(dtr-D,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  nth_index(Dtrs,D,DI,DLeft,DRight,DFS,DDtrs,DRule,DResidue),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DResidue),
  print_incoming_edge(Left,Right,FS,Dtrs,RuleName,ND,Res).
query_incoming_act(_,Left,Right,FS,Dtrs,RuleName,ND,Res) :-
  query_incoming_edge(Left,Right,FS,Dtrs,RuleName,ND,Res).

% ==============================================================================
% Interpreter
% ==============================================================================
:- dynamic go/1.

edge_assert(Left,Right,FSOut,Dtrs,RuleName,N) :- 
  ale_flag(interp,off),                                      
  !,gen_edgenum(N),
  asserta(to_rebuild(N)),
  residuate_term(FSOut,ResidueOut),
  asserta(edge(N,Left,Right,FSOut,ResidueOut,Dtrs,RuleName)),
  ( current_predicate(edge_assert_hook,edge_assert_hook(_,_,_,_,_,_,_))  % SP4: pass residue to hook
  -> call_all(edge_assert_hook(N,Left,Right,FSOut,ResidueOut,Dtrs,RuleName))
  ; true
  ).
%  format('Edge added: Number: ~w, Left: ~w, Right: ~w, Rule: ~w~n',
%         [N,Left,Right,RuleName]), % DEBUG
%  ttyflush. % DEBUG

edge_assert(Left,Right,FSOut,Dtrs,RuleName,N) :-
  !,nl,
  length(Dtrs,ND),
  (ale_flag(residue,show) -> frozen_term(FSOut,Frozen) ; Frozen = []),
  ( print_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Frozen)
  -> gen_edgenum(N),
     asserta(to_rebuild(N)),
     residuate_term(FSOut,ResidueOut),
     asserta(edge(N,Left,Right,FSOut,ResidueOut,Dtrs,RuleName)),
     ( current_predicate(edge_assert_hook,edge_assert_hook(_,_,_,_,_,_,_))
     -> call_all(edge_assert_hook(N,Left,Right,FSOut,ResidueOut,Dtrs,RuleName))
     ; true
     )
  ).

print_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res) :-
 ((current_predicate(portray_edge,portray_edge(_,_,_,_,_,_,_)),
   portray_edge(pending,Left,Right,FSOut,RuleName,ND,Res)) -> true
 ; nl,pp_fs_res(FSOut,Res),
   nl,write('Edge created for category above: '),
   nl,write('      from: '),write(Left),write(' to: '),write(Right),
   nl,write('    string: '),write_parsing_substring(Left,Right),
   nl,write('      rule:  '),write(RuleName),
   nl,write(' # of dtrs: '),write(ND),nl
 ),
 query_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res).

query_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res) :-
  go(Left),               % right-to-left parser triggers on left
  !,retractall(go(_)),
  query_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res).
query_edge(_,_,_,_,_,_,_) :-
  go(_),
  !.
query_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res) :-
  nl,write('Action(add,noadd,go(-#),break,dtr-#,abort)? '),
  nl,read(Response),
  query_edge_act(Response,Left,Right,FSOut,Dtrs,RuleName,ND,Res).

query_edge_act(add,_,_,_,_,_,_,_) :-
  !.
query_edge_act(noadd,_,_,_,_,_,_,_) :- 
  !,fail.
query_edge_act(go,_,_,_,_,_,_,_) :-
  !,asserta(go(go)).
query_edge_act(go-G,_,_,_,_,_,_,_) :-
  !,asserta(go(G)).
query_edge_act(break,Left,Right,FSOut,Dtrs,RuleName,ND,Res) :-
  !,break,
  print_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res).
query_edge_act(dtr-D,Left,Right,FSOut,Dtrs,RuleName,ND,Res):-
  nth_index(Dtrs,D,DI,DLeft,DRight,DFS,DDtrs,DRule,DResidue),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DResidue),
  print_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res).
query_edge_act(abort,_,_,_,_,_,_,_) :-
  !,abort.
query_edge_act(_,Left,Right,FSOut,Dtrs,RuleName,ND,Res) :-
  query_edge(Left,Right,FSOut,Dtrs,RuleName,ND,Res).

print_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DRes) :-
 ((current_predicate(portray_dtr_edge,portray_dtr_edge(_,_,_,_,_,_,_)),
   portray_dtr_edge(D,DLeft,DRight,DFS,DRule,DND,DRes)) -> true
 ; nl,pp_fs_res(DFS,DRes),
   nl,write('Daughter number '), write(D),
   nl,write('      from: '),write(DLeft),write(' to: '),write(DRight),
   nl,write('    string: '),write_parsing_substring(DLeft,DRight),
   nl,write('      rule:  '),write(DRule),
   nl,write(' # of dtrs: '),write(DND),nl
 ),
 query_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DRes).

query_dtr_edge(D,I,DLeft,DRight,DFS,DDtrs,DRule,DND,DRes) :-
  nl,write('Action(retract,dtr-#,parent,abort)?' ),
  nl,read(Response),
  query_dtr_act(Response,D,I,DLeft,DRight,DFS,DDtrs,DRule,DND,DRes).
query_dtr_act(parent,_,_,_,_,_,_,_,_,_) :-
  !.
query_dtr_act(retract,_,I,DLeft,_,_,_,_,_,_) :-
  retract(edge(I,DLeft,_,_,_,_,_)),  % will fail on empty cats
  !.
query_dtr_act(abort,_,_,_,_,_,_,_,_,_) :-
  !,abort.
query_dtr_act(dtr-DD,D,I,Left,Right,FS,Dtrs,Rule,ND,Res) :-
  nth_index(Dtrs,DD,DI,DLeft,DRight,DFS,DDtrs,DRule,DRes),
  !,length(DDtrs,DND),
  print_dtr_edge(DD,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DRes),
  print_dtr_edge(D,I,Left,Right,FS,Dtrs,Rule,ND,Res).
query_dtr_act(_,D,I,Left,Right,FS,Dtrs,Rule,ND,Res) :-
  query_dtr_edge(D,I,Left,Right,FS,Dtrs,Rule,ND,Res).

nth_index([I|Is],N,DI,DLeft,DRight,DFS,DDtrs,DRule,Residue) :- 
  N =:= 1
  -> DI = I,
     (I = empty(E,DLeft)
     -> call_residue(empty_cat(E,DLeft,DFS,DDtrs,DRule),DFS,Residue),
        % empty_cat could in principle pass the residue to us
        DLeft = DRight
      ; (call_with_residue(clause(edge(I,DLeft,DRight,DFS,DRes,DDtrs,DRule),true),DRes,Residue)
        -> true
         ; error_msg((nl,write('edge has been retracted')))
        )
     )
   ; NMinus1 is N-1,
     nth_index(Is,NMinus1,DI,DLeft,DRight,DFS,DDtrs,DRule,Residue).


% ==============================================================================
% Definite Clause Resolution/Compilation
% ==============================================================================

% ------------------------------------------------------------------------------
% compile_body(GoalDesc,IqsIn,IqsOut,PGoals,PGoalsRest,CBSafe,VarsIn,VarsOut,
%              FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% compiles arbitrary Goal.
% PGoals is instantiated to list of Prolog goals required to add
% arguments relations in Goal and then call the procedure to solve them.
% IqsIn and IqsOut are uninstantiated at compile time.  
% ------------------------------------------------------------------------------
% 4/1/96 - Octav -- changed compile_body/7 to take an extra argument that's
% used for computing the Goals list as difference list
compile_body(((GD1,GD2),GD3),PGoals,PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !, compile_body((GD1,(GD2,GD3)),PGoals,PGoalsRest,Context,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs).
compile_body(((IfD -> ThenD ; ElseD),PGD),PGoals,PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !,prior_cont_vars(IfD,IfVars),
    prior_cont_vars(ThenD,ThenVars),
    prior_cont_vars(PGD,PGDVars),
    ord_union(PGDVars,ContVs,ThenElseContVs),
    ord_union(ThenVars,ThenElseContVs,IfContVs),
    ord_union(IfVars,PriorVs,ThenPriorVs),
    (compile_body(IfD,IfGoals,[],disj,VarsIn,VarsIf,FSPal,FSsIn,FSsIf,MFSIn,MFSIf,NVs,PriorVs,IfContVs)
    -> IfCompiled = true,
       ( compile_body(ThenD,ThenGoals,[],disj,VarsIf,VarsThen,FSPal,FSsIf,FSsThen,MFSIf,MFSThen,NVs,
                      ThenPriorVs,ThenElseContVs)
       -> ThenCompiled = true,
	  ( compile_body(ElseD,ElseGoals,[],disj,VarsIn,VarsElse,FSPal,FSsIn,FSsElse,MFSIn,MFSElse,NVs,
                         PriorVs,ThenElseContVs)
	  -> ElseCompiled = true,
	     mfs_merge(MFSIn,MFSThen,MFSElse,Context,MFSMid),
             vars_merge(VarsIn,VarsThen,VarsElse,Context,VarsMid,MFSMid,MFSMid2),
             fss_merge(FSsIn,FSsThen,FSsElse,FSsMid,MFSMid2,MFSMid3),
             goal_list_to_seq(IfGoals,IfG),
             goal_list_to_seq(ThenGoals,ThenG),
             goal_list_to_seq(ElseGoals,ElseG),
             PGoals = [(IfG -> ThenG ; ElseG)|PGoalsMid],
             prior_cont_vars(ElseD,ElseVars),
             ord_union(ThenVars,ElseVars,ThenElseVars),
             ord_union(ThenElseVars,ThenPriorVs,PGPriorVs),
	     compile_body_catch_fail(PGD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,
			             FSPal,FSsMid,FSsOut,MFSMid3,MFSOut,NVs,PGPriorVs,ContVs)
	  ; ElseCompiled = false,
	    compile_body(((IfD -> ThenD), PGD),PGoals,PGoalsRest,Context,VarsIn,
			 VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs)
	  )
       ; ThenCompiled = false,
         compile_body((\+ IfD, ElseD, PGD),PGoals,PGoalsRest,Context,VarsIn,
		      VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs),
	 % need to recompile with the appropriate contexts (not disj)
         ElseCompiled = true % or else this goal will never succeed
       )
    ; IfCompiled = false,
      compile_body((ElseD, PGD),PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,
		   MFSIn,MFSOut,NVs,PriorVs,ContVs),
      ThenCompiled = true, % well, not that we tried, but no warning is warranted
      ElseCompiled = true
    ),
    ( IfCompiled == false
    -> print_message(warning,ale(shallow_cut_failure_if((IfD -> ThenD ; ElseD))))
    ; true),
    ( ThenCompiled == false
    -> print_message(warning,ale(shallow_cut_failure_then((IfD -> ThenD ; ElseD))))
    ; true),
    ( ElseCompiled == false
    -> print_message(warning,ale(shallow_cut_failure_else((IfD -> ThenD ; ElseD))))
    ; true).
compile_body(((GD1;GD2),GD3),PGoals,PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !, compile_body(((GD1,GD3);(GD2,GD3)),PGoals,PGoalsRest,Context,
                  VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs).
compile_body((\+ GD1, GD2),PGoals,PGoalsRest,
             Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !, ( compile_body(GD1,PGoalsList,[],when_or_neg,VarsIn,_,FSPal,FSsIn,_,MFSIn,_,NVs,PriorVs,[]) % no continuant
     -> PGoals = [(\+ PGoal)|PGoalsMid],
	goal_list_to_seq(PGoalsList,PGoal),
	compile_body_catch_fail(GD2,PGoalsMid,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
				FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs)
     ; print_message(warning,ale(neg_arg_failure(\+ GD1))),
       compile_body(GD2,PGoals,PGoalsRest,
		    Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs)
     ).
compile_body((Desc1 =@ Desc2,GD),PGoals,PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
   !, empty_avl(EAssoc),
   initialise_rel_mode(2,ArgPaths,EAssoc,ModeIn,MFSIn,MFSMid),
   compile_descs_fresh([Desc1,Desc2],[FS1,FS2],ArgPaths,PGoals,
			  [(FS1 == FS2)|PGoalsMid],Context,VarsIn,VarsMid,
			  FSPal,FSsIn,FSsMid,ModeIn,_ModeOut,MFSMid,MFSMid2,NVs),
%  verify_input_modes(2,'=@',ArgPaths,ModeOut), --- '=@' has bot input mode in both args
%  assert_output_modes(2,'=@',ArgPaths,ModeOut,_), --- '=@' has bot output mode in both args
   term_variables([Desc1|Desc2],EqVars),
   ord_union(EqVars,PriorVs,GPriorVs),
   compile_body_catch_fail(GD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,FSPal,FSsMid,FSsOut,MFSMid2,
                           MFSOut,NVs,GPriorVs,ContVs).
compile_body((Desc1 = Desc2,GD),PGoals,PGoalsRest,Context,VarsIn,VarsOut,
	     FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !, empty_avl(EAssoc),                   % this is a special case: must compile
  initialise_rel_mode(1,[N],EAssoc,ModeIn,MFSIn,MFSMid), %  equality on single argument
  compile_desc_act((Desc1,Desc2),EAssoc,_IVars,PGoals,PGoalsMid,N,Context,VarsIn,VarsMid,FSPal,
		   FSsIn,FSsMid,ModeIn,_ModeOut,MFSMid,MFSMid2,NVs),
  term_variables([Desc1|Desc2],EqVars),
  ord_union(EqVars,PriorVs,GPriorVs),
  compile_body_catch_fail(GD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,FSPal,FSsMid,
			  FSsOut,MFSMid2,MFSOut,NVs,GPriorVs,ContVs).
compile_body((true,GD),PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !, compile_body(GD,PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
                  FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs).
compile_body((fail,_),[fail|PGoalsRest],PGoalsRest,_,Vars,Vars,_,FSs,FSs,MFS,MFS,_,_,_):-
  !.
compile_body((!,PGD),[!|PGoalsMid],PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !, compile_body(PGD,PGoalsMid,PGoalsRest,Context,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs).
compile_body(((IfD -> ThenD),PGD),[(IfG -> ThenG)|PGoalsMid],PGoalsRest,Context,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !,prior_cont_vars(IfD,IfVars),
    prior_cont_vars(ThenD,ThenVars),
    prior_cont_vars(PGD,PGVars),
    ord_union(PGVars,ContVs,ThenContVs),
    ord_union(ThenVars,ThenContVs,IfContVs),
    ord_union(IfVars,PriorVs,ThenPriorVs),
    ord_union(ThenVars,ThenPriorVs,PGPriorVs),
    compile_body(IfD,IfGoals,[],Context,VarsIn,VarsIf,FSPal,FSsIn,FSsIf,MFSIn,MFSIf,NVs,PriorVs,IfContVs),
    compile_body_catch_fail(ThenD,ThenGoals,[],Context,VarsIf,VarsMid,FSPal,FSsIf,FSsMid,MFSIf,MFSMid,NVs,
                            ThenPriorVs,ThenContVs),
    goal_list_to_seq(IfGoals,IfG),
    goal_list_to_seq(ThenGoals,ThenG),
    compile_body_catch_fail(PGD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,FSPal,FSsMid,FSsOut,MFSMid,
			    MFSOut,NVs,PGPriorVs,ContVs).
compile_body((prolog(Goal),GD),PGoals,PGoalsRest,Context,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !, desc_varfs_body(GD,DVars,DFSs,NVs), % should record FSs created by EFD closure
  term_variables(Goal,HookVars),
  ord_union(HookVars,PriorVs,GPriorVs),
  map_vars(HookVars,HookNVars,NVs),
  ord_intersection(DVars,HookNVars,HookDVars),
  tricky_vars_merge(HookDVars,VarsIn,VarsMid,MFSIn,MFSMid),
  replace_hook_fss(Goal,DFSs,PGoal,PGoals,[PGoal|PGoalsMid],FSPal,FSsIn,FSsMid,MFSMid,MFSMid2),
  compile_body_catch_fail(GD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,FSPal,
			  FSsMid,FSsOut,MFSMid2,MFSOut,NVs,GPriorVs,ContVs).
compile_body((prolog(NVs,Goal),GD),PGoals,PGoalsRest,Context,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !, desc_varfs_body(GD,DVars,DFSs,NVs), % should record FSs created by EFD closure
  term_variables(Goal,HookVars),
  ord_union(HookVars,PriorVs,GPriorVs),
  map_vars(HookVars,HookNVars,NVs),
  ord_intersection(DVars,HookNVars,HookDVars),
  tricky_vars_merge(HookDVars,VarsIn,VarsMid,MFSIn,MFSMid),
  replace_hook_fss(Goal,DFSs,PGoal,PGoals,[PGoal|PGoalsMid],FSPal,FSsIn,FSsMid,MFSMid,MFSMid2),
  compile_body_catch_fail(GD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,FSPal,
			  FSsMid,FSsOut,MFSMid2,MFSOut,NVs,GPriorVs,ContVs).
compile_body((when(Cond,WBody),GD),PGoals,PGoalsRest,Context,VarsIn,VarsOut,
	     FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !,desc_varfs_body(when(Cond,WBody),WhenALEVars,WhenFSs,NVs),
  desc_varfs_body(GD,GALEVars,ContFSs,NVs),
  ord_intersection(WhenALEVars,GALEVars,DVars),
  ord_intersection(WhenFSs,ContFSs,DFSs),
  tricky_vars_merge(DVars,VarsIn,VarsTricky,MFSIn,MFSVarTricky),
  tricky_fss_merge(DFSs,FSsIn,FSsTricky,MFSVarTricky,MFSTricky),  % every FS is tricky - could 
           % discriminate between unseen and tricky much better here (possibly by binding all
           % when/2 FSs to palette args just before suspension)
  prior_cont_vars(GD,GVars), % this is GALEVars plus Prolog vars that might occur in GD prolog hooks
  ord_union(GVars,ContVs,WhenContVs),
  prior_cont_vars(when(Cond,WBody),WhenVars),
  ord_union(WhenVars,PriorVs,GPriorVs),
  ( compile_cond(Cond,WBody,PGoals,PGoalsMid,VarsTricky,FSPal,FSsTricky,MFSTricky,NVs,PriorVs,WhenContVs)
  -> VarsTricky = VarsMid, MFSMid = MFSTricky, FSsMid = FSsTricky
  ; print_message(warning,ale(cond_failure(Cond,WBody))), PGoals = PGoalsMid,
    VarsMid = VarsIn, MFSMid = MFSIn, FSsMid = FSsIn
  ),
  compile_body_catch_fail(GD,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,FSPal,
			  FSsMid,FSsOut,MFSMid,MFSOut,NVs,GPriorVs,ContVs).
compile_body((AGD,GD2),PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !,AGD =.. [Rel|ArgDescs],
  functor(AGD,_,RelArity),
  empty_avl(EAssoc),
  initialise_rel_mode(RelArity,ArgPaths,EAssoc,ModeIn,MFSIn,MFSMid),
  compile_descs_fresh(ArgDescs,Args,ArgPaths,PGoals,[AGoal|PGoalsMid],
                      Context,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeIn,ModeMid,MFSMid,MFSMid2,NVs),
  verify_input_modes(RelArity,Rel,ArgPaths,ModeMid,MFSMid2),
  assert_output_modes(RelArity,Rel,ArgPaths,ModeMid,_,MFSMid2,MFSMid3),
  cat_atoms('fs_',Rel,CompiledRel),
  AGoal =.. [CompiledRel|Args],
  term_variables(AGD,AGVars),
  ord_union(AGVars,PriorVs,G2PriorVs),
  compile_body_catch_fail(GD2,PGoalsMid,PGoalsRest,Context,VarsMid,VarsOut,
			  FSPal,FSsMid,FSsOut,MFSMid3,MFSOut,NVs,G2PriorVs,ContVs).
compile_body((IfD -> ThenD ; ElseD),PGoals,
	     PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !,prior_cont_vars(IfD,IfVars),
    prior_cont_vars(ThenD,ThenVars),
    ord_union(IfVars,PriorVs,ThenPriorVs),
    ord_union(ThenVars,ContVs,IfContVs),
    (compile_body(IfD,IfGoals,[],disj,VarsIn,VarsIf,FSPal,FSsIn,FSsIf,MFSIn,MFSIf,NVs,PriorVs,IfContVs)
    -> IfCompiled = true,
       ( compile_body(ThenD,ThenGoals,[],disj,VarsIf,VarsThen,FSPal,FSsIf,FSsThen,MFSIf,MFSThen,NVs,
                      ThenPriorVs,ContVs)
       -> ThenCompiled = true,
	  ( compile_body(ElseD,ElseGoals,[],disj,VarsIn,VarsElse,FSPal,FSsIn,FSsElse,MFSIn,MFSElse,NVs,
                         PriorVs,ContVs)
	  -> ElseCompiled = true,
	     mfs_merge(MFSIn,MFSThen,MFSElse,Context,MFSMid),
             vars_merge(VarsIn,VarsThen,VarsElse,Context,VarsOut,MFSMid,MFSMid2),
             fss_merge(FSsIn,FSsThen,FSsElse,FSsOut,MFSMid2,MFSOut),
             goal_list_to_seq(IfGoals,IfG),
             goal_list_to_seq(ThenGoals,ThenG),
             goal_list_to_seq(ElseGoals,ElseG),
             PGoals = [(IfG -> ThenG ; ElseG)|PGoalsRest]
	  ; ElseCompiled = false,
	    compile_body((IfD -> ThenD),PGoals,PGoalsRest,Context,VarsIn,
			 VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs)  
	  )
       ; ThenCompiled = false,
	 compile_body((\+ IfD, ElseD),PGoals,PGoalsRest,Context,VarsIn,
		      VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs),
	 % need to recompile with the appropriate contexts (not disj)
	 ElseCompiled = true  % or else this goal will never succeed
       )
    ; IfCompiled = false,
      compile_body(ElseD,PGoals,PGoalsRest,Context,VarsIn,
	 	   VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs),
      ThenCompiled = true, % well, not that we tried, but no warning is warranted
      ElseCompiled = true
    ),
    ( IfCompiled == false
    -> print_message(warning,ale(shallow_cut_failure_if((IfD -> ThenD ; ElseD))))
    ; true
    ),
    ( ThenCompiled == false
    -> print_message(warning,ale(shallow_cut_failure_then((IfD -> ThenD ; ElseD))))
    ; true
    ),
    ( ElseCompiled == false
    -> print_message(warning,ale(shallow_cut_failure_else((IfD -> ThenD ; ElseD))))
    ; true
    ).
compile_body((GD1;GD2),PGoals,PGoalsRest,Context,
             VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs):-
  !, ( compile_body(GD1,PGoals1,[],disj,VarsIn,VarsDisj1,FSPal,FSsIn,FSsDisj1,MFSIn,MFSDisj1,NVs,
                    PriorVs,ContVs)
     -> Disj1Compiled = true
     ; print_message(warning,ale(disj1_failure((GD1;GD2)))),
       Disj1Compiled = false
     ),
     ( compile_body(GD2,PGoals2,[],disj,VarsIn,VarsDisj2,FSPal,FSsIn,FSsDisj2,MFSIn,MFSDisj2,NVs,
                    PriorVs,ContVs)
     -> Disj2Compiled = true
     ; print_message(warning,ale(disj2_failure((GD1;GD2)))),
       Disj2Compiled = false
     ),
     ( Disj1Compiled == true
     -> ( Disj2Compiled == true
	-> goal_list_to_seq(PGoals1,PGoal1),
	   goal_list_to_seq(PGoals2,PGoal2),
	   PGoals = [(PGoal1;PGoal2)|PGoalsRest],
	   mfs_merge(MFSIn,MFSDisj1,MFSDisj2,Context,MFSMid),
	   vars_merge(VarsIn,VarsDisj1,VarsDisj2,Context,VarsOut,MFSMid,MFSMid2),
	   fss_merge(FSsIn,FSsDisj1,FSsDisj2,FSsOut,MFSMid2,MFSOut)
	; compile_body(GD1,PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,
                       PriorVs,ContVs)
	)
     ; Disj2Compiled == true,
       compile_body(GD2,PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,
                    PriorVs,ContVs)
     ).
compile_body((\+ GD),PGoals,PGoalsRest,_Context,
             VarsIn,VarsIn,FSPal,FSs,FSs,MFSIn,MFSIn,NVs,PriorVs,_) :- % vars will be unbound, so dont thread
  !, ( compile_body(GD,PGoalsList,[],when_or_neg,VarsIn,_,FSPal,FSs,_,MFSIn,_,NVs,PriorVs,[]) % no continuant either
     -> PGoals = [(\+ PGoal)|PGoalsRest],
        goal_list_to_seq(PGoalsList,PGoal)
     ; print_message(warning,ale(neg_arg_failure(\+ GD))),
       PGoals = PGoalsRest
     ).
compile_body((Desc1 =@ Desc2),PGoals,PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,_,_):-
  !, empty_avl(EAssoc),
  initialise_rel_mode(2,ArgPaths,EAssoc,ModeIn,MFSIn,MFSMid),
  compile_descs_fresh([Desc1,Desc2],[FS1,FS2],ArgPaths,PGoals,
               [(FS1 == FS2)|PGoalsRest],
               Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,ModeIn,_ModeOut,MFSMid,MFSOut,NVs).
%  verify_input_modes(2,'=@',ArgPaths,ModeOut), --- '=@' has bot input mode in both args
%  assert_output_modes(2,'=@',ArgPaths,ModeOut,_). --- '=@' has bot output mode in both args
compile_body((Desc1 = Desc2),PGoals,PGoalsRest,Context,VarsIn,VarsOut,
	     FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,_,_) :-
  !, empty_avl(EAssoc),
  initialise_rel_mode(1,[N],EAssoc,ModeIn,MFSIn,MFSMid),
  compile_desc_act((Desc1,Desc2),EAssoc,_IVars,PGoals,PGoalsRest,N,Context,VarsIn,VarsOut,FSPal,
		   FSsIn,FSsOut,ModeIn,_ModeOut,MFSMid,MFSOut,NVs).
compile_body(true,PGoals,PGoals,_,Vars,Vars,_,FSs,FSs,MFS,MFS,_,_,_):-
  !.
compile_body(fail,[fail|PGoalsRest],PGoalsRest,_,Vars,Vars,_,FSs,FSs,MFS,MFS,_,_,_):-
  !.
compile_body(!,[!|PGoalsRest],PGoalsRest,_,Vars,Vars,_,FSs,FSs,MFS,MFS,_,_,_):-
  !.
compile_body((IfD -> ThenD),[(IfG -> ThenG)|PGoalsRest],PGoalsRest,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !,prior_cont_vars(IfD,IfVars),
    prior_cont_vars(ThenD,ThenVars),
    ord_union(IfVars,PriorVs,ThenPriorVs),
    ord_union(ThenVars,ContVs,IfContVs),
    compile_body(IfD,IfGoals,[],Context,VarsIn,VarsIf,FSPal,FSsIn,FSsIf,MFSIn,MFSIf,NVs,PriorVs,IfContVs),
    compile_body(ThenD,ThenGoals,[],Context,VarsIf,VarsOut,FSPal,FSsIf,FSsOut,MFSIf,MFSOut,NVs,
                 ThenPriorVs,ContVs),
    goal_list_to_seq(IfGoals,IfG),
    goal_list_to_seq(ThenGoals,ThenG).
compile_body(prolog(Goal),PGoals,PGoalsRest,_,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,
	     MFSIn,MFSOut,NVs,_,_) :-
  !, term_variables(Goal,HookVars),
  map_vars(HookVars,HookNVars,NVs),
  tricky_vars_merge(HookNVars,VarsIn,VarsOut,MFSIn,MFSMid),
  replace_hook_fss(Goal,[],PGoal,PGoals,[PGoal|PGoalsRest],FSPal,FSsIn,FSsOut,MFSMid,MFSOut).
compile_body(prolog(NVs,Goal),PGoals,PGoalsRest,_,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,
	     MFSIn,MFSOut,NVs,_,_) :-
  !, term_variables(Goal,HookVars),
  map_vars(HookVars,HookNVars,NVs),
  tricky_vars_merge(HookNVars,VarsIn,VarsOut,MFSIn,MFSMid),
  replace_hook_fss(Goal,[],PGoal,PGoals,[PGoal|PGoalsRest],FSPal,FSsIn,FSsOut,MFSMid,MFSOut).
compile_body(when(Cond,WBody),PGoals,PGoalsRest,_Context,VarsIn,VarsOut,
	     FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  !,desc_varfs_body(when(Cond,WBody),WhenVars,WhenFSs,NVs),
  tricky_vars_merge(WhenVars,VarsIn,VarsTricky,MFSIn,MFSVarTricky),
  tricky_fss_merge(WhenFSs,FSsIn,FSsTricky,MFSVarTricky,MFSTricky),
  ( compile_cond(Cond,WBody,PGoals,PGoalsRest,VarsTricky,FSPal,FSsTricky,MFSTricky,NVs,PriorVs,ContVs)
  -> VarsTricky = VarsOut, MFSOut = MFSTricky, FSsOut = FSsTricky
  ; print_message(warning,ale(cond_failure(Cond,WBody))), PGoals = PGoalsRest,
    VarsOut = VarsIn, MFSOut = MFSIn, FSsOut = FSsIn
  ).
compile_body(AtGD,PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
             FSsIn,FSsOut,MFSIn,MFSOut,NVs,_,_):-
  AtGD =.. [Rel|ArgDescs],
  functor(AtGD,_,RelArity),
  empty_avl(EAssoc),
  initialise_rel_mode(RelArity,ArgPaths,EAssoc,ModeIn,MFSIn,MFSMid),
  compile_descs_fresh(ArgDescs,Args,ArgPaths,PGoals,[AtGoal|PGoalsRest],
                      Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,ModeIn,ModeMid,MFSMid,MFSMid2,NVs),
  verify_input_modes(RelArity,Rel,ArgPaths,ModeMid,MFSMid2),
  assert_output_modes(RelArity,Rel,ArgPaths,ModeMid,_,MFSMid2,MFSOut),
  cat_atoms('fs_',Rel,CompiledRel),
  AtGoal =.. [CompiledRel|Args].

% Really, we should only be doing this for continuations of prolog/1,2 hooks, which
%  are the only ALE built-ins that could have side effects.  That, however, would
%  require static analysis of the call graph, which we're not building yet.  So
%  right now, we're doing it after just about everything.  Remember that even
%  descriptions can contain functions, which can in turn call prolog/1,2 hooks.
compile_body_catch_fail(Goal,PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
			FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs) :-
  ( compile_body(Goal,PGoals,PGoalsRest,Context,VarsIn,VarsOut,FSPal,
		 FSsIn,FSsOut,MFSIn,MFSOut,NVs,PriorVs,ContVs)
  -> true
  ; PGoals = [fail|PGoalsRest], VarsOut = VarsIn, FSsOut = FSsIn, MFSOut = MFSIn
  ).

% ------------------------------------------------------------------------------
% compile_cond(Cond:<cond>,WBody:<goal>,
%              PGoals:<prolog_goals>,PGoalsRest:<prolog_goals>,
%              FSPal:<var>,FSsIn:<fs>s,FSsIn:<fs>s)
% ------------------------------------------------------------------------------
% Compile a delay condition into Prolog when/2 statements to delay execution of
%  PGoals-PGoalsRest, the compiled code for the ALE goal, WBody.  A delay on a
%  FS can be any function-free, inequation-free description.  Delays on 
%  multiple FSs closed under conjunction and disjunction are also supported.
% ------------------------------------------------------------------------------
compile_cond(X^(Cond),WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs) :-
  !, ( nonvar(X) -> error_msg((nl,write_list(['non-variable',X,used,in,quantifier]),nl))
     ; true
     ),
  % KNOWN BUG: because of EFD-closure, this will sometimes reject otherwise good vars - oh well
  avl_store(X,NVs,unseen,NewNVs), % innermost var gets priority
  ord_del_element(ContVs,X,CondContVs),
  ord_del_element(PriorVs,X,CondPriorVs),
  compile_cond(Cond,WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NewNVs,CondPriorVs,CondContVs).
compile_cond(Cond,WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs) :-
  transform_cond(Cond,CUFCond),
  compile_cond_list(CUFCond,WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs).

transform_cond(Cond,CUFCond) :-
  flatten_cond(Cond,FlatCond,[]),
  unfold_tails(FlatCond,UFCond),
  compress_feat_prefixes(UFCond,CUFCond).

% SHOULD RENAME VARIABLES TO REFLECT COND OR DESC PROPERLY
flatten_cond(FS=Desc,Descs,DescsRest) :-
  !,expand_cd_macros(Desc,EDesc),
  on_exception(fd(Exception),flatten_desc(EDesc,FS,[],Descs,DescsRest),
	       ( Exception = ill_cond_desc(Cond)
	          -> raise_exception(ale(ill_cond_desc(Cond,Desc)))
	       ; Exception = undef_cond_feat(F)
	          -> raise_exception(ale(undef_cond_feat(F,Desc)))
	       ; raise_exception(Exception)
	       )).
flatten_cond((C1;C2),[(FC1;FC2)|Rest],Rest) :-
  !,flatten_cond(C1,FC1,[]),
  flatten_cond(C2,FC2,[]).
flatten_cond((C1,C2),FC1,FC2Rest) :-
  !,flatten_cond(C1,FC1,FC2),
  flatten_cond(C2,FC2,FC2Rest).
flatten_cond(X,_,_) :-
  raise_exception(ale(ill_cond(X))).

expand_cd_macros(X,X) :-
  var(X),
  !.
expand_cd_macros([],e_list) :- !.
expand_cd_macros([H|T],(hd:EH,tl:ET)) :-
  !,expand_cd_macros(H,EH),
  expand_cd_macros(T,ET).
expand_cd_macros(@ MacroName,EDesc) :-
  !, ( (MacroName macro Desc) -> true
     ; error_msg((nl,write_list([undefined,macro,MacroName,used,in,description]),nl))
     ),  % we used to backtrack on macro definitions here - bad move
  expand_cd_macros(Desc,EDesc).
expand_cd_macros(F:Desc,F:EDesc) :-
  !,expand_cd_macros(Desc,EDesc).
expand_cd_macros((Desc1,Desc2),(EDesc1,EDesc2)) :-
  !,expand_cd_macros(Desc1,EDesc1),
  expand_cd_macros(Desc2,EDesc2).
expand_cd_macros((Desc1;Desc2),(EDesc1;EDesc2)) :-
  !,expand_cd_macros(Desc1,EDesc1),
  expand_cd_macros(Desc2,EDesc2).
expand_cd_macros(X,X).  % paths, types, etc. - flag inequations and functional descs later.
               % Paths can't be expanded because their implicit var is narrowly quantified.

% postcondition: when result list contains FS=Blah, Blah is never a list
% SHOULD RENAME VARIABLES TO REFLECT COND OR DESC PROPERLY
flatten_desc(X,FS,FeatPrefix,[FS=FPX|DsRest],DsRest) :-
  var(X),  % this case captures both FSs and vars
  !,unwind_prefix(FeatPrefix,X,FPX).
flatten_desc((D1,D2),FS,FeatPrefix,Descs,DsRest) :-
  !,flatten_desc(D1,FS,FeatPrefix,Descs,DsMid),
  flatten_desc(D2,FS,FeatPrefix,DsMid,DsRest).
flatten_desc(F:Desc,FS,FeatPrefix,Descs,DsRest) :-
  !, ( var(F) -> raise_exception(ale(feat_notatom(F,F:Desc)))
     ; approp(F,_,_) -> flatten_desc(Desc,FS,[F|FeatPrefix],Descs,DsRest)
     ; raise_exception(fd(undef_cond_feat(F)))
     ).
flatten_desc((D1;D2),FS,FeatPrefix,[(Ds1;Ds2)|DsRest],DsRest) :-
  !,flatten_desc(D1,FS,FeatPrefix,Ds1,[]),
  flatten_desc(D2,FS,FeatPrefix,Ds2,[]).
flatten_desc((Path1 == Path2),FS,FeatPrefix,[FS=FPEq|DsRest],DsRest) :-
  !,unwind_prefix(FeatPrefix,(Path1 == Path2),FPEq).
flatten_desc(Other,FS,FeatPrefix,[(FS=FPOther)|DsRest],DsRest) :-
%  type(Other), - seems to be here only to enforce no-ineq no-fun requirement
%  !, 
  unwind_prefix(FeatPrefix,Other,FPOther).
%flatten_desc(X,_,_,_,_) :-
%  raise_exception(fd(ill_cond_desc(X))).

unwind_prefix([],Desc,Desc).
unwind_prefix([F|Prefix],Desc,Result) :-
  unwind_prefix(Prefix,F:Desc,Result).

unfold_tails([],[]).
unfold_tails([FS=Desc|FRest],[FS=Desc|UFRest]) :-
  !,unfold_tails(FRest,UFRest).
unfold_tails([(FC1;FC2)|FRest],[(UFC1New;UFC2New)]) :-
  append(FC1,FRest,FC1New),
  append(FC2,FRest,FC2New),
  unfold_tails(FC1New,UFC1New),
  unfold_tails(FC2New,UFC2New).

compress_feat_prefixes([],[]).
compress_feat_prefixes([FS=X|Cond],[FS=X|CCond]) :-
  var(X),
  !,compress_feat_prefixes(Cond,CCond).
compress_feat_prefixes([FS=F:Desc|Cond],[FS=F:FDesc|CCondRest]) :-
  !,compress_fp_feat(Cond,F,FS,FDescs,CondRest),
  compress_feat_prefixes([FS=Desc|FDescs],CFDescs),
  collect_feat_descs(CFDescs,FDesc),
  compress_feat_prefixes(CondRest,CCondRest).
compress_feat_prefixes([FS=Other|Cond],[FS=Other|CCond]) :-
  !,compress_feat_prefixes(Cond,CCond).
compress_feat_prefixes([(C1;C2)],[(CC1;CC2)]) :-
  compress_feat_prefixes(C1,CC1),
  compress_feat_prefixes(C2,CC2).

compress_fp_feat([FS=F:Desc|CondRest],F,FS0,FDescs,FCondRest) :-
  FS == FS0,
  !,FDescs = [FS=Desc|FDescsRest],
  compress_fp_feat(CondRest,F,FS0,FDescsRest,FCondRest).
compress_fp_feat(CondRest,_,_,[],CondRest).

collect_feat_descs([_=Desc],Desc) :- !.
collect_feat_descs([_=Desc1|EqDescs],(Desc1,Desc2)) :-
  collect_feat_descs(EqDescs,Desc2).
  
compile_cond_list([Cond1|Cond2],WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs) :-
  compile_cond_list_act(Cond2,Cond1,WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs).

compile_cond_list_act([],(Cond1;Cond2),WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,
		      NVs,PriorVs,ContVs) :- 
  !,
  ord_add_element(PriorVs,Trigger,CondPriorVs),
  ord_add_element(ContVs,Trigger,CondContVs),
  ( compile_cond_list(Cond1,(prolog(Trigger = 0) -> WBody ; true),PGoals0,PGoalsMid,
		      Vars,FSPal,FSs,MFS,NVs,PriorVs,CondContVs)
  -> ( compile_cond_list(Cond2,(prolog(Trigger = 1) -> WBody ; true),PGoalsMid,
	    	         PGoalsRest,Vars,FSPal,FSs,MFS,NVs,CondPriorVs,ContVs)
     -> PGoals = PGoals0
     ; compile_cond_list(Cond1,WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs)
     )
  ; compile_cond_list(Cond2,WBody,PGoals,PGoalsRest,Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs)
  ).
compile_cond_list_act([],FS=Desc,WBody,[PGoal|PGoalsRest],PGoalsRest,Vars,FSPal,
		      FSs,MFS,NVs,PriorVs,ContVs) :-
  ( avl_fetch(FS,NVs,Status)
  -> ( Status == unseen -> raise_exception(ale(narrow_left(FS,Desc)))
     ; Status = seen(FSVar) -> compile_cond_desc(Desc,FSVar,WGoal,PGoal,Vars,VarsBody,
				  	         FSPal,FSs,FSsBody,MFS,MFSBody,NVs,NVsMid)
     )  % We have to use two separate calls to compile_cond_desc/11 because binding FS
        % could change its position in the standard order - then we wouldn't be able to
        % find it in assoc trees like NVs anymore
  ; compile_cond_desc(Desc,FS,WGoal,PGoal,Vars,VarsBody,FSPal,FSs,FSsBody,MFS,MFSBody,NVs,NVsMid)
  ),
% replace_nv_body(WBody,NBody,Vars,VarsTricky,NVs), % all narrow vars are tricky in body
%         % - maybe could do better, but user might wake up suspension by binding two
%         % vars in prolog hook without instantiating them
  avl_map(nv_fresh,NVsMid,NewNVs),
  term_variables(Desc,DescVars),
  ord_union(DescVars,PriorVs,BodyPriorVs),
  compile_body(WBody,BodyGoals,[],when_or_neg,VarsBody,_VarsLost,FSPal,FSsBody,
	       _FSsLost,MFSBody,_MFSLost,NewNVs,
               BodyPriorVs,ContVs), % KNOWN BUG: this might drag the FS palette into the suspension - bad move.
  goal_list_to_seq(BodyGoals,BodyGoalSeq),  %  goal_list_to_seq(BodyGoals,WGoal).	       
  prior_cont_vars(BodyGoalSeq,BodyVars),
  map_vars(BodyPriorVs,NewPriorVs,NewNVs),
  map_vars(ContVs,NewContVs,NewNVs),
  sort(NewPriorVs,SortedNewPriorVs),
  sort(NewContVs,SortedNewContVs),
  ord_intersection(BodyVars,SortedNewPriorVs,PriorBodyVars),
  ord_intersection(BodyVars,SortedNewContVs,ContBodyVars),
  ord_union(PriorBodyVars,ContBodyVars,ExternalVars),
  length(ExternalVars,EV),
  ( (heavy_sequence(BodyGoalSeq),
     EV < 256) -> genindex(N), cat_atoms('w',N,WGoalPredName),
                               WGoal =.. [WGoalPredName|ExternalVars],
                               assert(wpred(WGoal,BodyGoalSeq))
  ; WGoal = BodyGoalSeq
  ).
compile_cond_list_act([Cond|CondRest],FS=Desc,WBody,[PGoal|PGoalsRest],PGoalsRest,
		      Vars,FSPal,FSs,MFS,NVs,PriorVs,ContVs) :-
  ( avl_fetch(FS,NVs,Status)
  -> ( Status == unseen -> raise_exception(ale(narrow_left(FS,Desc)))
     ; Status = seen(FSVar) -> compile_cond_desc(Desc,FSVar,PGoal2,PGoal,Vars,VarsMid,
					         FSPal,FSs,FSsMid,MFS,MFSMid,NVs,NewNVs)
     )
  ; compile_cond_desc(Desc,FS,PGoal2,PGoal,Vars,VarsMid,FSPal,FSs,FSsMid,MFS,MFSMid,NVs,NewNVs)
  ),
  term_variables(Desc,DescVars),
  ord_union(DescVars,PriorVs,NewPriorVs),
  compile_cond_list_act(CondRest,Cond,WBody,PGoals2,[],VarsMid,FSPal,FSsMid,MFSMid,NewNVs,
                        NewPriorVs,ContVs),
  goal_list_to_seq(PGoals2,PGoal2).

compile_cond_desc(Var,FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVsIn,NVsOut) :-
  var(Var),
  !, '$get_attributes'(Var,TFS,_),
  ( var(TFS) ->  % Var is not a compile-time-bound FS
    FSsOut = FSsIn,

     (  avl_fetch(Var,NVsIn,SeenFlag)  % Var IS A NARROWLY QUANTIFIED VARIABLE
     -> ( SeenFlag == unseen                             % Is this the first time we've seen Var?
	-> avl_store(Var,NVsIn,seen(FreshVar),NVsOut),  % yes
	   ( avl_fetch(FS,VarsIn,vmode(FSSeenFlag,FSMode,CBSafe))
	   -> ( FSSeenFlag == tricky -> PGoal = ((FreshVar = FS),WGoal),
		                        avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafe),VarsMid),
		                        MFSMid = MFSIn
	      ; % FSSeenFlag == seen,
		PGoal = ((FreshVar = FS),WGoal), VarsMid = VarsIn, MFSMid = MFSIn
	      )
	   ; % FS has not been seen
	     PGoal = ((FreshVar = FS),WGoal),
	     fresh_mode(FSMode,MFSIn,MFSMid),
	     avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsMid)
	   ),
	   avl_store(FreshVar,VarsMid,vmode(seen,FSMode,false),VarsOut), MFSOut = MFSMid

	% no, we've seen Var before - it's mapped to NVar
	; SeenFlag = seen(NVar), NVsOut = NVsIn, % because of flattening, we either saw NVar or didn't
				                 % - no tricky case
	  ( avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafeFS))
	  -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafeFS),VarsMid), MFSMid = MFSIn
	  ; fresh_mode(FSMode,MFSIn,MFSMid),
	    avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsMid)
	  ),
	  ( avl_fetch(NVar,VarsMid,vmode(_,NVMode,CBSafeNV))
	  -> avl_store(NVar,VarsMid,vmode(seen,NVMode,CBSafeNV),VarsOut), MFSMid2 = MFSMid
	  ; fresh_mode(NVMode,MFSMid,MFSMid2),
	    avl_store(NVar,VarsMid,vmode(seen,NVMode,false),VarsOut)
	  ),
	  ( FSMode == NVMode -> PGoal = WGoal, MFSOut = MFSMid2  % either because FS == NVar, or they are 
	  ; PGoal = when_eq(FS,NVar,WGoal),                      %  already unified in this context
	    unify_mode(FSMode,NVMode,MFSMid2,MFSOut)
	  )
	)
     
     ; NVsOut = NVsIn,  	        % Var IS NOT A NARROWLY QUANTIFIED VARIABLE
	 ( avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafeFS))
	 -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafeFS),VarsMid), MFSMid = MFSIn
         ; fresh_mode(FSMode,MFSIn,MFSMid),
	   avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsMid)
         ),
         ( avl_fetch(Var,VarsMid,vmode(_,VMode,CBSafeVar))
	 -> avl_store(Var,VarsMid,vmode(seen,VMode,CBSafeVar),VarsOut), MFSMid2 = MFSMid
         ; fresh_mode(VMode,MFSMid,MFSMid2),
	   avl_store(Var,VarsMid,vmode(seen,VMode,false),VarsOut)
         ),
       ( FSMode == VMode -> PGoal = WGoal, MFSOut = MFSMid2 % either because FS == Var, or they are
       ; PGoal = when_eq(FS,Var,WGoal),                     %  already unified in this context
	 unify_mode(FSMode,VMode,MFSMid2,MFSOut)
       )
     )
  ; %compile_cond_desc(Tag-SVs,FS,WGoal,PGoal,Vars,Vars,FSPal,FSsIn,FSsOut,MFS,MFS,NVs,NVs) :-
    NVsOut = NVsIn,                                         % Var is a compile-time bound FS
    ( avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafeFS))
    -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafeFS),VarsOut), MFSMid = MFSIn
    ; fresh_mode(FSMode,MFSIn,MFSMid),
      avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsOut)
    ),
    track_fs(Var,FSVar,FSVarMode,FSSeen,Arg,FSsIn,FSsOut,MFSMid,MFSMid2),
    bind_fs(FSSeen,FSVar,Arg,FSPal,PGoals,[PGoalFinal]),
    ( FSVarMode == FSMode -> PGoalFinal = WGoal, MFSOut = MFSMid2
    ; unify_mode(FSMode,FSVarMode,MFSMid2,MFSOut),
      PGoalFinal = when_eq(FS,FSVar,WGoal)
    ),
%    find_fs(FSsIn,Var,PGoals,[when_eq(FS,FSVar,WGoal)],FSVar,FSPal,FSsOut),
    goal_list_to_seq(PGoals,PGoal)
  ).
compile_cond_desc(F:Desc,FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVsIn,
		  NVsOut) :-
  !,
  ( clause(introduce(F,FIntro),true) -> true
  ; raise_exception(ale(undef_feat(F)))
  ),

  (avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafe))
  -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafe),VarsMid), MFSMid = MFSIn
  ; fresh_mode(FSMode,MFSIn,MFSMid),
    avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsMid)
  ),

  get_mtype(FSMode,FSType,MFSMid),
  ( sub_type(FIntro,FSType) -> PGoal = (FGoal,DescGoal), MFSMid2 = MFSMid
  ; unify_type(FIntro,FSType,NewFSType), % FIntro cannot be a_/1 atom - has features
    PGoal = when_type(FIntro,FS,(FGoal,DescGoal)),
    assert_mode(NewFSType,FSMode,MFSMid,MFSMid2)
  ),

  feat_mode(F,FSMode,FSatFMode,FFill,MFSMid2,MFSMid3),

  clause(fcolour(F,K,_),true),
  FGoal0 = arg(K,FS,FSatF),
  (FFill == arg -> FGoal = FGoal0
  ; FFill = fill(FIntroRestr),
    ( FIntroRestr == bot -> FGoal = FGoal0
    ; atom(FIntroRestr) -> cat_atoms('add_to_typed_',FIntroRestr,FillRel),
	                   FillGoal =.. [FillRel,FSatF], FGoal = (FGoal0,FillGoal)
    ; arg(1,FIntroRestr,X), FillRel = 'add_to_typed_a_', FillGoal =.. [FillRel,FSatF,X],
	                    FGoal = (FGoal0,FillGoal)
    )
  ),
	
  avl_store(FSatF,VarsMid,vmode(seen,FSatFMode,false),VarsMid2),
  compile_cond_desc(Desc,FSatF,WGoal,DescGoal,VarsMid2,VarsOut,FSPal,FSsIn,FSsOut,MFSMid3,MFSOut,NVsIn,
		    NVsOut).
compile_cond_desc((Path1 == Path2),FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,
		  NVs,NVs) :-
  !,expand_path(Path1,PathVar,ExpPath1),
  expand_path(Path2,PathVar,ExpPath2),
  avl_store(PathVar,NVs,unseen,PathNVs),
  compile_cond_desc((ExpPath1,ExpPath2),FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,
		    FSsOut,MFSIn,MFSOut,PathNVs,_).
compile_cond_desc((Desc1,Desc2),FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVsIn,
		  NVsOut) :-
  !,compile_cond_desc(Desc1,FS,PGoal2,PGoal,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,MFSIn,MFSMid,NVsIn,
		      NVsMid),
  compile_cond_desc(Desc2,FS,WGoal,PGoal2,VarsMid,VarsOut,FSPal,FSsMid,FSsOut,MFSMid,MFSOut,NVsMid,
		    NVsOut).
%compile_cond_desc((Desc1;Desc2),FS,WGoal,(PGoal1,PGoal2),NVs) :-
%  !,compile_cond_desc(Desc1,FS,(Trigger=0 -> WGoal ; true),PGoal1,NarrowVars),
%  compile_cond_desc(Desc2,FS,(Trigger=1 -> WGoal ; true),PGoal2,NarrowVars).
compile_cond_desc((a_ X),FS,WGoal,PGoal,VarsIn,VarsOut,_,FSs,FSs,MFSIn,MFSOut,NVs,NVs) :-
  !,
  ( avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafe))
  -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafe),VarsOut), MFSMid = MFSIn
  ; fresh_mode(FSMode,MFSIn,MFSMid),
    avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsOut)
  ),

  get_mtype(FSMode,FSType,MFSMid),
  ( sub_type((a_ X),FSType) -> PGoal = WGoal, MFSOut = MFSMid
  ; cunify_type((a_ X),FSType,NewFSType),
    PGoal = when_a_(X,FS,WGoal),
    assert_mode(NewFSType,FSMode,MFSMid,MFSOut)
  ).
compile_cond_desc(Var,FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVsIn,NVsOut) :-
  functor(Var,Module,Arity),
  clause(marity(Module,Arity),true),
  !,
  NVsOut = NVsIn,
  ( avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafeFS))
  -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafeFS),VarsOut), MFSMid = MFSIn
  ; fresh_mode(FSMode,MFSIn,MFSMid),
    avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsOut)
  ),
%  find_fs(FSsIn,Var,PGoals,[when_eq(FS,FSVar,WGoal)],FSVar,FSPal,FSsOut),
  track_fs(Var,FSVar,FSVarMode,FSSeen,Arg,FSsIn,FSsOut,MFSMid,MFSMid2),
  bind_fs(FSSeen,FSVar,Arg,FSPal,PGoals,[PGoalFinal]),
  ( FSVarMode == FSMode -> PGoalFinal = WGoal, MFSOut = MFSMid2
  ; unify_mode(FSMode,FSVarMode,MFSMid2,MFSOut),
    PGoalFinal = when_eq(FS,FSVar,WGoal)
  ),
  goal_list_to_seq(PGoals,PGoal).
compile_cond_desc(Type,FS,WGoal,PGoal,VarsIn,VarsOut,_,FSsIn,FSsOut,MFSIn,MFSOut,NVs,NVs) :-
  non_a_type(Type),
  !,
  ( avl_fetch(FS,VarsIn,vmode(_,FSMode,CBSafe))
  -> avl_store(FS,VarsIn,vmode(seen,FSMode,CBSafe),VarsOut), MFSMid = MFSIn
  ; fresh_mode(FSMode,MFSIn,MFSMid),
    avl_store(FS,VarsIn,vmode(seen,FSMode,false),VarsOut)
  ),

  get_mtype(FSMode,FSType,MFSMid),
  ( sub_type(Type,FSType) -> PGoal = WGoal, MFSOut = MFSMid
  ; unify_type(Type,FSType,NewFSType),  % guarded not to be a_/1 atom
    PGoal = when_type(Type,FS,WGoal),
    assert_mode(NewFSType,FSMode,MFSMid,MFSOut)
  ),
  FSsOut = FSsIn.
compile_cond_desc(sem((a_ sem(X,Term,Pivot,Root,Anchor,LRSCode))),FS,WGoal,PGoal,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,
                  MFSIn,MFSOut,NVsIn,NVsOut) :-
  !, compile_body((FS = (sem:(a_ sem(Term,Anchor)),pivot:(a_ sem(Pivot,Anchor)),root:(a_ sem(Root,Anchor)))),
                  PGoals,[DelayedLRSGoal],serial,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,NVsIn),
  convert_lrs_to_delay(LRSCode,DelayedLRSGoal,WGoal,NVsIn,NVsOut),
  goal_list_to_seq([FS=X|PGoals],PGoal).
compile_cond_desc(X,_,_,_,_,_,_,_,_,_,_,_,_) :-
  error_msg((nl,write('undefined conditional description '),write(X),nl)).

expand_path([],Var,Var).
expand_path([Feat|Path],Var,(Feat:Rest)) :-
  expand_path(Path,Var,Rest).

heavy_sequence((_,_)).
heavy_sequence((IfG -> ThenG ; ElseG)) :- 
 !, ( heavy_sequence(IfG) -> true
    ; heavy_sequence(ThenG) -> true
    ; heavy_sequence(ElseG) -> true
    ).
heavy_sequence((_;_)).
% heavy_sequence(when(_,Goal)): the compiler might label Goal heavy, but for the inner when
heavy_sequence(\+ Goal) :- heavy_sequence(Goal).
heavy_sequence((IfG -> ThenG)) :-
   heavy_sequence(IfG) -> true
 ; heavy_sequence(ThenG) -> true.

prior_vars([],_,[]).
prior_vars([V|Vs],Vars,ExternalVars) :-
  get_assoc(V,Vars,_) -> ExternalVars = [V|EVarsRest], prior_vars(Vs,Vars,EVarsRest)
 ; prior_vars(Vs,Vars,ExternalVars).

prior_cont_vars(DtrsorBody,PCVs) :-
  prior_cont_vars(DtrsorBody,[],PCVs).

prior_cont_vars((C1,C2),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(C1,PCVsIn,PCVsMid),
  prior_cont_vars(C2,PCVsMid,PCVsOut).
prior_cont_vars((goal> G),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(G,PCVsIn,PCVsOut).
prior_cont_vars((\+ G),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(G,PCVsIn,PCVsOut).
prior_cont_vars((sem_goal> G),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(G,PCVsIn,PCVsOut).
prior_cont_vars((G1;G2),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(G1,PCVsIn,PCVsMid),
  prior_cont_vars(G2,PCVsMid,PCVsOut).
prior_cont_vars((G1 -> G2),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(G1,PCVsIn,PCVsMid),
  prior_cont_vars(G2,PCVsMid,PCVsOut).
prior_cont_vars(when(Cond,Body),PCVsIn,PCVsOut) :-
  !,prior_cont_vars(Body,[],PCVsBody),
  narrow_vars(Cond,NVs),
  sort(NVs,SortedNVs),
  ord_subtract(PCVsBody,SortedNVs,FreeBodyPCVs),
  ord_union(FreeBodyPCVs,PCVsIn,PCVsOut).
prior_cont_vars(AG,PCVsIn,PCVsOut) :-
  term_variables(AG,AGVars),
  ord_union(AGVars,PCVsIn,PCVsOut).

narrow_vars(V^Cond,[V|Vs]) :-
  !,narrow_vars(Cond,Vs).
narrow_vars(_,[]).

% ------------------------------------------------------------------------------
% when_type(Type:<type>,FS:<fs>,WGoal:<prolog_goal>)
% ------------------------------------------------------------------------------
% Wait until FS is of type Type, then execute WGoal.  Type is not bot.
% ------------------------------------------------------------------------------
%when_type(Type,FS,WGoal) :-
%  when(nonvar(FS),when_type0(Type,FS,WGoal)).

when_type(Type,FS,WGoal) :-
  deref(FS,TFS,FSType,_),
  when_type_act(FSType,TFS,Type,FS,WGoal).

when_type_act(0,_TFS,Type,FS,WGoal) :-
  !,  % Type is not bot, so we must delay - 0 means there's nothing attached
  '$put_attributes'(FS,tfs(bot,Int)),
  when_type_delayed(Type,FS,Int,WGoal).

when_type_act(bot,TFS,Type,FS,WGoal) :-
  !,  % Type is not bot, so we must delay - bot means there's something attached
  arg(2,TFS,Int),
  when_type_delayed(Type,FS,Int,WGoal).

when_type_act(FSType,TFS,Type,FS,WGoal) :-
  unify_type(Type,FSType,Result),
  !,
  ( Result == FSType -> call(WGoal)      % already of that type - assume approp
 	                                       % is satisfied (o.w. wont terminate on
	                                       % cyclic structures)
  ; functor(TFS,_,Arity),  
    arg(Arity,TFS,Int),
    when_type_delayed(Type,FS,Int,WGoal) % not yet - delay
  ).

when_type_act(_,_,_,_,_).   % never will be Type: will restore on backtracking
% formerly used shallow cuts, but overwhelming rate of success in unify_type/3 call above
%  makes this faster.

when_type_delayed(Type,FS,Int,WGoal) :-
  when(nonvar(Int),when_type_delayed0(Type,FS,Int,WGoal)).

when_type_delayed0(Type,FS,Int,WGoal) :-
  functor(Int,FSType,_),  % FSType promoted, so it isn't bot
  ( unify_type(Type,FSType,Result) 
  -> ( Result == FSType -> call(WGoal)  % formerly when_approp(Type,WGoal)
     ; arg(1,Int,NewInt),  % maximal types don't have this argument, but they'll never reach here
       when_type_delayed(Type,FS,NewInt,WGoal)
     )
  ; true
  ).

%when_type_delayed0(Type,TagIn,SVsIn,WGoal) :-
%  ( deref(TagIn,SVsIn,Tag,SVs)
%  -> when(nonvar(SVs),(functor(SVs,FSType,_),
%                       ( unify_type(Type,FSType,Result) 
%                       -> ( Result == FSType -> when_approp(FSType,SVs,WGoal)
%			  ; when_type_delayed(Type,Tag,SVs,WGoal)
%			  )
%                       ; true
%                       )))
%  ; true % pp_fs will restore on backtracking
%  ).

% ------------------------------------------------------------------------------
% when_a_(X:<prolog_term>,FS:<fs>,Goal:<prolog_goal)
% ------------------------------------------------------------------------------
% Like when_type/3, but for a_/1 atoms
% ------------------------------------------------------------------------------
when_a_(X,FS,WGoal) :-
  ( var(FS) -> '$get_attributes'(FS,_,FSType),
               ( FSType == 0 -> when(nonvar(FS),when_a_delayed(FS,X,WGoal)) % not yet - delay
	       ; FSType == bot -> when(nonvar(FS),when_a_delayed(FS,X,WGoal)) % not yet - delay
	       ; true		% never will be
	       )
  ; FS = (a_ FSX) -> % already a_ atom
                     when(?=(X,FSX),(X==FSX -> call(WGoal) ; true))   % not yet - delay
  ; true
  ).

when_a_delayed((a_ FSX),X,WGoal) :-
  !,when(?=(X,FSX),(X==FSX -> call(WGoal) ; true)).
when_a_delayed(_,_,_).  % succeed without calling WGoal for any other type

% ------------------------------------------------------------------------------
% when_eq(FS1:<fs>,FS2:<fs>,Goal:<prolog_goal>)
% ------------------------------------------------------------------------------
% Wait until FS1 == FS2, then execute Goal
% ------------------------------------------------------------------------------
when_eq(FS1,FS2,WGoal) :-
  when(?=(FS1,FS2),(FS1==FS2 -> call(WGoal) ; true)).

% inequations: 2-place call
ineq(FS1,FS2) :-
  dif(FS1,FS2).
	
% ------------------------------------------------------------------------------
% goal_list_to_seq(Goals:<goal>s, GoalsSeq:<goal_seq>)
% ------------------------------------------------------------------------------
%
% ------------------------------------------------------------------------------
goal_list_to_seq(Var,GsSeq) :-
  when(nonvar(Var),goal_list_to_seq_act(Var,GsSeq)).
  % we need these delays because ivar_unseen/8 may still be waiting for a CBSafe to
  % be bound.
goal_list_to_seq_act([],true).
goal_list_to_seq_act([G|Gs],GsSeq) :-
  ((G = true)
   -> goal_list_to_seq(Gs,GsSeq)
    ; goal_list_to_seq_act(Gs,G,GsSeq)).

goal_list_to_seq(Var,G,GsSeq) :-
  when(nonvar(Var),goal_list_to_seq_act(Var,G,GsSeq)).
goal_list_to_seq_act([],G,G).
goal_list_to_seq_act([G2|Gs],G,(G,GsSeq)):-
  goal_list_to_seq(Gs,G2,GsSeq).

% ------------------------------------------------------------------------------
% goal_list_to_disj(Goals:<goal>s, GoalsDisj:<goal_seq>)
% ------------------------------------------------------------------------------
%
% ------------------------------------------------------------------------------
goal_list_to_disj([],fail).
goal_list_to_disj([G|Gs],GsSeq) :-
  ((G = fail)
   -> goal_list_to_disj(Gs,GsSeq)
    ; goal_list_to_disj_act(Gs,G,GsSeq)).

goal_list_to_disj_act([],G,G).
goal_list_to_disj_act([G2|Gs],G,(G;GsSeq)):-
  goal_list_to_disj_act(Gs,G2,GsSeq).

% ------------------------------------------------------------------------------
% compile_descs(Descs,Vs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,
%               FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% compiles descriptions Descs to constraint Vs into diff list Goals-GoalsRest
% ------------------------------------------------------------------------------
compile_descs([],[],[],Goals,Goals,_,Vars,Vars,_,FSs,FSs,Mode,Mode,MFS,MFS,_).
compile_descs([ArgDesc|ArgDescs],[Arg|Args],[N|ArgPaths],SubGoals,SubGoalsRest,
	      Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  compile_desc(ArgDesc,Arg,SubGoals,SubGoalsMid,N,Context,VarsIn,VarsMid,
	       FSPal,FSsIn,FSsMid,ModeIn,ModeMid,MFSIn,MFSMid,NVs),
  compile_descs(ArgDescs,Args,ArgPaths,SubGoalsMid,SubGoalsRest,Context,VarsMid,
		VarsOut,FSPal,FSsMid,FSsOut,ModeMid,ModeOut,MFSMid,MFSOut,NVs).

% ------------------------------------------------------------------------------
% compile_descs_fresh(Descs,Vs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
%                     VarsOut,FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% similar to compile_descs, except that Vs are instantiated to Ref-bot
% before compiling Descs
% ------------------------------------------------------------------------------
% HACK: should eventually allow compiler to place relational call before end of
%  argument description code
compile_descs_fresh([],[],[],Goals,Goals,_,Vars,Vars,_,FSs,FSs,Mode,Mode,MFS,MFS,_).
compile_descs_fresh([ArgDesc|ArgDescs],[Arg|Args],[N|ArgPaths],SubGoals,SubGoalsRest,
		    Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  empty_avl(EAssoc),
  compile_desc_act(ArgDesc,EAssoc,ImplicitVars,SubGoals,SubGoalsMid,N,Context,
       	           VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeIn,ModeMid,MFSIn,MFSMid,NVs),
  ivar_fresh(N,N,ImplicitVars,FS,_,SubGoalsMid,SubGoalsMid2),
  FS = fs(Arg),  % can probably get rid of this wrapper
  compile_descs_fresh(ArgDescs,Args,ArgPaths,SubGoalsMid2,SubGoalsRest,Context,
		      VarsMid,VarsOut,FSPal,FSsMid,FSsOut,ModeMid,ModeOut,MFSMid,MFSOut,NVs).

% ==============================================================================
% Mode Tracking
% ==============================================================================
initialise_rel_mode(0,[],Mode,Mode,MFS,MFS) :- !.
initialise_rel_mode(A,[N|Paths],ModeIn,ModeOut,MFSIn,MFSOut) :-
  NewA is A - 1,
  genindex(N),
  initialise_mode(N,ModeIn,ModeMid,MFSIn,MFSMid),
  initialise_rel_mode(NewA,Paths,ModeMid,ModeOut,MFSMid,MFSOut).

initialise_mode(TermPath,ModeIn,ModeOut,MFSIn,MFSOut) :-
  fresh_mode(FMode,MFSIn,MFSOut),
  avl_store(TermPath,ModeIn,FMode,ModeOut).

fresh_mode(Mode,MFSIn,MFSOut) :-
  fresh_mode(bot,Mode,MFSIn,MFSOut).

fresh_mode(0,mode(FS,_,_),MFSIn,MFSOut) :-
  !, avl_store(FS,MFSIn,bot,MFSOut).
fresh_mode(bot,mode(FS,_,_),MFSIn,MFSOut) :-
  !, avl_store(FS,MFSIn,bot,MFSOut).
fresh_mode(lazy(T),mode(FS,_,_),MFSIn,MFSOut) :-
  !, avl_store(FS,MFSIn,lazy(T),MFSOut).
fresh_mode(T,mode(FS,_,_),MFSIn,MFSOut) :-  % second arg bound to ivar/1 when implicit var allocated
  avl_store(FS,MFSIn,mgsat(T),MFSOut).

verify_input_modes(_,_,_,_,_). % place-holder
assert_output_modes(_,_,_,Mode,Mode,MFS,MFS). % place-holder

assert_input_modes(0,_,[],Mode,Mode,MFS,MFS) :- !.
assert_input_modes(A,Rel,[_N|Paths],ModeIn,ModeOut,MFSIn,MFSOut) :-
  NewA is A - 1,
  ModeMid = ModeIn, % place-holder
  MFSMid = MFSIn,
  assert_input_modes(NewA,Rel,Paths,ModeMid,ModeOut,MFSMid,MFSOut).

verify_output_modes(_,_,_,_,_). % place-holder

assert_mode(type(T),TermPath,Mode,MFSIn,MFSOut) :-
  avl_fetch(TermPath,Mode,TermPathMode),
  assert_mode(T,TermPathMode,MFSIn,MFSOut).

assert_mode(path(Path),Mode,PMode,MFSIn,MFSOut) :-
  assert_mode_path(Path,Mode,PMode,MFSIn,MFSOut).

assert_mode_path([F|Path],Mode,FPMode,MFSIn,MFSOut) :-
  !,assert_mode_path(Path,Mode,PMode,MFSIn,MFSMid),
  clause(introduce(F,FIntro),true),
  assert_mode(FIntro,PMode,MFSMid,MFSMid2),
  feat_mode(F,PMode,FPMode,_,MFSMid2,MFSOut).
assert_mode_path(TermPath,Mode,PMode,MFS,MFS) :-
  avl_fetch(TermPath,Mode,PMode).

assert_mode(T,mode(FS,_IVar,Max),MFSIn,MFSOut) :-
  avl_fetch(FS,MFSIn,MSVs),  
  get_mfs_type(MSVs,Type,Exp),    % Look up current type
  ( T = max(Type2) -> Max = max     % set Max flag
  ; Type2 = T
  ),
  assert_mode_act(Type2,Type,Exp,MSVs,FS,MFSIn,MFSOut).

assert_mode_act(Type2,Type,Exp,MSVs,FS,MFSIn,MFSOut) :-
  ( sub_type(Type2,Type) -> MFSOut = MFSIn % do nothing to FS - mode already knows Type2
  ; Exp == mgsat -> cunify_type(Type2,Type,NewType),  % otherwise update FS - we might have let
                    avl_store(FS,MFSIn,mgsat(NewType),MFSOut) % some a_/1 atoms slip in here, because...
  ; Exp == atom -> cunify_type(Type2,Type,NewType), % Because modes are an approximation, we
                   avl_store(FS,MFSIn,mgsat(NewType),MFSOut) % would have to tabulate types
                   % that rooted principal filters of atomic types to re-establish this property.
  ; Exp == lazy -> cunify_type(Type2,Type,NewType),    % Type2 doesn't subsume Type, so the
                   avl_store(FS,MFSIn,mgsat(NewType),MFSOut)  % value moved - can't be lazy now
  ; Exp == expanded -> unify_type(Type2,Type,NewType),  % NewType is not a_/1 atom
                       approps(NewType,NewFRs,NewArity),
                       approps(Type,FRs,_),
                       functor(NewMSVs,NewType,NewArity),
                       avl_store(FS,MFSIn,NewMSVs,MFSMid),
                       assert_mode_approp(FRs,NewFRs,0,0,MSVs,NewMSVs,MFSMid,MFSOut)
  ).

assert_mode_approp([],NewFRs,_,NewI,_,NewSVs,MFSIn,MFSOut) :-
  assert_mode_fill(NewFRs,NewI,NewSVs,MFSIn,MFSOut).
assert_mode_approp([F:R|FRs],NewFRs,I,NewI,SVs,NewSVs,MFSIn,MFSOut) :-
  assert_mode_approp_act(NewFRs,F,R,FRs,I,NewI,SVs,NewSVs,MFSIn,MFSOut).

assert_mode_approp_act([NewF:NewR|NewFRs],F,R,FRs,I,NewI,SVs,NewSVs,MFSIn,MFSOut) :-
  NewIPlus1 is NewI + 1,
  arg(NewIPlus1,NewSVs,FMode),
  ( F == NewF -> IPlus1 is I + 1,
                 arg(IPlus1,SVs,FMode),
                 ( sub_type(NewR,R) -> MFSMid = MFSIn
		 ; assert_mode(NewR,FMode,MFSIn,MFSMid)
		 ),
                 assert_mode_approp(FRs,NewFRs,IPlus1,NewIPlus1,SVs,NewSVs,MFSMid,MFSOut)
  ; clause(introduce(NewF,NewFIntro),true), approp(NewF,NewFIntro,NewFIntroRestr),
    ( sub_type(NewR,NewFIntroRestr) -> fresh_mode(lazy(NewR),FMode,MFSIn,MFSMid)  % intro-restricted values are 
    ; fresh_mode(NewR,FMode,MFSIn,MFSMid)                                         %  unfilled
    ),
    assert_mode_approp_act(NewFRs,F,R,FRs,I,NewIPlus1,SVs,NewSVs,MFSMid,MFSOut)
  ).

assert_mode_fill([],_,_,MFS,MFS).
assert_mode_fill([NewF:NewR|NewFRs],NewI,NewSVs,MFSIn,MFSOut) :-
  NewIPlus1 is NewI + 1,
  clause(introduce(NewF,NewFIntro),true), approp(NewF,NewFIntro,NewFIntroRestr),
  ( sub_type(NewR,NewFIntroRestr) -> fresh_mode(lazy(NewR),NewRMode,MFSIn,MFSMid) % intro-restricted values are 
  ; fresh_mode(NewR,NewRMode,MFSIn,MFSMid)                                        %  unfilled
  ),
  arg(NewIPlus1,NewSVs,NewRMode),
  assert_mode_fill(NewFRs,NewIPlus1,NewSVs,MFSMid,MFSOut).

path_mode([F|Path],Mode,FPMode,[FFill|FillRest],MFSIn,MFSOut) :-
  !, path_mode(Path,Mode,PMode,FillRest,MFSIn,MFSMid),  % HACK: this is a good sign that Path should
  feat_mode(F,PMode,FPMode,FFill,MFSMid,MFSOut).        %  be stored in reversed order.
path_mode(TermPath,Mode,PMode,TermPath,MFS,MFS) :-
  avl_fetch(TermPath,Mode,PMode).

paths_mode([],_,[],[],MFS,MFS).
paths_mode([Path|Paths],Mode,[PMode|PModes],[Fill|Fills],MFSIn,MFSOut) :-
  path_mode(Path,Mode,PMode,Fill,MFSIn,MFSMid),
  paths_mode(Paths,Mode,PModes,Fills,MFSMid,MFSOut).

get_mtype(mode(MFS,_,_),T,MFSs) :-
  avl_fetch(MFS,MFSs,MSVs),
  get_mfs_type(MSVs,T,_).

get_mfs_type((a_ X),(a_ X),atom) :- !.
get_mfs_type(mgsat(T),T,mgsat) :- !.
get_mfs_type(lazy(T),T,lazy) :- !.
get_mfs_type(SVs,T,Status) :-
  functor(SVs,T,Arity),
  ( Arity == 0 -> Status = atom
  ; Status = expanded
  ).

fs_to_mode(FS,Mode,MFSIn,MFSOut) :-
  empty_avl(FSAssoc),  % we need this to check for cycles during conversion
  fs_to_mode(FS,bot,Mode,FSAssoc,_,MFSIn,MFSOut).
% but really we should never use bot --- fs_to_mode/4 should not
%  be called on unattributed variables.

fs_to_mode(FS,LazyType,mode(MFS,_,_),FSIn,FSOut,MFSIn,MFSOut) :-
  avl_fetch(FS,FSIn,MFS) -> MFSOut = MFSIn, FSOut = FSIn
  ; get_type(FS,Type),
    ( Type == 0 -> MSVs = lazy(LazyType), FSOut = FSIn,  % KNOWN BUG: Are 0s never shared?  If so, add FS to FS Assoc
	           avl_store(MFS,MFSIn,MSVs,MFSOut)
    ; approps(Type,FRs,Arity),
      ( functor(Type,'a_',1) -> MSVs = Type
      ; functor(MSVs,Type,Arity)
      ),
      avl_store(MFS,MFSIn,MSVs,MFSMid),
      avl_store(FS,FSIn,MFS,FSMid),
      fs_to_mode_act(FRs,0,FS,MSVs,FSMid,FSOut,MFSMid,MFSOut)
    ).

fs_to_mode_act([],_,_,_,FS,FS,MFS,MFS).
fs_to_mode_act([F:R|FRs],I,FS,MSVs,FSIn,FSOut,MFSIn,MFSOut) :-
  NewI is I + 1,
  arg(NewI,MSVs,FMode),
  clause(fcolour(F,FPos,_),true),
  arg(FPos,FS,FFS),
  fs_to_mode(FFS,R,FMode,FSIn,FSMid,MFSIn,MFSMid),
  fs_to_mode_act(FRs,NewI,FS,MSVs,FSMid,FSOut,MFSMid,MFSOut).
	
unify_mode(mode(MFS1,IVar,Max),mode(MFS2,IVar,Max),MFSIn,MFSOut) :-
  unify_mfs(MFS1,MFS2,MFSIn,MFSOut).

unify_mfs(MFS1,MFS2,MFSIn,MFSOut) :-
  avl_fetch(MFS1,MFSIn,MSVs1),
  avl_fetch(MFS2,MFSIn,MSVs2),
  ( MSVs1 == MSVs2 -> MFSOut = MFSIn
  ;  unify_mfs_act(MSVs1,MSVs2,MFS1,MFS2,MFSIn,MFSOut)
  ).

unify_mfs_act(MSVs1,MSVs2,MFS1,MFS2,MFSIn,MFSOut) :-
%  avl_fetch(MFS1,MFSIn,MSVs1),
%  avl_delete(MFS2,MFSIn,MSVs2,MFSMid),
%  MFS1 = MFS2,  % doing this is as bad as unifying source-code variables - they follow the compiler through disjunctions
  get_mfs_type(MSVs1,T1,Exp1),
  get_mfs_type(MSVs2,T2,Exp2),
  unify_type(T1,T2,TResult),  % KNOWN BUG: should this not be cunify_type/3?
  ( Exp1 == expanded -> ( Exp2 == expanded -> approps(T1,FRs1,Arity1),
			                      ( T1 == T2 -> avl_store(MFS2,MFSIn,MSVs1,MFSMid),
                                                            unify_mfs_eq(0,Arity1,MSVs1,MSVs2,MFSMid,MFSOut)
					      ; approps(T2,FRs2,_Arity2),
						( sub_type(T1,T2) -> avl_store(MFS1,MFSIn,MSVs2,MFSMid),
		                                    unify_mfs_subs(FRs1,FRs2,MSVs1,0,MSVs2,0,MFSMid,MFSOut)
						; sub_type(T2,T1) -> avl_store(MFS2,MFSIn,MSVs1,MFSMid),
                                                                     unify_mfs_subs(FRs2,FRs1,MSVs2,0,MSVs1,0,
						    		                    MFSMid,MFSOut)
						; approps(TResult,FRsResult,ArityResult),
						  functor(MSVsResult,TResult,ArityResult),
						  avl_store(MFS1,MFSIn,MSVsResult,MFSMid),
                                                  avl_store(MFS2,MFSMid,MSVsResult,MFSMid2),
 				                  unify_mfs_unif(FRs1,FRs2,FRsResult,MSVs1,0,MSVs2,0,
							         MSVsResult,0,MFSMid2,MFSOut)
						)
					      )
                        ; % Exp2 == mgsat, lazy or atom,
  		          ( sub_type(T2,T1) -> avl_store(MFS2,MFSIn,MSVs1,MFSOut)
			  ; approps(TResult,FRsResult,ArityResult),
		            approps(T1,FRs1,_Arity1),
			    functor(MSVsResult,TResult,ArityResult),
			    avl_store(MFS1,MFSIn,MSVsResult,MFSMid),
                            avl_store(MFS2,MFSMid,MSVsResult,MFSMid2),
			    assert_mode_approp(FRs1,FRsResult,0,0,MSVs1,MSVsResult,MFSMid2,MFSOut)
			  )
			)
    ; sub_type(T1,T2) -> avl_store(MFS1,MFSIn,MSVs2,MFSOut)
    ; Exp1 == lazy -> ( Exp2 == lazy -> ( sub_type(T2,T1) -> avl_store(MFS2,MFSIn,MSVs1,MFSOut)
					; avl_store(MFS1,MFSIn,lazy(TResult),MFSMid),
                                          avl_store(MFS2,MFSMid,lazy(TResult),MFSOut)
					)
		      ; Exp2 == expanded -> approps(TResult,FRsResult,ArityResult),
					    approps(T2,FRs2,_Arity2),
					    functor(MSVsResult,TResult,ArityResult),
					    avl_store(MFS1,MFSIn,MSVsResult,MFSMid),
                                            avl_store(MFS2,MFSMid,MSVsResult,MFSMid2),
					    assert_mode_approp(FRs2,FRsResult,0,0,MSVs2,MSVsResult,
						               MFSMid2,MFSOut)
		      ; % Exp2 == mgsat or atom
                        avl_store(MFS1,MFSIn,mgsat(TResult),MFSMid),
			avl_store(MFS2,MFSMid,mgsat(TResult),MFSOut)
		      )
    ; % Exp1 == mgsat or atom
      ( Exp2 == expanded -> approps(TResult,FRsResult,ArityResult),
		            approps(T2,FRs2,_Arity2),
			    functor(MSVsResult,TResult,ArityResult),
			    avl_store(MFS1,MFSIn,MSVsResult,MFSMid),
                            avl_store(MFS2,MFSMid,MSVsResult,MFSMid2),
			    assert_mode_approp(FRs2,FRsResult,0,0,MSVs2,MSVsResult,MFSMid2,MFSOut)
      ; % Exp2 == mgsat, lazy or atom
	( sub_type(T2,T1) -> avl_store(MFS2,MFSIn,MSVs1,MFSOut)
        ; avl_store(MFS1,MFSIn,mgsat(TResult),MFSMid),
          avl_store(MFS2,MFSMid,mgsat(TResult),MFSOut)
	)
      )
    ).

unify_mfs_eq(A,A,_,_,MFS,MFS) :- !.
unify_mfs_eq(I,A,MSVs1,MSVs2,MFSIn,MFSOut) :-
  NewI is I + 1,
  arg(NewI,MSVs1,Arg1),
  arg(NewI,MSVs2,Arg2),
  unify_mode(Arg1,Arg2,MFSIn,MFSMid),
  unify_mfs_eq(NewI,A,MSVs1,MSVs2,MFSMid,MFSOut).

unify_mfs_subs([],_,_,_,_,_,MFS,MFS).
unify_mfs_subs([F:_|FRs1],FRs2,MSVs1,I1,MSVs2,I2,MFSIn,MFSOut) :-
  unify_mfs_subs_act(FRs2,F,FRs1,MSVs1,I1,MSVs2,I2,MFSIn,MFSOut).

%unify_mfs_subs_act([],_,_,_,_,_,_) - cannot happen
unify_mfs_subs_act([F2:_|FRs2],F1,FRs1,MSVs1,I1,MSVs2,I2,MFSIn,MFSOut) :-
  NewI2 is I2 + 1,
  ( F2 == F1 -> NewI1 is I1 + 1,
                arg(NewI1,MSVs1,Arg1),
                arg(NewI2,MSVs2,Arg2),
                unify_mode(Arg1,Arg2,MFSIn,MFSMid),
                unify_mfs_subs(FRs1,FRs2,MSVs1,NewI1,MSVs2,NewI2,MFSMid,MFSOut)
  ; unify_mfs_subs_act(FRs2,F1,FRs1,MSVs1,I1,MSVs2,NewI2,MFSIn,MFSOut)
  ).

unify_mfs_unif([],FRs2,FRsResult,_,_,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut) :-
  assert_mode_approp(FRs2,FRsResult,I2,I3,MSVs2,MSVs3,MFSIn,MFSOut).
unify_mfs_unif([F1:R1|FRs1],FRs2,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut) :-
  unify_mfs_unif_act(FRs2,F1,R1,FRs1,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut).

unify_mfs_unif_act([],F1,R1,FRs1,FRsResult,MSVs1,I1,_,_,MSVs3,I3,MFSIn,MFSOut) :-
  assert_mode_approp_act(FRsResult,F1,R1,FRs1,I1,I3,MSVs1,MSVs3,MFSIn,MFSOut).
unify_mfs_unif_act([F2:R2|FRs2],F1,R1,FRs1,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut) :-
  compare(Comp,F1,F2),
  unify_mfs_unif_comp(Comp,F1,R1,FRs1,F2,R2,FRs2,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut).

unify_mfs_unif_comp(=,F,R1,FRs1,_F,R2,FRs2,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut) :-
  unify_type(R1,R2,R1UnifyR2),
  NewI1 is I1 + 1,
  NewI2 is I2 + 1,
  arg(NewI1,MSVs1,Arg1),
  arg(NewI2,MSVs2,Arg2),
  unify_mode(Arg1,Arg2,MFSIn,MFSMid),
  unify_mfs_unif_find(FRsResult,Arg1,F,R1UnifyR2,MSVs3,I3,FRsResOut,NewI3,MFSMid,MFSMid2),
  unify_mfs_unif(FRs1,FRs2,FRsResOut,MSVs1,NewI1,MSVs2,NewI2,MSVs3,NewI3,MFSMid2,MFSOut).
unify_mfs_unif_comp(<,F1,R1,FRs1,F2,R2,FRs2,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut) :-
  NewI1 is I1 + 1,
  arg(NewI1,MSVs1,Arg1),
  unify_mfs_unif_find(FRsResult,Arg1,F1,R1,MSVs3,I3,FRsResOut,NewI3,MFSIn,MFSMid),
  unify_mfs_unif_act(FRs1,F2,R2,FRs2,FRsResOut,MSVs2,I2,MSVs1,NewI1,MSVs3,NewI3,MFSMid,MFSOut).
unify_mfs_unif_comp(>,F1,R1,FRs1,F2,R2,FRs2,FRsResult,MSVs1,I1,MSVs2,I2,MSVs3,I3,MFSIn,MFSOut) :-
  NewI2 is I2 + 1,
  arg(NewI2,MSVs2,Arg2),
  unify_mfs_unif_find(FRsResult,Arg2,F2,R2,MSVs3,I3,FRsResOut,NewI3,MFSIn,MFSMid),
  unify_mfs_unif_act(FRs2,F1,R1,FRs1,FRsResOut,MSVs1,I1,MSVs2,NewI2,MSVs3,NewI3,MFSMid,MFSOut).

%unify_mfs_unif_find([],_,_,_,_,_,_,_,_,_,_,_) - cannot happen
unify_mfs_unif_find([FRes:RRes|FRsResult],Arg,F,R,MSVs3,I3,FRsResOut,NewI3,MFSIn,MFSOut) :-
  ( FRes == F -> NewI3 is I3 + 1,
                 arg(NewI3,MSVs3,Arg),
                 ( sub_type(RRes,R) -> MFSOut = MFSIn
		 ; assert_mode(RRes,Arg,MFSIn,MFSOut)  % non-join-homomorphic case
		 ),
                 FRsResOut = FRsResult
  ; MidI3 is I3 + 1,                     		% introduced feature
    arg(MidI3,MSVs3,MFS3),
    clause(introduce(FRes,FResIntro),true), approp(FRes,FResIntro,FResIntroRestr),
    ( sub_type(RRes,FResIntroRestr) -> avl_store(MFS3,MFSIn,lazy(RRes),MFSMid)
    ; avl_store(MFS3,MFSIn,mgsat(RRes),MFSMid)
    ),
    unify_mfs_unif_find(FRsResult,Arg,F,R,MSVs3,MidI3,FRsResOut,NewI3,MFSMid,MFSOut)  
  ).
	
feat_mode(F,Mode,FMode,FFill,MFSIn,MFSOut) :-
  arg(1,Mode,MFS),
  avl_fetch(MFS,MFSIn,MSVs),
  feat_mode_act(MSVs,MFS,F,FMode,FFill,MFSIn,MFSOut).

feat_mode_act(mgsat(T),MFS,F,FMode,FFill,MFSIn,MFSOut) :-
  !,approps(T,FRs,Arity),
  functor(NewSVs,T,Arity),
  avl_store(MFS,MFSIn,NewSVs,MFSMid),
  assert_mode_fill(FRs,0,NewSVs,MFSMid,MFSOut),
  nthchk(N,FRs,(F:_)),
  arg(N,NewSVs,FMode),
  bind_fill(FMode,FFill,MFSOut).
feat_mode_act(lazy(T),MFS,F,FMode,FFill,MFSIn,MFSOut) :-
  !,approps(T,FRs,Arity),
  functor(NewSVs,T,Arity),
  avl_store(MFS,MFSIn,NewSVs,MFSMid),
  assert_mode_fill(FRs,0,NewSVs,MFSMid,MFSOut),
  nthchk(N,FRs,(F:_)),
  arg(N,NewSVs,FMode),
  bind_fill(FMode,FFill,MFSOut).  
%  get_mfs(FMode,FMFS),
%  avl_fetch(FMFS,MFSOut,FMSVs),
%  ( FMSVs = lazy(FillType) -> FFill = fill(FillType)
%  ; FFill = arg
%  ).
feat_mode_act(MSVs,_,F,FMode,FFill,MFS,MFS) :-
  get_mfs_type(MSVs,T,_),
  approps(T,FRs,_),
  nthchk(N,FRs,(F:_)),
  arg(N,MSVs,FMode),
  bind_fill(FMode,FFill,MFS).
%  get_mfs(FMode,FMFS),
%  avl_fetch(FMFS,MFS,FMSVs),
%  ( FMSVs = lazy(FillType) -> FFill = fill(FillType)
%  ; FFill = arg
%  ).  

bind_fill(Mode,Fill,MFS) :-
  arg(1,Mode,FMFS),
  avl_fetch(FMFS,MFS,FMSVs),
  ( FMSVs = lazy(FillType) -> Fill = fill(FillType)
  ; Fill = arg
  ).

nthchk(N,Xs,X) :- nth1(N,Xs,X),!.

mode_merge(ModeIn,_ModeDisj1,_ModeDisj2,ModeIn). % place-holder

mfs_merge(MFSIn,MFSDisj1,MFSDisj2,_Context,MFSOut) :- % place-holder: FSA intersection
  avl_to_list(MFSDisj1,MFSs1),
  avl_to_list(MFSDisj2,MFSs2),
  mfs_merge(MFSs1,MFSs2,MFSIn,MFSOutList),
  ord_list_to_avl(MFSOutList,MFSOut).

mfs_merge([],MFS2,MFSIn,MFSOut) :-
  mfs_merge_rest(MFS2,MFSIn,MFSOut).
mfs_merge([Var-_|MFS1],MFS2,MFSIn,MFSOut) :-
  mfs_merge_nelist(MFS2,Var,MFS1,MFSIn,MFSOut).

mfs_merge_nelist([],Var,MFS1,MFSIn,[Var-MSVsOut|MFSOut]) :-
  ( avl_fetch(Var,MFSIn,MSVsOut) -> true
  ; MSVsOut = bot
  ),
  mfs_merge_rest(MFS1,MFSIn,MFSOut).
mfs_merge_nelist([Var2-_|MFS2],Var1,MFS1,MFSIn,MFSOut) :-
  compare(Comp,Var1,Var2),
  mfs_merge_nelist_act(Comp,Var1,Var2,MFS1,MFS2,MFSIn,MFSOut).

mfs_merge_nelist_act(=,Var,_Var,MFS1,MFS2,MFSIn,[Var-MSVsOut|MFSOut]) :-
  ( avl_fetch(Var,MFSIn,MSVsOut) -> true  % HACK: just back off to the input - could be that they have more in common
  ; MSVsOut = bot
  ),
  mfs_merge(MFS1,MFS2,MFSIn,MFSOut).
mfs_merge_nelist_act(<,Var1,Var2,MFS1,MFS2,MFSIn,[Var1-MSVsOut|MFSOut]) :-
  ( avl_fetch(Var1,MFSIn,MSVsOut) -> true
  ; MSVsOut = bot
  ),
  mfs_merge_nelist(MFS1,Var2,MFS2,MFSIn,MFSOut).
mfs_merge_nelist_act(>,Var1,Var2,MFS1,MFS2,MFSIn,[Var2-MSVsOut|MFSOut]) :-
  ( avl_fetch(Var2,MFSIn,MSVsOut) -> true
  ; MSVsOut = bot
  ),
  mfs_merge_nelist(MFS2,Var1,MFS1,MFSIn,MFSOut).


mfs_merge_rest([],_,[]).
mfs_merge_rest([Var-_|MFS],MFSIn,[Var-MSVsOut|MFSOut]) :-
  ( avl_fetch(Var,MFSIn,MSVsOut) -> true
  ; MSVsOut = bot
  ),
  mfs_merge_rest(MFS,MFSIn,MFSOut).

% ==============================================================================
% Phrase Structure Rule Compiler
% ==============================================================================

:-dynamic curr_lex_rule_depth/1.
curr_lex_rule_depth(2).

% ------------------------------------------------------------------------------
% lex_rule_depth(N:<int>)
% ------------------------------------------------------------------------------
% asserts curr_lex_rule_depth/1 to N -- controls lexical rule depth
% ------------------------------------------------------------------------------
lex_rule_depth(N):-
  retractall(curr_lex_rule_depth(_)),
  assert(curr_lex_rule_depth(N)).

% ------------------------------------------------------------------------------
% lex(Word:<word>, Tag:<var_tag>, SVs:<svs>, IqsOut:<ineq>s)               mh(0)
% ------------------------------------------------------------------------------
% Word has category Tag-SVs
% ------------------------------------------------------------------------------
lex(_,_) if_b [fail] :-
  current_predicate('--->',(_ ---> _)) -> \+ (_ ---> _) ; true.
lex(Word,FS) if_b Goals :-
  current_predicate('--->',(_ ---> _)),
%  lex_tick_reset, % DEBUG
  (WordStart ---> DescOrGoal),
%  write(user_error,'**DEBUG:'),write(user_error,WordStart), nl(user_error), flush_output(user_error), % DEBUG
   add_lex(WordStart,DescOrGoal,Word,FS,Goals).
%   lex_tick. % DEBUG

:- dynamic lextick/1.
lex_tick :-
  retract(lextick(L)),
  NewL is L + 1,
  assert(lextick(NewL)),
  write(user_error,NewL),nl(user_error), flush_output(user_error),
  fail.
lex_tick_reset :-
  retractall(lextick(_)),
  assert(lextick(0)).

add_lex(WordStart,DescOrGoal,Word,FS,Goals) :-
  lex_desc_goal(DescOrGoal,Desc,true,GoalStart),
  lex_act(Word,FS,Goals,WordStart,Desc,GoalStart).

lex_desc_goal(DescOrGoal,Desc,GoalSeek,GoalStart) :-
  ( var(DescOrGoal) -> Desc = DescOrGoal, GoalStart = GoalSeek
  ; functor(DescOrGoal,goal,2) -> arg(1,DescOrGoal,Desc),
                                  arg(2,DescOrGoal,GoalStart)
  ; Desc = DescOrGoal, GoalStart = GoalSeek
  ).

lex_act(Word,FS,Goals,WordStart,Desc,GoalStart) :-
  term_variables(Desc,DescVars),
  term_variables(GoalStart,GoalVars),
  ( ord_intersect(GoalVars,DescVars) -> Link = link % FSStart must be tabulated in palette
  ; Link = nolink
  ),
  if((add_to(Desc,FSStart,bot,tfs(bot,_),FSStart,bot),
      apply_forall_lex(WordStart,FSStart)),
     (curr_lex_rule_depth(Max),
      lex_close(0,Max,WordStart,FSStart,DescVars,GoalStart,Link,Word,FS,Goals)),
     error_msg((write('lex: unsatisfiable lexical entry for '),
                write(WordStart),nl))).

% ------------------------------------------------------------------------------
% lex_close(WordIn:<word>, TagIn:<var_tag>, SVsIn:<svs>,
%           WordOut:<word>, TagOut:<var_tag>, SVsOut:<svs>, IqsIn:<ineq>s,
%           IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% If WordIn has category TagIn-SVsIn, then WordOut has category
% TagOut-SVsOut;  computed by closing under lexical rules
% ------------------------------------------------------------------------------
lex_close(_,_,Word,FS,DescVars,Goal,Link1,Word,FSVar,Goals0) :-
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(MFSIn),
  empty_avl(NVs),
  residuate_term(FS,ResidueSeq),
  ( Link1 == link -> Link2 = link            % Another reason to tabulate structure is that
  ; term_variables(ResidueSeq,ResidueVars),  % the residues themselves share structure with the body goals
    term_variables(Goal,GoalVars), % Recompute this even if Goal = GoalStart because forall_lex_rule may have instantiated more structure
    ( ord_intersect(GoalVars,ResidueVars) -> Link2 = link
    ; Link2 = nolink
    )
  ),
  ( Link2 == link -> track_fs(FS,FSVar,_FSVarMode,FSSeen,Arg,FSsIn,FSsMid,MFSIn,MFSMid), % the assertion in here will residuate FS again
                     bind_fs(FSSeen,FSVar,Arg,FSPal,Goals,GoalsMid) 
      % find_fs([],FS,Goals,GoalsMid,FSVar,FSPal,FSsMid)
  ; FSsMid = FSsIn, FS = FSVar, MFSMid = MFSIn,
    ( ResidueSeq == true -> Goals = GoalsMid
    ; Goals = [ResidueSeq|GoalsMid]
    )
  ),
  compile_body(Goal,GoalsMid,[],serial,VarsIn,_,FSPal,FSsMid,FSsOut,MFSMid,_,NVs,DescVars,[]),
  build_fs_palette(FSsOut,FSPal,Goals0,Goals,lex).
lex_close(N,Max,WordIn,FSIn,_,Goal,_,WordOut,FSOut,Goals):-
  current_predicate(lex_rule,lex_rule(_,_,_,_,_,_,_,_)),
  N < Max,
  lex_rule(WordIn,FSIn,Goal,WordMid,FSMid,DescMidVars,GoalMid,Link),
  NPlus1 is N + 1,
  lex_close(NPlus1,Max,WordMid,FSMid,DescMidVars,GoalMid,Link,WordOut,FSOut,Goals).

% lex_goal/2 - run-time hooks for lexical items.
%lex_goal(Phon,FS) :-
%  current_predicate(fs_lex_goal,fs_lex_goal(_,_))
%  -> fs_lex_goal(Phon,FS)
%  ; true. 

forall_lex(_,_,_) if_b [true] :-
  \+ current_predicate(forall,(_ forall _)),
  !.
forall_lex(_,_,_) if_b [true] :-
  \+ (_ forall _ ---> _ do _),
  !.
forall_lex(_,_,_) if_b _ :-
  findall(Name,(Name forall _ ---> _ do _),Names),
  has_duplicates(Names),
  append(_,[Name|Rest],Names), member_eq(Name,Rest),
  raise_exception(ale(forall_lex_dup(Name))).
forall_lex(Name,Word,FS) if_b Goals :-
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(EMFS),
  empty_avl(ENVs),
  (Name forall WordArg ---> Desc do Body),
  desc_varfs_desc(Desc,[],DescVars,[],_,[],ENVs),
  sort(DescVars,SortedDescVars), % remove duplicates
  list_to_nv_unseen(SortedDescVars,DescNVs),
  compile_body((prolog(Word=WordArg) -> when(FS=Desc,Body) ; true),Goals,[],serial,
	       VarsIn,_,_,FSsIn,_,EMFS,_,DescNVs,[],[]).  % Prolog doesn't have any notion of
% narrow variable scope on its delays, so we can't delay until Word==WordArg (which some
% twisted soul might want if their Words are compound Prolog terms).

apply_forall_lex(_,_) if_b [true] :-
  \+ current_predicate(forall,(_ forall _)),
  !.
apply_forall_lex(Word,FS) if_b Goals :-
  ebagof(forall_lex(Name,WParm,FParm),W^D^B^((Name forall W ---> D do B),
	  				     WParm = Word, FParm = FS),Goals).

% ------------------------------------------------------------------------------
% empty_cat(N:<neg>, Node:<int>, Tag:<var_tag>, SVs:<svs>, Iqs:<ineq>s, 
%           Dtrs:<ints>, RuleName:<atom>)                                  mh(0)
% ------------------------------------------------------------------------------
empty_cat(_,_,_,_,_) if_h [fail] :-
  \+ current_predicate(empty,empty(_)),
  ( true
  ; current_predicate(rule,(_ rule _)),
    findall(alec_rule(RuleName,Dtrs,_,Mother,true,PrevDtrs,PrevDtrs,DtrStore,DtrStore),
	    (RuleName rule Mother ===> Dtrs),Rules),
    name_rules(Rules,NamedRules),
    member(Rule,NamedRules),
    assert(Rule),
    fail
  ).
empty_cat(N,Node,FSHead,Dtrs,RuleName) if_h SubGoals :-
  current_predicate(empty,empty(_)),
  findall(empty(M,_,FS,ResidueSeq,[],empty),
   (empty(Desc),
    add_to(Desc,FS,bot,tfs(bot,_),FS,bot),
    gen_emptynum(M),
    residuate_term(FS,ResidueSeq)
%  curr_lex_rule_depth(Max),             % should we be closing empty cats
%  lex_close(0,Max,e,Tag,bot,_,TagMid,SVsMid,IqsIn,IqsMid), % under lex. rules?
    ),
   BasicEmptys),

  (ale_flag(subtest,off)
  -> MinimalEmptys = BasicEmptys
   ; minimise_emptys(BasicEmptys,[],MinimalEmptys)
  ),

  close_emptys(MinimalEmptys,ClosedEmptys,ClosedRules),

  (ale_flag(subtest,off)
  -> MinimalClosedEmptys = ClosedEmptys
   ; minimise_emptys(ClosedEmptys,[],MinimalClosedEmptys)
  ),

 (( MinimalClosedEmptys = [] -> SubGoals = [fail]
  ; member(empty(N,Node,FSOut,ResidueSeq,Dtrs,RuleName),MinimalClosedEmptys), % SP4: rebind residue at run-time
    ( ResidueSeq = true -> SubGoals = [], FSOut = FSHead
    ; SubGoals = [ResidueSeq,FSHead = FSOut]  % SP4: but FSHead might be bound already
    )
  )
 ; name_rules(ClosedRules,NamedClosedRules),
   member(Rule,NamedClosedRules),
   assert(Rule),
   fail
 ).

% ------------------------------------------------------------------------------
% minimise_emptys(+Emptys:<empty>s,+Accum:<empty>s,?MinimalEmptys:<empty>s)
% ------------------------------------------------------------------------------
% MinimalEmptys is the minimal list resulting from combining Emptys and
% Accum.  A list of empty(N,Node,Tag,SVs,Iqs,Dtrs,RuleName) terms is minimal 
% iff no term on the list subsumes any other term.
% ------------------------------------------------------------------------------
minimise_emptys([],MinimalEmptys,MinimalEmptys).
minimise_emptys([BE|BasicEmptys],Accum,MinimalEmptys) :-
  minimise_emptys_act(Accum,BE,BasicEmptys,NewAccum,NewAccum,MinimalEmptys).

minimise_emptys_act([],B,BsRest,NewAccum,[B],MEs) :-
  minimise_emptys(BsRest,NewAccum,MEs).
minimise_emptys_act([A|AsRest],B,BsRest,NewAccum,NARest,MEs) :-
  arg(3,A,AFS),
  arg(3,B,BFS),
  empty_avl(H),
  empty_avl(K),
  frozen_term(AFS,AFrozen),
  frozen_term(BFS,BFrozen),
  filter_iqs(AFrozen,AIqs,_),
  filter_iqs(BFrozen,BIqs,_),
  subsume(s(AFS,BFS,bot,sdone),<,>,LReln,RReln,H,K,AIqs,BIqs),
  me_subsume_act(LReln,RReln,A,B,AsRest,BsRest,NewAccum,NARest,MEs).

me_subsume_act(<,_,A,_,AsRest,BsRest,NewAccum,[A|AsRest],MEs) :-
  nl,write('EFD-closure discarded a subsumed empty category'),
  minimise_emptys(BsRest,NewAccum,MEs).
me_subsume_act(#,>,_,B,AsRest,BsRest,NewAccum,NARest,MEs) :-
  nl,write('EFD-closure discarded a subsumed empty category'),  
  minimise_emptys_act(AsRest,B,BsRest,NewAccum,NARest,MEs).
me_subsume_act(#,#,A,B,AsRest,BsRest,NewAccum,[A|NARest],MEs) :-
  minimise_emptys_act(AsRest,B,BsRest,NewAccum,NARest,MEs).

% ------------------------------------------------------------------------------
% close_emptys(+Emptys:<empty>s,-ClosedEmptys:<empty>s,-ClosedRules:<rule>s)
% ------------------------------------------------------------------------------
% Close Emptys under the rules in the database to obtain ClosedEmptys.  In
%  the process, we also close those rules closed under empty category prefixes,
%  to obtain ClosedRules.
% ------------------------------------------------------------------------------
close_emptys(Emptys,ClosedEmptys,ClosedRules) :-
  findall(alec_rule(RuleName,Dtrs,_,Mother,true,PrevDtrs,PrevDtrs,DtrStore,DtrStore), % SP4: true = Residue
        (current_predicate(rule,(_ rule _)),
        (RuleName rule Mother ===> Dtrs)),
        Rules),
  efd_iterate(Emptys,Rules,[],[],[],ClosedEmptys,ClosedRules).

% ------------------------------------------------------------------------------
% efd_iterate(+Es:<empty>s,+Rs:<rule>s,+NRs:<rule>s,+EAs:<empty>s,+RAs:<rule>s,
%             -ClosedEmptys:<empty>s,-ClosedRules:<rule>s)
% ------------------------------------------------------------------------------
% The Empty-First-Daughter closure algorithm closes a given collection of
%  base empty categories and base extended PS rules breadth-first under 
%  prefixes of empty category daughters.  This has the following benefits:
%  1) it corrects a long-standing problem in ALE with combining empty 
%     categories.  Because any permutation of empty categories can, in
%     principle, be combined to form a new empty category, ALE cannot perform
%     depth-first closure under a leftmost empty category as it can with 
%     normal edges;
%  2) it corrects a problem that non-ISO-compatible Prologs, including SICStus 
%     Prolog, have with asserted predicates that results in empty category
%     leftmost daughters not being able to combine with their own outputs;
%  3) it allows parsers to establish a precondition that rules only need to
%     be closed with non-empty leftmost daughters at run-time.  As a result,
%     when a new mother category is created and closed under rules as the
%     leftmost daughter, it cannot combine with other edges created with the
%     same left node.  This allows ALE, at each step in its right-to-left pass
%     throught the string, to copy all of the edges in the internal database
%     back onto the heap before they can be used again, and thus reduces
%     edge copying to a constant 2/edge for non-empty edges (edges with 
%     different left and right nodes).  Keeping a copy of the chart on the
%     heap also allows for more sophisticated indexing strategies that would
%     otherwise be overwhelmed by the cost of copying the edge before matching.
%
% Let Es,Rs,NEs,NRs,EAs, and RAs be lists.  Initialise Es to the base empty 
%  categories, and Rs to the base rules, and the others to []
% 
% loop:
% while Es =/= [] do
%   for each E in Es do
%     for each R in Rs do
%       match E against the leftmost unmatched category description of R
%       if it does not match, continue
%       if the leftmost category was the rightmost (unary rule), then
%         add the new empty category to NEs
%       otherwise, add the new rule (with leftmost category marked as matched)
%         to NRs
%     od
%   od
%   EAs := Es + EAs
%   Rs := Rs + RAs, RAs := []
%   Es := NEs, NEs := []
% od
% if NRs = [], 
%  then end: EAs are the closed empty cats, Rs are the closed rules
%  else
%    Es := EAs, EAs := []
%    RAs := Rs, Rs := NRs, NRs := []
%    go to loop
%
% This algorithm terminates for exactly those grammars in which bottom-up
%  parsing over empty categories terminates, i.e., it is no worse than pure
%  bottom-up parsing.
% ------------------------------------------------------------------------------
efd_iterate([],Rules,NewRules,EmptyAccum,_RuleAccum,  % RuleAccum is []
            ClosedEmptys,ClosedRules) :-
  !,
  (NewRules == []
  -> ClosedEmptys = EmptyAccum, ClosedRules = Rules
   ; efd_iterate(EmptyAccum,NewRules,[],[],Rules,ClosedEmptys,ClosedRules)
  ).
efd_iterate(Emptys,Rules,NewRules,EmptyAccum,RuleAccum,
            ClosedEmptys,ClosedRules) :-
  apply_once(Emptys,Rules,NewEmptysandRules),
  split_emptys_rules(NewEmptysandRules,NewRules,NewRules1,NewEmptys),
  append(Emptys,EmptyAccum,EmptyAccum1),
  append(Rules,RuleAccum,Rules1),
  efd_iterate(NewEmptys,Rules1,NewRules1,EmptyAccum1,[],
              ClosedEmptys,ClosedRules).

% ------------------------------------------------------------------------------
% apply_once(+Es:<empty>s,+Rs:<empty>s,-NEsorRs:<empty_or_rule>s)
% ------------------------------------------------------------------------------
% the two for-loops of the EFD-closure algorithm above.
% ------------------------------------------------------------------------------
apply_once(Emptys,Rules,NewEmptysandRules) :-
  findall(EmptyorRule,
          (member(Empty,Emptys),
           arg(4,Empty,EResidueSeq), call(EResidueSeq), %SP4: reattach FS's attributes and suspensions
           member(alec_rule(RuleName,Dtrs,Node,Mother,RResidueSeq,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest),
                  Rules),
           call(RResidueSeq),

%           arg(1,Empty,N),	% DEBUG
	      
	   match_cat_to_next_cat(Dtrs,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest,
                                 Empty,EmptyorRule,Node)

%                                  write(user_error,'matched '),write(user_error,N),
%				  write(user_error,' to '),write(user_error,RuleName),
%				  nl(user_error),flush_output(user_error),
%	                          ( EmptyorRule = empty(NewN,_,_,_,_) -> write(user_error,'new empty from rule '), write(user_error,RuleName),write(user_error,':'),write(user_error,NewN),
%				      nl(user_error), flush_output(user_error)
%				  ; EmptyorRule = alec_rule(_,_,_,_,_,_) -> write(user_error,'new rule'),
%				    nl(user_error), flush_output(user_error)
%				  ; true
%				  )
	  ),
          NewEmptysandRules).

% ------------------------------------------------------------------------------
% split_emptys_rules(+NEsorRs:<empty_or_rule>s,+NRsOld:<rule>s,
%                    -NRsNew:<rule>s,-NEsNew:<empty>s)
% ------------------------------------------------------------------------------
% classifies the results of apply_once/3 as empty cats or rules, and adds them
% to NEs or NRs, respectively.
% ------------------------------------------------------------------------------

split_emptys_rules([],NewRulesRest,NewRulesRest,[]).
split_emptys_rules([Item|Items],NewRulesRest,NewRules,NewEmptys) :-
  functor(Item,Functor,_),
  (Functor == alec_rule
  -> NewRules = [Item|NewRulesMid],
%     nl(user_error),write(user_error,'EFD-closure generated a partial rule'),  % DEBUG
%      flush_output(user_error),
     split_emptys_rules(Items,NewRulesRest,NewRulesMid,NewEmptys)
   ; % Functor == empty,
     NewEmptys = [Item|NewEmptysMid],
%     nl(user_error),write(user_error,'EFD-closure generated an empty category'),  % DEBUG
%      flush_output(user_error),
     split_emptys_rules(Items,NewRulesRest,NewRules,NewEmptysMid)
  ).

% ------------------------------------------------------------------------------
% match_cat_to_next_cat(+Dtrs:<dtr>s,+Mother:<desc>,+RuleName:<atom>,
%                       +PrevDtrs:<empty/2>s,-PrevDtrsRest:<var_empty/2>s,
%                       +RuleIqs:<ineq>s,+Empty:<empty>,
%                       -EmptyorRule:<empty_or_rule>,-Node:<var_int>)
% ------------------------------------------------------------------------------
% interpretive matching of empty category to leftmost category description
% plus all procedural attachments up to the next category description.
% ------------------------------------------------------------------------------
match_cat_to_next_cat((cat> Dtr,Rest),Mother,RuleName,PrevDtrs,
                      [empty(N,Node)|PrevDtrsMid],DtrStore,DtrStoreMid,
                      empty(N,Node,FS,_,_,_),EmptyorRule,Node) :-
  deref(FS,TFS,Type,AttPos),	
  add_to(Dtr,FS,Type,TFS,AttPos,bot),
  DtrStoreMid = [FS|DtrStoreMid2],
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,
                    DtrStoreMid2,EmptyorRule,Node).
match_cat_to_next_cat((cat> Dtr),Mother,RuleName,PrevDtrs,[empty(N,Node)],
                      DtrStoreList,DtrStoreMid,empty(N,Node,FS,_,_,_),
                      empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),
                      Node) :-
  deref(FS,TFS,Type,AttPos),
  add_to(Dtr,FS,Type,TFS,AttPos,bot),
  add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
  DtrStoreMid = [FS],
  list_to_store(DtrStoreList,DtrStore),
  apply_forall_rule(DtrStore,FSOut,RuleName),
  residuate_term(FSOut,ResOut),
  gen_emptynum(NewN).
match_cat_to_next_cat((sem_head> Dtr,Rest),Mother,RuleName,PrevDtrs,
                      [empty(N,Node)|PrevDtrsMid],DtrStore,DtrStoreMid,
                      empty(N,Node,FS,_,_,_),EmptyorRule,Node) :-
  deref(FS,TFS,Type,AttPos),
  add_to(Dtr,FS,Type,TFS,AttPos,bot),
  DtrStoreMid = [FS|DtrStoreMid2],
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,
                    DtrStore,DtrStoreMid2,EmptyorRule,Node).
match_cat_to_next_cat((sem_head> Dtr),Mother,RuleName,PrevDtrs,[empty(N,Node)],
                      empty(N,Node,FS,_,_,_),DtrStoreList,DtrStoreMid,
                      empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),
                      Node) :-
  deref(FS,TFS,Type,AttPos),
  add_to(Dtr,FS,Type,TFS,AttPos,bot),
  add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
  DtrStoreMid = [FS],
  list_to_store(DtrStoreList,DtrStore),
  apply_forall_rule(DtrStore,FSOut,RuleName),
  residuate_term(FSOut,ResOut),
  gen_emptynum(NewN).
match_cat_to_next_cat((cats> Dtrs,Rest),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                      DtrStore,DtrStoreMid,Empty,EmptyorRule,Node) :-
  add_to(Dtrs,DtrsFS,bot,tfs(bot,_),DtrsFS,bot),
  deref(DtrsFS,_,DtrsType,_),
  (sub_type(ne_list,DtrsType)
  -> clause(fcolour(hd,HdPos,_),true),
     arg(HdPos,DtrsFS,HdFS),  % no need to fill this - intro restr should be bot
     Empty = empty(N,Node,HdFS,_,_,_),
     DtrStoreMid = [HdFS|DtrStoreRest],
     clause(fcolour(tl,TlPos,_),true),
     arg(TlPos,DtrsFS,TlFS),  % no need to fill this - list and bot are both invalid.
     deref(TlFS,_,TlType,_),
     ( sub_type(ne_list,TlType) -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
     	                           EmptyorRule = alec_rule(RuleName,(remainder(TlFS),Rest),Node,Mother,
							   ResidueSeq,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest),
                                   residuate_term([Mother,TlFS|Rest],ResidueSeq)
     ; sub_type(e_list,TlType) -> PrevDtrsMid = [empty(N,Node)|PrevDtrsMid2],
	                          match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid2,
						    DtrStore,DtrStoreRest,EmptyorRule,Node)
     ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),  % KNOWN BUG: may report bot
                  write(' is not a valid argument (e_list or ne_list)')))    %  when real type is list.
     )
  ; sub_type(e_list,DtrsType) -> match_cat_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,
						       DtrStore,DtrStoreMid,Empty,EmptyorRule,Node)
  ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
               write(' is not a valid argument (e_list or ne_list)')))
  ).
match_cat_to_next_cat((cats> Dtrs),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                      DtrStoreList,DtrStoreMid,empty(N,Node,FS,_,_,_),EmptyorRule,
                      Node) :-
  add_to(Dtrs,DtrsFS,bot,tfs(bot,_),DtrsFS,bot),
  deref(DtrsFS,_,DtrsType,_),
  (sub_type(ne_list,DtrsType)
  -> clause(fcolour(hd,HdPos,_),true),
     clause(fcolour(tl,TlPos,_),true),
     arg(HdPos,DtrsFS,FS),    % no need to fill this - intro restr is bot.
     arg(TlPos,DtrsFS,TlFS),  % no need to fill this - list and bot are both invalid.
     deref(TlFS,_,TlType,_),
     ( sub_type(ne_list,TlType) -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
    	                           DtrStoreMid = [FS|DtrStoreRest],
	                           EmptyorRule = alec_rule(RuleName,remainder(TlFS),Node,Mother,ResidueSeq,
		 					   PrevDtrs,PrevDtrsRest,DtrStoreList,DtrStoreRest),
                                   residuate_term([Mother|TlFS],ResidueSeq)
     ; sub_type(e_list,TlType) -> add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
    	                          DtrStoreMid = [FS],
                                  list_to_store(DtrStoreList,DtrStore),
	                          apply_forall_rule(DtrStore,FSOut,RuleName),
	                          PrevDtrsMid = [empty(N,Node)],
    	                          EmptyorRule = empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),
                                  residuate_term(FSOut,ResOut),
	                          gen_emptynum(NewN)
     ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),  % KNOWN BUG: may report bot,
                  write(' is not a valid argument (e_list or ne_list)')))    %  when real type is list.
     )
  ; sub_type(e_list,DtrsType)
     -> error_msg((nl,write('error: rule '),write(RuleName),
                   write(' has no daughters')))
      ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
                   write(' is not a valid argument (e_list or ne_list)')))
  ).
match_cat_to_next_cat((remainder(RFS),Rest),Mother,RuleName,PrevDtrs,
                      PrevDtrsMid,DtrStore,DtrStoreMid,empty(N,Node,FS,_,_,_),
                      EmptyorRule,Node) :-
%	dpp_fs(RFS), flush_output, % DEBUG
  clause(fcolour(hd,HdPos,_),true),
  clause(fcolour(tl,TlPos,_),true),
  arg(HdPos,RFS,FS),   % no need to fill this - intro restr is bot
  DtrStoreMid = [FS|DtrStoreRest],
  arg(TlPos,RFS,TlFS), % no need to fill this - list and bot are both invalid.
  deref(TlFS,_,TlType,_),
  (sub_type(ne_list,TlType)
  -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
     EmptyorRule = alec_rule(RuleName,(remainder(TlFS),Rest),Node,Mother,ResidueSeq,
                             PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest),
     residuate_term([Mother,TlFS|Rest],ResidueSeq)
   ; sub_type(e_list,TlType) -> PrevDtrsMid = [empty(N,Node)|PrevDtrsMid2],
                                match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid2,DtrStore,
						  DtrStoreRest,EmptyorRule,Node)
   ; error_msg((nl,write('error: cats> value with sort, '),write(TlType), % KNOWN BUG: may report bot, when
                write(' is not a valid argument (e_list or ne_list)')))   %  real type is list.
  ).
match_cat_to_next_cat(remainder(RFS),Mother,RuleName,PrevDtrs,PrevDtrsMid,
                      DtrStoreList,DtrStoreMid,empty(N,Node,FS,_,_,_),EmptyorRule,
                      Node) :-
  clause(fcolour(hd,HdPos,_),true),
  clause(fcolour(tl,TlPos,_),true),
  arg(HdPos,RFS,FS),    % no need to fill this - intro restr is bot
  arg(TlPos,RFS,TlFS),  % no need to fill this - list and bot are both invalid.
  deref(TlFS,_,TlType,_),
  ( sub_type(ne_list,TlType) -> PrevDtrsMid = [empty(N,Node)|PrevDtrsRest],
                                DtrStoreMid = [FS|DtrStoreRest],
                                EmptyorRule = alec_rule(RuleName,remainder(TlFS),Node,
	 					        Mother,ResidueSeq,PrevDtrs,PrevDtrsRest,
							DtrStoreList,DtrStoreRest),
                                residuate_term([Mother|TlFS],ResidueSeq)
  ; sub_type(e_list,TlType) -> add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
                               DtrStoreMid = [FS],
                               list_to_store(DtrStoreList,DtrStore),
                               apply_forall_rule(DtrStore,FSOut,RuleName),
                               PrevDtrsMid = [empty(N,Node)],
                               EmptyorRule = empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),
                               residuate_term(FSOut,ResOut),
                               gen_emptynum(NewN)
  ; error_msg((nl,write('error: cats> value with sort, '),write(TlType),  % KNOWN BUG: may report bot, when
               write(' is not a valid argument (e_list or ne_list)')))    %  real type is list.
  ).
match_cat_to_next_cat((goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,
                      PrevDtrsMid,DtrStore,DtrStoreMid,Empty,EmptyorRule,Node) :-
  query_goal(GoalDesc),
%  call(Goal), --- query_goal/1 now calls its Goal
  match_cat_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreMid,
                        Empty,EmptyorRule,Node).
match_cat_to_next_cat((goal> _),_,RuleName,_,_,_,_,_,_,_) :-
  error_msg((nl,write('error: rule '),write(RuleName),
             write(' has no daughters'))).
match_cat_to_next_cat((sem_goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,
                      PrevDtrsMid,DtrStore,DtrStoreMid,Empty,EmptyorRule,Node) :-
  query_goal(GoalDesc),
%  call(Goal), --- query_goal/1 now calls its Goal
  match_cat_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreMid,
                        Empty,EmptyorRule,Node).
match_cat_to_next_cat((sem_goal> _),_,RuleName,_,_,_,_,_,_,_) :-
  error_msg((nl,write('error: rule '),write(RuleName),
             write(' has no daughters'))).

% ------------------------------------------------------------------------------
% match_to_next_cat(+Dtrs:<dtr>s,+Mother:<desc>,+RuleName:<atom>,
%                   +PrevDtrs:<empty/2>s,-PrevDtrsRest:<var_empty/2>s,
%                   +RuleIqs:<ineq>s,-EmptyorRule:<empty_or_rule>,
%                   -Node:<var_int>)
% ------------------------------------------------------------------------------
% Same as match_cat_to_next_cat/8 but leftmost category has already been
% matched.  Now interpret all procedural attachments until next category
% is encountered or no daughters remain.
% ------------------------------------------------------------------------------

match_to_next_cat((cat> Dtr,Rest),Mother,RuleName,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest,
                  alec_rule(RuleName,(cat> Dtr,Rest),Node,Mother,ResidueSeq,PrevDtrs,
                            PrevDtrsRest,DtrStore,DtrStoreRest),
                  Node) :- residuate_term([Mother,Dtr|Rest],ResidueSeq).
match_to_next_cat((cat> Dtr),Mother,RuleName,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest,
                  alec_rule(RuleName,(cat> Dtr),Node,Mother,ResidueSeq,PrevDtrs,PrevDtrsRest,DtrStore,
			    DtrStoreRest),
                  Node) :- residuate_term([Mother|Dtr],ResidueSeq).
match_to_next_cat((sem_head> Dtr,Rest),Mother,RuleName,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest,
                  alec_rule(RuleName,(sem_head> Dtr,Rest),Node,Mother,ResidueSeq,PrevDtrs,
                            PrevDtrsRest,DtrStore,DtrStoreRest),
                  Node) :- residuate_term([Mother,Dtr|Rest],ResidueSeq).
match_to_next_cat((sem_head> Dtr),Mother,RuleName,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest,
                  alec_rule(RuleName,(sem_head> Dtr),Node,Mother,ResidueSeq,PrevDtrs,PrevDtrsRest,
			    DtrStore,DtrStoreRest),
                  Node) :- residuate_term([Mother|Dtr],ResidueSeq).
match_to_next_cat((cats> Dtrs,Rest),Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest,
                  EmptyorRule,Node) :-
  add_to(Dtrs,DtrsFS,bot,tfs(bot,_),DtrsFS,bot),
  deref(DtrsFS,_,DtrsType,_),
  ( sub_type(ne_list,DtrsType) -> EmptyorRule = alec_rule(RuleName,(remainder(DtrsFS),Rest),Node,Mother,
							  ResidueSeq,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest),
                                  residuate_term([Mother,DtrsFS|Rest],ResidueSeq)
  ; sub_type(e_list,DtrsType) -> match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,
						   DtrStoreRest,EmptyorRule,Node)
  ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
               write(' is not a valid argument (e_list or ne_list)')))
  ).
match_to_next_cat((cats> Dtrs),Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStoreList,DtrStoreRest,
                  EmptyorRule,Node) :-
  add_to(Dtrs,DtrsFS,bot,tfs(bot,_),DtrsFS,bot),
  deref(DtrsFS,_,DtrsType,_),
  ( sub_type(ne_list,DtrsType) -> EmptyorRule = alec_rule(RuleName,remainder(DtrsFS),Node,Mother,ResidueSeq,
							  PrevDtrs,PrevDtrsMid,DtrStoreList,DtrStoreRest),
                                  residuate_term([Mother|DtrsFS],ResidueSeq)
  ; sub_type(e_list,DtrsType) -> add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
                                 DtrStoreRest = [],
                                 list_to_store(DtrStoreList,DtrStore),
                                 apply_forall_rule(DtrStore,FSOut,RuleName),
                                 PrevDtrsMid = [],
                                 EmptyorRule = empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),
                                 residuate_term(FSOut,ResOut),
                                 gen_emptynum(NewN)
  ; error_msg((nl,write('error: cats> value with sort, '),write(DtrsType),
               write(' is not a valid argument (e_list or ne_list)')))
  ).
match_to_next_cat((goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest,
                  EmptyorRule,Node) :-
  query_goal(GoalDesc),
%  call(Goal), --- query_goal/1 now calls its Goal
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest,EmptyorRule,Node).
match_to_next_cat((goal> GoalDesc),Mother,RuleName,PrevDtrs,[],DtrStoreList,DtrStoreRest,
                  empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),
                  Node) :-
  query_goal(GoalDesc),
%  call(Goal), --- query_goal/1 now calls its Goal
  add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
  DtrStoreRest = [],
  list_to_store(DtrStoreList,DtrStore),
  apply_forall_rule(DtrStore,FSOut,RuleName),
  residuate_term(FSOut,ResOut),
  gen_emptynum(NewN).
match_to_next_cat((sem_goal> GoalDesc,Rest),Mother,RuleName,PrevDtrs,
                  PrevDtrsMid,DtrStore,DtrStoreRest,EmptyorRule,Node) :-
  query_goal(GoalDesc),
%  call(Goal), --- query_goal/1 now calls its Goal
  match_to_next_cat(Rest,Mother,RuleName,PrevDtrs,PrevDtrsMid,DtrStore,DtrStoreRest,EmptyorRule,Node).
match_to_next_cat((sem_goal> GoalDesc),Mother,RuleName,PrevDtrs,[],DtrStoreList,DtrStoreRest,
                  empty(NewN,Node,FSOut,ResOut,PrevDtrs,RuleName),Node) :-
  query_goal(GoalDesc),
%  call(Goal), --- query_goal/1 now calls its Goal
  add_to(Mother,FSOut,bot,tfs(bot,_),FSOut,bot),
  DtrStoreRest = [],
  list_to_store(DtrStoreList,DtrStore),
  apply_forall_rule(DtrStore,FSOut,RuleName),
  residuate_term(FSOut,ResOut),
  gen_emptynum(NewN).

% ------------------------------------------------------------------------------
% name_rules(+Rules:<rule>s,-Rules:<rule>s)
% ------------------------------------------------------------------------------
% Disambiguate rule names for rule indexing.
% ------------------------------------------------------------------------------
name_rules(RulesIn,RulesOut) :-
  findall(Name-Rule,(member(Rule,RulesIn),arg(1,Rule,Name)),KeyedRules),
  keysort(KeyedRules,SortedKeyedRules),
  name_rules_act(SortedKeyedRules,RulesOut).

name_rules_act([],[]).
name_rules_act([Key-Rule|SortedKeyedRules],RulesOut) :-
  name_rules_act2(SortedKeyedRules,Key,Rule,RulesOut).

name_rules_act2([],_,Rule,[Rule]).
name_rules_act2([Key2-Rule2|SortedKeyedRules],Key1,Rule1,RulesOut) :-
  Key2 == Key1 -> RulesOut = [NewRule1,NewRule2|RulesOutRest],
                  tag_rule_name(Key1,0,NewKey1),
                  tag_rule_name(Key2,1,NewKey2),
		  map_rule_name(Rule1,NewKey1,NewRule1),
		  map_rule_name(Rule2,NewKey2,NewRule2),
		  name_rules_act3(SortedKeyedRules,Key1,2,RulesOutRest)
  ; RulesOut = [Rule1|RulesOutRest],
    name_rules_act2(SortedKeyedRules,Key2,Rule2,RulesOutRest).

name_rules_act3([],_,_,[]).
name_rules_act3([Key2-Rule|SortedKeyedRules],Key1,N,RulesOut) :-
  Key2 == Key1 -> RulesOut = [NewRule|RulesOutRest],
                  tag_rule_name(Key2,N,NewKey2),
                  map_rule_name(Rule,NewKey2,NewRule),
		  NewN is N + 1,
		  name_rules_act3(SortedKeyedRules,Key1,NewN,RulesOutRest)
  ; name_rules_act2(SortedKeyedRules,Key2,Rule,RulesOut).

tag_rule_name(Key,N,NewKey) :-
  Key =.. [KeyFun|KeyArgs],
  name(KeyFun,KeyName),
  name(N,NName),
  append(KeyName,[47,47|NName],NewKeyName),  % add "//N"
  name(NewKeyFun,NewKeyName),
  NewKey =.. [NewKeyFun|KeyArgs].

map_rule_name(alec_rule(_,Daughters,Left,Mother,ResidueSeq,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest),
	      NewName,
	      alec_rule(NewName,Daughters,Left,Mother,ResidueSeq,PrevDtrs,PrevDtrsRest,DtrStore,DtrStoreRest)).

% ------------------------------------------------------------------------------
% rule(Tag:<var_tag>, SVs:<svs>, Iqs:<ineq>s, Left:<int>, Right:<int>,
%      N:<int>,Chart:<chart>)                                              mh(0)
% ------------------------------------------------------------------------------
% adds the result of any rule of which Tag-SVs from Left to Right
% might be the first element and the rest of the categories are in the chart
% ------------------------------------------------------------------------------
rule(_,_,_,_,_,_) if_h [fail] :-
  \+ clause(alec_rule(_,_,_,_,_,_,_,_,_),true).
rule(RuleName,FS,Left,Right,N,Chart) if_h % [nl(user_error),write(user_error,RuleName),  % DEBUG
                                          % nl(user_error),flush_output(user_error)|
                                          SubGoals :-
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(MFSIn),
  clause(alec_rule(RuleName,Daughters,Left,Mother,ResidueSeq,PrevDtrs,PrevDtrsRest,CompiledDtrStore,[]),true),
  call(ResidueSeq), % HACK: SP4: reattach the attributes so that the compiler can see which vars are bound to an FS
%  nl(user_error),write(user_error,RuleName),nl(user_error),flush_output(user_error), % DEBUG
  compile_dtrs(Daughters,FS,Left,Right,N,SubGoalsMid,[],PrevDtrs,
               PrevDtrsRest,Mother,RuleName,Chart,serial,VarsIn,_,FSPal,FSsIn,
               FSsOut,MFSIn,_,[CompiledDtrStore|ArgStore],ArgStore,[]),
  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsMid,rule),
  assert(rule_compiled(RuleName)).

% ------------------------------------------------------------------------------
% compile_dtrs(Dtrs,Tag,SVs,Iqs,Left,Right,N,PGoals,PGoalsRest,Dtrs,DtrsRest,
%              Mother,RuleName,Chart,CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% compiles description Dtrs to apply rule to first category Tag-SVs,
% at position Left-Right in chart, producing a list of Prolog goals
% diff list PGoals-PGoalsRest;  Mother is result produced
% ------------------------------------------------------------------------------
compile_dtrs((cat> Dtr,Rest),FS,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),  % could refine bot mode by analysing lexicon and PS rule mothers
  compile_desc(Dtr,FS,PGoals,PGoalsMid,M,Context,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,
	       ModeIn,_,MFSMid,MFSMid2,NVs),
  DtrsMid = [N|DtrsRest],
  add_to_store(DtrStoreMid,FS,DtrStoreRest),
  term_variables(Dtr,DtrVars),
  ord_union(DtrVars,PriorVs,RestPriorVs),
  compile_dtrs_rest(Rest,Left,Right,PGoalsMid,PGoalsRest,Mother,
                    Dtrs,DtrsRest,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut,MFSMid2,MFSOut,DtrStore,DtrStoreRest,RestPriorVs).
% 5/1/96 Octav -- added a clause for 'sem_head>' label
% (sem_head> daughters behave just like cat> daughters during parsing)
compile_dtrs((sem_head> Dtr,Rest),FS,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid), % could refine bot mode by analysing lexicon and PS rule mothers
  compile_desc(Dtr,FS,PGoals,PGoalsMid,M,Context,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,
	       ModeIn,_,MFSMid,MFSMid2,NVs),
  DtrsMid = [N|DtrsRest],
  add_to_store(DtrStoreMid,FS,DtrStoreRest),
  term_variables(Dtr,DtrVars),
  ord_union(DtrVars,PriorVs,RestPriorVs),
  compile_dtrs_rest(Rest,Left,Right,PGoalsMid,PGoalsRest,Mother,
                    Dtrs,DtrsRest,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut,MFSMid2,MFSOut,DtrStore,DtrStoreRest,RestPriorVs).
compile_dtrs((cats> Dtrs,Rest),FSIn,Left,Right,N,PGoals,PGoalsRest,
             PrevDtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs) :-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  empty_avl(EAssoc),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),
  assert_mode(type(max(list)),M,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Dtrs,EAssoc,ImplicitVars,PGoals,PGoalsMid2,M,Context,VarsIn,VarsMid,
		   FSPal,FSsIn,FSsMid,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs),
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars  
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar2),
  ( ale_lists_defined -> clause(fcolour(hd,HdPos,_),true),
                         clause(fcolour(tl,TlPos,_),true)
  ; raise_exception(cats_no_lists(RuleName,Dtrs))
  ),
  PGoalsMid3 = [deref(FSVar2,_,Sort,_),
		( sub_type(e_list,Sort) -> PGoal_elist, DtrStoreMid = DtrStore_elist
		; (match_list(Sort,FSVar2,HdPos,TlPos,FSIn,Right,N,DtrsMid,DtrsRest,
			      Chart,NextRight,DtrStoreMid,DtrStore_nelist), % a_ correctly causes error
		   PGoal_nelist))|PGoalsRest],
  term_variables(Dtrs,DtrsVars),
  ord_union(DtrsVars,PriorVs,RestPriorVs),
  compile_dtrs_rest(Rest,Left,NextRight,PGoalsMid_nelist,[],
               Mother,PrevDtrs,DtrsRest,RuleName,Chart,disj,VarsMid,
               Vars_nelist,FSPal,FSsMid,FSs_nelist,MFSMid3,MFS_nelist,
               DtrStore,DtrStore_nelist,RestPriorVs),
  compile_dtrs(Rest,FSIn,Left,Right,N,PGoalsMid_elist,[],
               PrevDtrs,DtrsMid,Mother,RuleName,Chart,disj,VarsMid,
               Vars_elist,FSPal,FSsMid,FSs_elist,MFSMid3,MFS_elist,DtrStore,DtrStore_elist,RestPriorVs),
  goal_list_to_seq(PGoalsMid_nelist,PGoal_nelist),
  goal_list_to_seq(PGoalsMid_elist,PGoal_elist),
  mfs_merge(MFSMid,MFS_nelist,MFS_elist,Context,MFSMid2),
  vars_merge(VarsMid,Vars_nelist,Vars_elist,Context,VarsOut,MFSMid2,MFSMid3),
  fss_merge(FSsMid,FSs_nelist,FSs_elist,FSsOut,MFSMid3,MFSOut).
compile_dtrs((remainder(RFS),Rest),FS,Left,Right,N,PGoals,
             PGoalsRest,Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs) :-
  !,PGoals = [arg(Arg,FSPal,RVar),
	      deref(RVar,_,Sort,_),
              match_list(Sort,RVar,HdPos,TlPos,FS,Right,N,DtrsMid,DtrsRest,Chart,NextRight,
			 DtrStoreMid,DtrStoreRest)|PGoalsMid],
  clause(fcolour(hd,HdPos,_),true),
  clause(fcolour(tl,TlPos,_),true),
  fs_to_mode(RFS,RFSMode,MFSIn,MFSMid),
  avl_store(RFS,FSsIn,fsmode(seen,RFSMode,RVar,Arg),FSsMid),
  ord_add_element(PriorVs,RVar,RestPriorVs),
  compile_dtrs_rest(Rest,Left,NextRight,PGoalsMid,PGoalsRest,Mother,
                    Dtrs,DtrsRest,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,
                    FSsMid,FSsOut,MFSMid,MFSOut,DtrStore,DtrStoreRest,RestPriorVs).
compile_dtrs((goal> Goal,Rest),FS,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),  % do we need to register FS here (with track_fs/bind_fs) in case Goal mentions it?
  prior_cont_vars(Rest,ContVs),
  prior_cont_vars(Goal,GoalVars),
  ord_union(GoalVars,PriorVs,RestPriorVs),
  compile_body(Goal,PGoals,PGoalsMid,Context,VarsIn,VarsMid,
               FSPal,FSsIn,FSsMid,MFSIn,MFSMid,NVs,PriorVs,ContVs),
  compile_dtrs(Rest,FS,Left,Right,N,PGoalsMid,PGoalsRest,
               Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
               FSsMid,FSsOut,MFSMid,MFSOut,DtrStore,DtrStoreMid,RestPriorVs).
% 6/1/97 Octav -- added a clause for 'sem_goal>' label
% (sem_goal> daughters behave just like goal> daughters during parsing)
compile_dtrs((sem_goal> Goal,Rest),FS,Left,Right,N,PGoals,
             PGoalsRest,Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  prior_cont_vars(Rest,ContVs),
  prior_cont_vars(Goal,GoalVars),
  ord_union(GoalVars,PriorVs,RestPriorVs),
  compile_body(Goal,PGoals,PGoalsMid,Context,VarsIn,VarsMid,FSPal,
               FSsIn,FSsMid,MFSIn,MFSMid,NVs,PriorVs,ContVs),
  compile_dtrs(Rest,FS,Left,Right,N,PGoalsMid,PGoalsRest,
               Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
               FSsMid,FSsOut,MFSMid,MFSOut,DtrStore,DtrStoreMid,RestPriorVs).
compile_dtrs((cat> Dtr),FSIn,Left,Right,N,PGoals,PGoalsRest,Dtrs,
             [N],Mother,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,
	     DtrStore,DtrStoreMid,_):-
  !, empty_avl(NVs),
  empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid), % could refine bot mode by analysing lexicon and PS rule
				                % mothers
  compile_desc(Dtr,FSIn,PGoals,PGoalsMid,M,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSMid,MFSMid2,NVs),
  add_to_store(DtrStoreMid,FSIn),
  genindex(M2),
  initialise_mode(M2,EMode,ModeIn2,MFSMid2,MFSMid3),
  empty_avl(EAssoc),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,M2,Context,VarsMid,
		   VarsOut,FSPal,FSsMid,FSsMid2,ModeIn2,_ModeOut2,MFSMid3,MFSMid4,NVs),
  % should be using ModeOut2 instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar),
  generate_apply_forall_rule(DtrStore,FSVar,RuleName,FSPal,FSsMid2,FSsOut,MFSMid4,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,Right,FSVar,Dtrs,RuleName,Chart)|PGoalsRest].
	     
% 5/1/96 Octav -- added a clause for 'sem_head>' label
% (behaves the same as cat> during parsing)
compile_dtrs((sem_head> Dtr),FSIn,Left,Right,N,PGoals,PGoalsRest,
	     Dtrs,[N],Mother,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,_):-
  !, empty_avl(NVs),
  empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),
  compile_desc(Dtr,FSIn,PGoals,PGoalsMid,M,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSMid,MFSMid2,NVs),
  add_to_store(DtrStoreMid,FSIn),
  genindex(M2),
  initialise_mode(M2,EMode,ModeIn2,MFSMid2,MFSMid3),
  empty_avl(EAssoc),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,
                   M2,Context,VarsMid,VarsOut,FSPal,FSsMid,FSsMid2,ModeIn2,_ModeOut2,MFSMid3,MFSMid4,NVs),
% don't check inequations after mother since add_edge_deref does that
% should be using ModeOut2 instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar),
  generate_apply_forall_rule(DtrStore,FSVar,RuleName,FSPal,FSsMid2,FSsOut,MFSMid4,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,Right,FSVar,Dtrs,RuleName,Chart)|PGoalsRest].

compile_dtrs((cats> Dtrs),FSIn,Left,Right,N,PGoals,PGoalsRest,
             PrevDtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,
             FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,_) :-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  empty_avl(EAssoc),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),
  assert_mode(type(max(list)),M,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Dtrs,EAssoc,ImplicitVars,PGoals,PGoalsMid2,M,Context,VarsIn,VarsMid,
		   FSPal,FSsIn,FSsMid,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs),
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar3),
  ( ale_lists_defined -> clause(fcolour(hd,HdPos,_),true),
                         clause(fcolour(tl,TlPos,_),true)
  ; raise_exception(cats_no_lists(RuleName,Dtrs))
  ),
  PGoalsMid3 = [deref(FSVar3,_,Sort,_),
		( sub_type(e_list,Sort) -> fail % KNOWN BUG: assumes e_list is maximal
		; (match_list(Sort,FSVar3,HdPos,TlPos,FSIn,Right,N,DtrsMid,[],Chart,NextRight,
			      DtrStoreMid,DtrStoreRest),
		   PGoal)
	        )|PGoalsRest],	%  a_ correctly causes error
  terminate_store(DtrStoreRest),
  genindex(M2),
  initialise_mode(M2,EMode,ModeIn2,MFSMid3,MFSMid4),
  compile_desc_act(Mother,EAssoc,IVars2,PGoalsMid,PGoalsMid4,M2,Context,VarsMid,VarsOut,
		   FSPal,FSsMid,FSsMid2,ModeIn2,_ModeOut2,MFSMid4,MFSMid5,NVs),
% should be using ModeOut2 instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,IVars2,FS2,_,PGoalsMid4,PGoalsMid5),
  FS2 = fs(FSVar2),
  generate_apply_forall_rule(DtrStore,FSVar2,RuleName,FSPal,FSsMid2,FSsOut,MFSMid5,MFSOut,PGoalsMid5,PGoalsMid6),
  PGoalsMid6 = [add_edge(Left,NextRight,FSVar2,PrevDtrs,RuleName,Chart)],
  goal_list_to_seq(PGoalsMid,PGoal).
compile_dtrs(remainder(RFS),FSIn,Left,Right,N,PGoals,PGoalsRest,
             Dtrs,DtrsMid,Mother,RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
             FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,_) :-
  !,PGoals = [arg(Arg,FSPal,RVar),
	      deref(RVar,_,Sort,_),
              match_list(Sort,RVar,HdPos,TlPos,FSIn,Right,N,DtrsMid,[],Chart,NextRight,
			 DtrStoreMid,DtrStoreRest)|PGoalsMid],
  terminate_store(DtrStoreRest),
  clause(fcolour(hd,HdPos,_),true),
  clause(fcolour(tl,TlPos,_),true),
  fs_to_mode(RFS,RFSMode,MFSIn,MFSMid),
  avl_store(RFS,FSsIn,fsmode(seen,RFSMode,RVar,Arg),FSsMid),
  empty_avl(NVs),
  empty_avl(EAssoc),
  empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,M,Context,VarsIn,VarsOut,
		   FSPal,FSsMid,FSsMid2,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs),
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar),
  generate_apply_forall_rule(DtrStore,FSVar,RuleName,FSPal,FSsMid2,FSsOut,MFSMid3,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,NextRight,FSVar,Dtrs,RuleName,Chart)|PGoalsRest].
compile_dtrs(Foo,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_):-
  raise_exception(ale(ill_dtr(Foo))).

% ------------------------------------------------------------------------------
% compile_dtrs_rest(Dtrs,Left,Right,IqsMid,PGoals,PGoalsRest,Mother,
%                   PrevDtrs,DtrsRest,RuleName,CBSafe,VarsIn,VarsOut,FSPal,
%                   FSsIn,FSsOut)
% ------------------------------------------------------------------------------
% same as compile_dtrs, only after first category on RHS of rule is
% found;  thus looks for an edge/7 if a cat> or cats> spec is found
% ------------------------------------------------------------------------------
compile_dtrs_rest((cat> Dtr,Rest),Left,Right,
            [get_edge(Right,Chart,N,NewRight,FS,_,_)|PGoals],
            PGoalsRest,Mother,PrevDtrs,[N|DtrsRest],RuleName,Chart,Context,VarsIn,
            VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid), % could refine bot mode by analysing lexicon and PS rule
				                % mothers
  compile_desc(Dtr,FS,PGoals,PGoalsMid,M,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSMid,MFSMid2,NVs),
  add_to_store(DtrStoreMid,FS,DtrStoreRest),
  term_variables(Dtr,DtrVars),
  ord_union(DtrVars,PriorVs,RestPriorVs),
  compile_dtrs_rest(Rest,Left,NewRight,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut,MFSMid2,MFSOut,DtrStore,DtrStoreRest,RestPriorVs).
% 5/1/96 - Octav -- added a clause for 'sem_head>' label
compile_dtrs_rest((sem_head> Dtr,Rest),Left,Right,
             [get_edge(Right,Chart,N,NewRight,FS,_,_)|PGoals],
             PGoalsRest,Mother,PrevDtrs,[N|DtrsRest],RuleName,Chart,Context,VarsIn,
             VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),
  compile_desc(Dtr,FS,PGoals,PGoalsMid,M,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSMid,MFSMid2,NVs),
  add_to_store(DtrStoreMid,FS,DtrStoreRest),
  term_variables(Dtr,DtrVars),
  ord_union(DtrVars,PriorVs,RestPriorVs),
  compile_dtrs_rest(Rest,Left,NewRight,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut,MFSMid2,MFSOut,DtrStore,DtrStoreRest,RestPriorVs).
compile_dtrs_rest((cats> Dtrs,Rest),Left,Right,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs) :-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  empty_avl(EAssoc),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),
  assert_mode(type(max(list)),M,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Dtrs,EAssoc,ImplicitVars,PGoals,PGoalsMid,M,Context,VarsIn,VarsMid,
		   FSPal,FSsIn,FSsMid,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs),	
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid,PGoalsMid2),
  FS = fs(FSVar),
  PGoalsMid2 = [deref(FSVar,_,Sort,_),	% HACK: could incorporate this deref into match_list_rest/7
		match_list_rest(Sort,FSVar,HdPos,TlPos,Right,NewRight,DtrsRest,DtrsRest2,Chart,
				DtrStoreMid,DtrStoreRest)
	       |PGoalsMid3],	% a_ causes error
  ( ale_lists_defined -> clause(fcolour(hd,HdPos,_),true),
                         clause(fcolour(tl,TlPos,_),true)
  ; raise_exception(cats_no_lists(RuleName,Dtrs))
  ),
  term_variables(Dtrs,DtrsVars),
  ord_union(DtrsVars,PriorVs,RestPriorVs),
  compile_dtrs_rest(Rest,Left,NewRight,PGoalsMid3,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest2,RuleName,Chart,Context,VarsMid,VarsOut,
                    FSPal,FSsMid,FSsOut,MFSMid3,MFSOut,DtrStore,DtrStoreRest,RestPriorVs).
compile_dtrs_rest((goal> Goal,Rest),Left,Right,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  prior_cont_vars(Rest,ContVs),
  prior_cont_vars(Goal,GoalVars),
  ord_union(GoalVars,PriorVs,RestPriorVs),
  compile_body(Goal,PGoals,PGoalsMid,Context,VarsIn,VarsMid,
               FSPal,FSsIn,FSsMid,MFSIn,MFSMid,NVs,PriorVs,ContVs),
  compile_dtrs_rest(Rest,Left,Right,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsMid,VarsOut,
                    FSPal,FSsMid,FSsOut,MFSMid,MFSOut,DtrStore,DtrStoreMid,RestPriorVs).
% 6/1/97 Octav -- added a clause for 'sem_goal>' label
% (sem_goal> daughters behave just like goal> daughters during parsing)
compile_dtrs_rest((sem_goal> Goal,Rest),Left,Right,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsIn,VarsOut,
                  FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,PriorVs):-
  !, empty_avl(NVs),
  prior_cont_vars(Rest,ContVs),
  prior_cont_vars(Goal,GoalVars),
  ord_union(GoalVars,PriorVs,RestPriorVs),
  compile_body(Goal,PGoals,PGoalsMid,Context,VarsIn,VarsMid,FSPal,
               FSsIn,FSsMid,MFSIn,MFSMid,NVs,PriorVs,ContVs),
  compile_dtrs_rest(Rest,Left,Right,PGoalsMid,PGoalsRest,Mother,
                    PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsMid,VarsOut,FSPal,
                    FSsMid,FSsOut,MFSMid,MFSOut,DtrStore,DtrStoreMid,RestPriorVs).
compile_dtrs_rest((cat> Dtr),Left,Right,
              [get_edge(Right,Chart,N,NewRight,EdgeFS,_,_)|PGoals],
              PGoalsRest,Mother,PrevDtrs,[N],RuleName,Chart,Context,VarsIn,VarsOut,
              FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,_):-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),  % could refine bot mode by analysing lexicon and PS rule mothers
  compile_desc(Dtr,EdgeFS,PGoals,PGoalsMid,M,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSMid,MFSMid2,NVs),
  add_to_store(DtrStoreMid,EdgeFS),
  genindex(M2),
  initialise_mode(M2,EMode,ModeIn2,MFSMid2,MFSMid3),
  empty_avl(EAssoc),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,M2,Context,VarsMid,
		   VarsOut,FSPal,FSsMid,FSsMid2,ModeIn2,_ModeOut2,MFSMid3,MFSMid4,NVs),
  % should be using ModeOut2 instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar2),
  generate_apply_forall_rule(DtrStore,FSVar2,RuleName,FSPal,FSsMid2,FSsOut,MFSMid4,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,NewRight,FSVar2,PrevDtrs,RuleName,Chart)|PGoalsRest].

% 5/1/96 - Octav -- added a clause for 'sem_head>' label
compile_dtrs_rest((sem_head> Dtr),Left,Right,
              [get_edge(Right,Chart,N,NewRight,EdgeFS,_,_)|PGoals],
              PGoalsRest,Mother,PrevDtrs,[N],RuleName,Chart,Context,VarsIn,VarsOut,
              FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,_):-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid), % could refine bot mode by analysing lexicon and PS rule mothers
  compile_desc(Dtr,EdgeFS,PGoals,PGoalsMid,M,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSMid,MFSMid2,NVs),
  add_to_store(DtrStoreMid,EdgeFS),
  genindex(M2),
  initialise_mode(M2,EMode,ModeIn2,MFSMid2,MFSMid3),
  empty_avl(EAssoc),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,M2,Context,VarsMid,
		   VarsOut,FSPal,FSsMid,FSsMid2,ModeIn2,_ModeOut2,MFSMid3,MFSMid4,NVs),
% should be using ModeOut2 instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar2),
  generate_apply_forall_rule(DtrStore,FSVar2,RuleName,FSPal,FSsMid2,FSsOut,MFSMid4,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,NewRight,FSVar2,PrevDtrs,RuleName,Chart)|PGoalsRest].

% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest((cats> Dtrs),Left,Right,PGoals,PGoalsRest,
                  Mother,PrevDtrs,DtrsRest,RuleName,Chart,Context,VarsIn,
                  VarsOut,FSPal,FSsIn,FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreMid,_) :-
  !, empty_avl(NVs),
  genindex(M),
  empty_avl(EMode),
  empty_avl(EAssoc),
  initialise_mode(M,EMode,ModeIn,MFSIn,MFSMid),
  assert_mode(type(max(list)),M,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Dtrs,EAssoc,ImplicitVars,PGoals,PGoalsMid2,M,Context,VarsIn,VarsMid,
		   FSPal,FSsIn,FSsMid,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs), % a_ causes error
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar),
  PGoalsMid3 = [deref(FSVar,_,Sort,_),
		match_list_rest(Sort,FSVar,HdPos,TlPos,Right,NewRight,DtrsRest,[],Chart,
				DtrStoreMid,DtrStoreRest)|PGoalsMid],
  terminate_store(DtrStoreRest),
  genindex(M2),
  ( ale_lists_defined -> clause(fcolour(hd,HdPos,_),true),
                         clause(fcolour(tl,TlPos,_),true)
  ; raise_exception(cats_no_lists(RuleName,Dtrs))
  ),
  initialise_mode(M2,EMode,ModeIn2,MFSMid3,MFSMid4),
  compile_desc_act(Mother,EAssoc,IVars2,PGoalsMid,PGoalsMid4,M2,Context,VarsMid,VarsOut,
		   FSPal,FSsMid,FSsMid2,ModeIn2,_ModeOut2,MFSMid4,MFSMid5,NVs),
% should be using ModeOut2 instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,IVars2,FS2,_,PGoalsMid4,PGoalsMid5),
  FS2 = fs(FSVar2),
  generate_apply_forall_rule(DtrStore,FSVar2,RuleName,FSPal,FSsMid2,FSsOut,MFSMid5,MFSOut,PGoalsMid5,PGoalsMid6),
  PGoalsMid6 = [add_edge(Left,NewRight,FSVar2,PrevDtrs,RuleName,Chart)|PGoalsRest].

% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest((goal> Goal),Left,Right,PGoals,PGoalsRest,Mother,
                  PrevDtrs,[],RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
                  FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreRest,PriorVs):-
  !, empty_avl(NVs),
  terminate_store(DtrStoreRest),
  compile_body(Goal,PGoals,PGoalsMid,Context,VarsIn,VarsMid,FSPal,
               FSsIn,FSsMid,MFSIn,MFSMid,NVs,PriorVs,[]),
  genindex(M2),
  empty_avl(EMode),
  empty_avl(EAssoc),
  initialise_mode(M2,EMode,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,M2,Context,VarsMid,
		   VarsOut,FSPal,FSsMid,FSsMid2,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs),
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar2),
  generate_apply_forall_rule(DtrStore,FSVar2,RuleName,FSPal,FSsMid2,FSsOut,MFSMid3,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,Right,FSVar2,PrevDtrs,RuleName,Chart)|PGoalsRest].
	       
% 6/1/97 Octav -- added a clause for 'sem_goal>' label
% (sem_goal> daughters behave just like goal> daughters during parsing)
% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest((sem_goal> Goal),Left,Right,PGoals,PGoalsRest,Mother,
                  PrevDtrs,[],RuleName,Chart,Context,VarsIn,VarsOut,FSPal,FSsIn,
                  FSsOut,MFSIn,MFSOut,DtrStore,DtrStoreRest,PriorVs):-
  !, empty_avl(NVs),
  terminate_store(DtrStoreRest),
  compile_body(Goal,PGoals,PGoalsMid,Context,VarsIn,VarsMid,FSPal,
               FSsIn,FSsMid,MFSIn,MFSMid,NVs,PriorVs,[]),
  genindex(M2),
  empty_avl(EMode),
  empty_avl(EAssoc),
  initialise_mode(M2,EMode,ModeIn,MFSMid,MFSMid2),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsMid,PGoalsMid2,M2,Context,VarsMid,
		   VarsOut,FSPal,FSsMid,FSsMid2,ModeIn,_ModeOut,MFSMid2,MFSMid3,NVs),
% should be using ModeOut instead of separate ImplicitVars AVL to store IVars
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsMid2,PGoalsMid3),
  FS = fs(FSVar2),
  generate_apply_forall_rule(DtrStore,FSVar2,RuleName,FSPal,FSsMid2,FSsOut,MFSMid3,MFSOut,PGoalsMid3,PGoalsMid4),
  PGoalsMid4 = [add_edge(Left,Right,FSVar2,PrevDtrs,RuleName,Chart)|PGoalsRest].

% don't check inequations after mother since add_edge_deref does that
compile_dtrs_rest(Foo,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_):-
  raise_exception(ale(ill_dtr(Foo))).

% ------------------------------------------------------------------------------
% compile_desc(Desc:<desc>, FS:<fs>, IqsIn:<ineq>s, IqsOut:<ineq>s, 
%              Goals:<goal>s, GoalsRest:<goal>s, CBSafe:<bool>, VarsIn:<avl>,
%              VarsOut:<avl>, FSPal:<var>, FSsIn:<fs>s, FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% Goals are the Prolog goals required to add the description Desc
% to the feature structure FS.  IqsIn and IqsOut are uninstantiated at
% compile time.  VarsIn and VarsOut are description-level variables that
% have been seen or may have been seen already.  If a variable has definitely
% not been seen yet and CBSafe is true, then it is safe to bind that variable
% at compile-time.
% ------------------------------------------------------------------------------
compile_desc(Desc,FS,Goals,GoalsRest,Path,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,
	     ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  empty_avl(EAssoc),
  avl_store(Path,EAssoc,fs(FS),ImplicitVars),
  compile_desc_act(Desc,ImplicitVars,_,Goals,GoalsRest,Path,Context,VarsIn,VarsOut,
		   FSPal,FSsIn,FSsOut,ModeIn,ModeOut,MFSIn,MFSOut,NVs).
% HACK: the IVars AVL has no reason to exist - this should all be indexed inside Mode
%  Doesn't appear that FSPal variables are being tracked either - they could be.

compile_desc_act(Desc,IVarsIn,IVarsOut,Goals,GoalsRest,Path,Context,VarsIn,VarsOut,
		 FSPal,FSsIn,FSsOut,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  serial_desc(Desc,Path,SDesc,[],ModeIn,ModeOut,MFSIn,MFSMid,NVs), % thread mode to initialise terminal paths
  sort_desc(SDesc,SortedSDesc,ModeOut,Context,VarsIn,VarsMid,FSsIn,FSsOut,MFSMid,MFSOut),
  peep_opt(SortedSDesc,Code),
  generate_code(Code,IVarsIn,IVarsOut,FSPal,Goals,GoalsRest),
  avl_to_list(VarsMid,VarsList), keysort(VarsList,SortedVarsList),
  list_to_avl(SortedVarsList,VarsOut).  % compile-time bindings in generate_code/8 may disturb standard
                                          %   of Vars in VarsMid.

sort_desc([],[],_,_,Vars,Vars,FSs,FSs,MFS,MFS).
sort_desc([C|CodeIn],CodeOut,Mode,Context,VarsIn,VarsOut,FSsIn,FSsOut,MFSIn,MFSOut) :-
  sort_desc_instr(C,CodeOut,CodeOutRest,Mode,Context,VarsIn,VarsMid,FSsIn,FSsMid,MFSIn,MFSMid),
  sort_desc(CodeIn,CodeOutRest,Mode,Context,VarsMid,VarsOut,FSsMid,FSsOut,MFSMid,MFSOut).

sort_desc_instr(var(vstatus(SeenFlag,CBSafe,Fill),Path,Var),CodeOut,CodeOutRest,Mode,
		Context,VarsIn,VarsOut,FSs,FSs,MFSIn,MFSOut) :-
% HACK: shouldn't use get_assoc/5 here - optimise for seen/unseen, not tricky
  (  avl_change(Var,VarsIn,vmode(SeenFlag,VMode,CBSafe),VarsOut,vmode(seen,VMode,CBSafe))
  -> path_mode(Path,Mode,PMode,PathFill,MFSIn,MFSMid),
     ( VMode \== PMode -> get_mtype(VMode,VType,MFSMid),
                          unfill(PathFill,VType,Fill),
	                  unify_mode(PMode,VMode,MFSMid,MFSOut),
     	                  CodeOut = [var(vstatus(SeenFlag,CBSafe,Fill),Path,Var)|CodeOutRest]
     ; CodeOut = CodeOutRest, MFSOut = MFSMid, PathFill = Fill
     )
  ; SeenFlag = unseen,
    path_mode(Path,Mode,PMode,Fill,MFSIn,MFSOut),
    avl_store(Var,VarsIn,vmode(seen,PMode,CBSafe),VarsOut),
    ( Context == serial -> CBSafe = true  % KNOWN BUG: not all serially intro'd vars are safe
    ; Context == when_or_neg -> CBSafe = false
    ; true			% Context == disj: wait and see
    ),
    CodeOut = [var(vstatus(SeenFlag,CBSafe,Fill),Path,Var)|CodeOutRest]
  ).
%  ; assert_mode(path(Path),Mode,PMode,MFSIn,MFSMid),
%      ( avl_change(Var,VarsIn,vmode(SeenFlag,VMode,CBSafe),
%		  VarsMid,vmode(seen,VMode,CBSafe))
%      -> unify_mode(PMode,VMode,MFSMid,MFSOut)
%      ; SeenFlag = unseen, MFSOut = MFSMid,
%	avl_store(Var,VarsIn,vmode(seen,PMode,CBSafe),VarsMid),
%	( Context == serial -> CBSafe = true % KNOWN BUG: not all serially intro'd vars are safe
%	; Context == when_or_neg -> CBSafe = false
%	; true		% Context == disj: wait and see
%	)
%      ),
%      CodeOut = [var(vstatus(SeenFlag,CBSafe),Path,Var)|CodeOutRest]
%  ).

sort_desc_instr(fs(Status,Path,FS),CodeOut,CodeOutRest,Mode,_Context,Vars,Vars,FSsIn,FSsOut,MFSIn,
		MFSOut) :-
  Status = fsstatus(FSSeen,FSVar,Arg,Fill),
  track_fs(FS,FSVar,FSMode,FSSeen,Arg,FSsIn,FSsOut,MFSIn,MFSMid),
  path_mode(Path,Mode,PMode,PathFill,MFSMid,MFSMid2),
  (FSMode \== PMode -> get_mtype(FSMode,FSType,MFSMid2),
                       unfill(PathFill,FSType,Fill),
                       unify_mode(PMode,FSMode,MFSMid2,MFSOut),
                       CodeOut = [fs(Status,Path,FS)|CodeOutRest]
  ; CodeOutRest = CodeOut, MFSOut = MFSMid2, PathFill = Fill
  ).

% KNOWN BUG: assuming that when_or_neg actually matters, this switch to disj erases it.
sort_desc_instr(or(Arg1,Path,SDesc1,SDesc2),CodeOut,CodeOutRest,Mode,Context,VarsIn,VarsOut,
		FSsIn,FSsOut,MFSIn,MFSOut) :-
  ( sort_desc(SDesc1,CodeDisj1,Mode,disj,VarsIn,VarsDisj1,FSsIn,FSsDisj1,MFSIn,MFSDisj1)
  -> ( sort_desc(SDesc2,CodeDisj2,Mode,disj,VarsIn,VarsDisj2,FSsIn,FSsDisj2,MFSIn,MFSDisj2)
     -> mfs_merge(MFSIn,MFSDisj1,MFSDisj2,Context,MFSMid),
	vars_merge(VarsIn,VarsDisj1,VarsDisj2,Context,VarsOut,MFSMid,MFSMid2),
        fss_merge(FSsIn,FSsDisj1,FSsDisj2,FSsOut,MFSMid2,MFSOut),
	CodeOut = [or(Arg1,Path,CodeDisj1,CodeDisj2)|CodeOutRest]
     ; append(CodeDisj1,CodeOutRest,CodeOut), MFSOut = MFSDisj1,
       VarsOut = VarsDisj1, FSsOut = FSsDisj1
     )
  ; sort_desc(SDesc2,CodeDisj2,Mode,disj,VarsIn,VarsDisj2,FSsIn,FSsDisj2,MFSIn,MFSDisj2),
    append(CodeDisj2,CodeOutRest,CodeOut), MFSOut = MFSDisj2,
    VarsOut = VarsDisj2, FSsOut = FSsDisj2
  ).

sort_desc_instr(type(Status,Path,Type),CodeOut,CodeOutRest,Mode,_Context,Vars,Vars,FSs,FSs,
		MFSIn,MFSOut) :- 
  arg(2,Status,Fill),
  path_mode(Path,Mode,PMode,PathFill,MFSIn,MFSMid),
  get_mtype(PMode,PType,MFSMid),
  ( (ground(Type), sub_type(Type,PType)) -> CodeOutRest = CodeOut, MFSOut = MFSIn
    % if Type isn't ground, then a_/1 atom might need to bind its argument vars
  ; unfill(PathFill,Type,Fill,FillType,FilledModeType),
    assert_mode(FilledModeType,PMode,MFSMid,MFSOut),
    CodeOut = [type(Status,Path,FillType),
	       type(Status,Path,Type)|CodeOutRest]
  ).

sort_desc_instr(ineq(Status,Path,N),[ineq(Status,Path,N)|CodeOutRest],CodeOutRest,Mode,_Context,
		Vars,Vars,FSs,FSs,MFSIn,MFSOut) :-
  arg(1,Status,Fill),
  path_mode(Path,Mode,_PMode,Fill,MFSIn,MFSOut).

sort_desc_instr(fun(Status,Path,Rel,Arity,ArgPaths,ArgFills,ResArgs),
		[fun(Status,Path,Rel,Arity,ArgPaths,ArgFills,ResArgs)|CodeOutRest],
		CodeOutRest,Mode,_Context,Vars,Vars,FSs,FSs,MFSIn,MFSOut) :-
  arg(1,Status,Fill),
  paths_mode([Path|ArgPaths],Mode,_,[Fill|ArgFills],MFSIn,MFSOut).

% FS added to implicit var is subsumed by Type
unfill([fill(FillType)|Fill],Type,NewFill) :-
  sub_type(FillType,Type),
  !,NewFill = [arg|Fill].
unfill(Fill,_,Fill).

% FS added to implicit var is of Type exactly
unfill([fill(FillType)|Fill],Type,NewFill,FillType,FilledModeType) :-
  cunify_type(Type,FillType,FilledModeType),
  !,NewFill = [arg|Fill].
unfill(Fill,Type,Fill,bot,FilledModeType) :-
  copy_term(Type,FilledModeType).  % Type might be an a_/1 atom with variables

% cunify_type(+T1,+T2,-T3): T3 is an alpha-variant of lub(T1,T2).
%  This is important in the case of a_/1 atoms.  We lose variable
%  binding info as a result sometimes, but at least we won't have
%  those bindings chasing us through disjunctions and co-routined
%  goals at compile-time.
cunify_type(T1,T2,T3) :-
  copy_term(T1,CopyofT1),
  copy_term(T2,CopyofT2),
  unify_type(CopyofT1,CopyofT2,T3).

%  ; assert_mode(path(Path),Mode,PMode,MFSIn,MFSMid),
%    CodeOut = [C|CodeOutRest],
%    assert_mode(Type,PMode,MFSMid,MFSOut).

%check_fill_type([F|_],PMode,Type,MFSs,Fill) :-
%  introduce(F,FIntro), approp(F,FIntro,IntroRestr),
%  get_mtype(PMode,PType,MFSs),
%  sub_type(PType,IntroRestr),
%  !, unify_type(IntroRestr,Type,Fill).
%check_fill_type(_,_,Type,_,Type).

%check_fill_var([F|_],PMode,VMode,MFSs,IntroRestr) :-
%  introduce(F,FIntro), approp(F,FIntro,IntroRestr),
%  get_mtype(PMode,PType,MFSs),
%  get_mtype(VMode,VType,MFSs),
%  sub_type(PType,IntroRestr),
%  \+ sub_type(IntroRestr,VType),
%  !.
%check_fill_var(_,_,_,_,bot).

%check_fill_var_unseen([F|_],PMode,MFSs,IntroRestr) :-
%  introduce(F,FIntro), approp(F,FIntro,IntroRestr),
%  get_mtype(PMode,PType,MFSs),
%  sub_type(PType,IntroRestr),
%  !.
%check_fill_var_unseen(_,_,_,bot).

peep_opt([],[]).
peep_opt([Instr|Rest],OptCode) :-
  peep_opt_select(Instr,Rest,OptCode).

peep_opt_select(type(Status,Path,Type),Code,OptCode) :-
  !,peep_opt_act(Code,Status,Path,Type,OptCode).
peep_opt_select(Instr,Code,[Instr|OptRest]) :-
  peep_opt(Code,OptRest).

peep_opt_act([],Status,Path,Type,[type(Status,Path,Type)]).
peep_opt_act([Instr2|Rest],Status,Path,Type,OptCode) :-
  peep_opt_sel2(Instr2,Status,Path,Type,Rest,OptCode).

% A third possible optimisation would be to eliminate var instructions on singleton vars.  Don't
%  forget a_/1 atom argument vars - there is currently no way to specify an a_/1 atomic type
%  without an argument, which means that we're generating code for a lot of anonymous vars there.
% There's a more general way to do the second optimisation, but it requires access to mode:
%  if unifying mode with Type produces a type s, and unifying mode with FIntro produces type
%  t and s<t, then the add_type call can be eliminated, even if not Type<FIntro.
% Optimisation 2 eliminated - now implicit type additions by features are handled by adding an explicit
%  type instruction during serialisation.  Should extend Optimisation 1 to type+var and type+fs pairs,
%  though - some add_type calls can be eliminated there too.  Should also optimise inside disjunctions.
peep_opt_sel2(type(Status2,Path2,Type2),Status,Path,Type,Rest,OptCode) :-
  !,
  (Path2 == Path ->  % OPTIMISATION 1: combine successive add_type calls on same path.
                     %  But we can only do this if there is no risk of variables being bound in an a_/1 atom.
                    ( (ground(Type),ground(Type2)) -> unify_type(Type,Type2,CombinedType), 
			                              combine_status(Status,Status2,CombinedStatus),
  			                              peep_opt_act(Rest,CombinedStatus,Path,CombinedType,OptCode)
	            ; Type = bot -> peep_opt_act(Rest,Status2,Path,Type2,OptCode)
		    ; Type2 = bot -> peep_opt_act(Rest,Status,Path,Type,OptCode)
		    ; OptCode = [type(Status,Path,Type)|OptRest],  % couldn't find optimisation at this point
                      peep_opt_act(Rest,Status2,Path2,Type2,OptRest)
		    )
%  ; (append(_,[F|Path],Path2),            % OPTIMISATION 2: eliminate add_type call if following
%     introduce(F,FIntro),                 %  featval will implicitly add the type.
%     sub_type(Type,FIntro)) -> peep_opt_act(Rest,Status2,Path2,Type2,OptCode)
  ; OptCode = [type(Status,Path,Type)|OptRest],  % couldn't find optimisation at this point
    peep_opt_act(Rest,Status2,Path2,Type2,OptRest)
  ).
peep_opt_sel2(Instr2,Status,Path,Type,Rest,OptCode) :-
%  arg(2,Instr2,Path2),
%  ( (append(_,[F|Path],Path2),            % OPTIMISATION 2: eliminate add_type call if following
%     introduce(F,FIntro),                 %  featval will implicitly add the type.
%     sub_type(Type,FIntro)) -> peep_opt_select(Instr2,Rest,OptCode)
%  ; 
    OptCode = [type(Status,Path,Type)|OptRest],  % couldn't find optimisation at this point
    peep_opt_select(Instr2,Rest,OptRest).
%  ).

% currently, this is only used by the peephole optimiser to combine type instructions
combine_status(tstatus(Plicit1,Fill1),tstatus(Plicit2,_Fill2),tstatus(PlicitRes,FillRes)) :-
  ( Plicit1 == explicit -> PlicitRes = explicit
  ; Plicit2 == explicit -> PlicitRes = explicit
  ; PlicitRes = implicit
  ),
  FillRes = Fill1.  % They operate on the same path, so Fill2 will be all args.

generate_code([],IVars,IVars,_,Goals,Goals).
generate_code([Instr|Code],IVarsIn,IVarsOut,FSPal,Goals,GoalsRest) :-
  generate_instr(Instr,IVarsIn,IVarsMid,FSPal,Goals,GoalsMid),
  generate_code(Code,IVarsMid,IVarsOut,FSPal,GoalsMid,GoalsRest).

generate_instr(var(vstatus(SeenFlag,CBSafe,Fill),Path,Var),IVarsIn,IVarsOut,_,Goals,GoalsRest) :-
  ( SeenFlag == seen -> ivar_seen(Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest)
  ; SeenFlag == tricky -> ivar_tricky(Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest)
  ; % SeenFlag = unseen,
    ivar_unseen(CBSafe,Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest)
  ).
%generate_instr(var(vstatus(_SeenFlag,CBSafe),Path,Var),IVarsIn,IVarsOut,_,FSs,FSs,Goals,GoalsRest) :-
%  ivar(CBSafe,Path,Var,IVarsIn,IVarsOut,Goals,GoalsRest).
generate_instr(type(tstatus(_,Fill),Path,Type),IVarsIn,IVarsOut,_,Goals,GoalsRest) :-
  ( Type == bot -> GoalsMid = GoalsRest  % can't always eliminate these because asserting existence of
                                         %  the path may be important
  ; atom(Type) -> cat_atoms('add_to_typed_',Type,Rel), ArgsRest = [], GoalsMid = [Goal|GoalsRest],
                  Goal =.. [Rel,FSVar|ArgsRest]
  ; arg(1,Type,X), ArgsRest = [X], Rel = 'add_to_typed_a_', GoalsMid = [Goal|GoalsRest],
    Goal =.. [Rel,FSVar|ArgsRest]
  ),
  ivar_fresh(Path,Fill,IVarsIn,FS,IVarsOut,Goals,GoalsMid),
  FS = fs(FSVar).
generate_instr(ineq(ineqstatus(Fill),Path,N),IVarsIn,IVarsOut,_,Goals,GoalsRest) :-
  ivar_fresh(Path,Fill,IVarsIn,PathFS,IVarsMid,Goals,GoalsMid),
  ivar_fresh(N,N,IVarsMid,FS,IVarsOut,GoalsMid,[ineq(PathVar,FSVar)|GoalsRest]),
  PathFS = fs(PathVar),
  FS = fs(FSVar).
generate_instr(fun(funstatus(Fill),Path,Fun,Arity,ArgPaths,ArgFills,[RA|ResArgsRest]),IVarsIn,IVarsOut,_,
	       Goals,GoalsRest) :-
  ivars_fresh([Path|ArgPaths],[Fill|ArgFills],IVarsIn,IVarsOut,[ResFS|ArgFSs],Goals,[Goal|GoalsRest]),
  name(Fun,FunName),
  append("fs_",FunName,RelName),
  name(Rel,RelName),
  gen_instr_funs(ResArgsRest,RA,Rel,ResFS,ArgFSs,Arity,Goal).
generate_instr(fs(fsstatus(FSSeen,FSVar,Arg,Fill),Path,_FS),IVarsIn,IVarsOut,FSPal,Goals,GoalsRest) :-
  bind_fs(FSSeen,FSVar,Arg,FSPal,Goals,GoalsMid),
  ivar_seen(Path,Fill,FSVar,IVarsIn,IVarsOut,GoalsMid,GoalsRest).
generate_instr(or(_,_Path,DisjCode1,DisjCode2),IVarsIn,IVarsOut,FSPal,[(Goal1;Goal2)|GoalsRest],GoalsRest) :-
  generate_code(DisjCode1,IVarsIn,IVarsDisj1,FSPal,Goals1,[]),
  generate_code(DisjCode2,IVarsIn,IVarsDisj2,FSPal,Goals2,[]),
  goal_list_to_seq(Goals1,Goal1),
  goal_list_to_seq(Goals2,Goal2),
  ivars_merge(IVarsDisj1,IVarsDisj2,IVarsOut).

gen_instr_funs([],RA,Rel,ResFS,ArgFSs,Arity,Goal) :-
  gen_instr_fun(RA,Rel,ResFS,ArgFSs,Arity,Goal).
gen_instr_funs([RA2|ResArgs],RA1,Rel,ResFS,ArgFSs,Arity,(Goal1;GoalRest)) :-
  gen_instr_fun(RA1,Rel,ResFS,ArgFSs,Arity,Goal1),
  gen_instr_funs(ResArgs,RA2,Rel,ResFS,ArgFSs,Arity,GoalRest).

gen_instr_fun(ResArg,Rel,ResFS,ArgFSs,Arity,Goal) :-
  PreLen is ResArg - 1, PostLen is Arity - ResArg + 1,
  length(PreArgs,PreLen), length(PostArgs,PostLen),
  append(PreArgs,PostArgs,ArgFSs),
  append(PreArgs,[ResFS|PostArgs],RelFSs),
  Goal =.. [Rel|RelFSs].

%generate_fill(bot,_,Goals,Goals) :- !.
%generate_fill(Type,Var,[Goal|GoalsRest],GoalsRest) :-  % HACK: we should really be monitoring variable
%  ( Type = (a_ X) -> Goal = add_to_typed_a_(Var,X)     %  mode throughout the current scope - only if
%  ; cat_atoms('add_to_typed_',Type,Rel),               %  var never attains Fill value should we
%    Goal =.. [Rel,Var]                                 %  explicitly add it.
%  ).

ivars_fresh([],[],IVars,IVars,[],Goals,Goals).
ivars_fresh([Path|ArgPaths],[Fill|ArgFills],IVarsIn,IVarsOut,[FSVar|ArgFSs],Goals,GoalsRest) :-
  ivar_fresh(Path,Fill,IVarsIn,FS,IVarsMid,Goals,GoalsMid),
  FS = fs(FSVar),
  ivars_fresh(ArgPaths,ArgFills,IVarsMid,IVarsOut,ArgFSs,GoalsMid,GoalsRest).

ivar_seen(Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest) :-
  avl_fetch(Path,IVarsIn,FS) -> FS = fs(FSVar), Goals = [Var=FSVar|GoalsRest],
                                IVarsOut = IVarsIn
  ; ivar_seen_act(Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest).

ivar_seen_act([F|Path],[FFill|Fill],Var,IVarsIn,IVarsOut,Goals,GoalsRest) :-
  !, clause(fcolour(F,K,_),true),
  ivar_fresh(Path,Fill,IVarsIn,FS,IVarsMid,Goals,[FVGoal,(Var=FSatFeat)|GoalsRest]),
  ( FFill == arg -> FVGoal = arg(K,FSVar,FSatFeat)
  ; FFill = fill(FillType),
    ( FillType == bot -> FVGoal = arg(K,FSVar,FSatFeat)
    ; atom(FillType) -> cat_atoms('add_to_typed_',FillType,FillRel),
                        FillGoal =.. [FillRel,FSatFeat], FVGoal = (arg(K,FSVar,FSatFeat),FillGoal)
    ; arg(1,FillType,X), FillRel = 'add_to_typed_a_', FillGoal =.. [FillRel,FSatFeat,X],
      FVGoal = (arg(K,FSVar,FSatFeat),FillGoal)
    )
  ),
  FS = fs(FSVar),
  avl_store([F|Path],IVarsMid,fs(FSatFeat),IVarsOut).
ivar_seen_act(N,_N,Var,IVarsIn,IVarsOut,Goals,Goals) :-
  avl_store(N,IVarsIn,fs(Var),IVarsOut).

ivar_tricky(Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest) :-
  avl_fetch(Path,IVarsIn,FS) -> FS = fs(FSVar), Goals = [(Var = FSVar)|GoalsRest],
                                IVarsOut = IVarsIn
  ; ivar_tricky_act(Path,Fill,Var,IVarsIn,IVarsMid,Goals,GoalsRest),
    avl_store(Path,IVarsMid,fs(Var),IVarsOut).

ivar_tricky_act([F|Path],[FFill|Fill],Var,IVarsIn,IVarsOut,Goals,GoalsRest) :-
  !, clause(fcolour(F,K,_),true),
  ivar_fresh(Path,Fill,IVarsIn,FS,IVarsOut,Goals,[FVGoal|GoalsRest]),
  ( FFill == arg -> FVGoal = VarGoal
  ; FFill = fill(FillType),
    ( FillType == bot -> FVGoal = VarGoal
    ; atom(FillType) -> cat_atoms('add_to_typed_',FillType,FillRel),
	                FillGoal =.. [FillRel,Var], FVGoal = (VarGoal,FillGoal)
    ; arg(1,FillType,X), FillRel = 'add_to_typed_a_', FillGoal =.. [FillRel,Var,X],
      FVGoal = (VarGoal,FillGoal)
    )
  ),
  FS = fs(FSVar),
  VarGoal = arg(K,FSVar,Var).
%  FreshGoal =.. [Rel,FSVar,FVar]. 
ivar_tricky_act(_N,_AlsoN,_Var,IVars,IVars,Goals,Goals).
	    
ivar_unseen(CBSafe,Path,Fill,Var,IVarsIn,IVarsOut,Goals,GoalsRest) :-
  avl_fetch(Path,IVarsIn,FS) -> IVarsIn = IVarsOut,
                                FS = fs(FSVar),
				when(nonvar(CBSafe),ivar_unseen_fs(CBSafe,Var,FSVar,Goals,GoalsRest))
  ; ivar_unseen_act(Path,Fill,Var,IVarsIn,IVarsMid,Goals,GoalsRest),
    avl_store(Path,IVarsMid,fs(Var),IVarsOut).

ivar_unseen_fs(true,Var,Var,Goals,Goals).  % KNOWN BUG: CBSafe not being set correctly
ivar_unseen_fs(false,Var,FSVar,[(Var = FSVar)|GoalsRest],GoalsRest).

ivar_unseen_act([F|Path],[FFill|Fill],Var,IVarsIn,IVarsOut,Goals,GoalsRest) :-
  !, clause(fcolour(F,K,_),true),
  ivar_fresh(Path,Fill,IVarsIn,FS,IVarsOut,Goals,[FVGoal|GoalsRest]),
  ( FFill == arg -> FVGoal = Goal
  ; FFill = fill(FillType),
    ( FillType == bot -> FVGoal = Goal
    ; atom(FillType) -> cat_atoms('add_to_typed_',FillType,FillRel), FillGoal =.. [FillRel,Var],
	                FVGoal = (Goal,FillGoal)
    ; arg(1,FillType,X), FillRel = 'add_to_typed_a_', FillGoal =.. [FillRel,Var,X],
	                 FVGoal = (Goal,FillGoal)
    )
  ),
  FS = fs(FSVar),
  Goal = arg(K,FSVar,Var).
ivar_unseen_act(_N,_AlsoN,_Var,IVars,IVars,Goals,Goals).

ivar_fresh(Path,Fill,IVarsIn,FS,IVarsOut,Goals,GoalsRest) :-
  ( avl_fetch(Path,IVarsIn,FS) -> IVarsIn = IVarsOut, Goals = GoalsRest
  ; FS = fs(FSVar),
    ivar_unseen_act(Path,Fill,FSVar,IVarsIn,IVarsMid,Goals,GoalsRest),
    avl_store(Path,IVarsMid,FS,IVarsOut)
  ).

% NOTES: Arity of fun has changed to accommodate non-determinism in ResArg position
%        Now must incorporate redundancy elim and type merging.
%sort_desc([],[],Mode,Mode).
%sort_desc([Instr|SDesc],Code,ModeIn,ModeOut) :-
%  arg(1,Instr,Status),
%  arg(2,Instr,IPath),
%  sort_instr(Instr,SInstr,ModeIn),
%  ( var(Status) -> on_exception(nonmono,(disj_cost(SInstr,ICost,ModeIn),
%                                         sort_desc_act(SDesc,SInstr,ICost,IPath,Code,
%						       ModeIn,ModeOut,PrevSDesc,
%						       PrevSDesc)),
%				(Status = nonmono,
%				 Code = [SInstr|CodeRest],
%				 update_mode(SInstr,ModeIn,ModeMid),
%                                 sort_desc(SDesc,CodeRest,ModeMid,ModeOut)))
%  ; Status == nonmono -> Code = [SInstr|CodeRest],
%                         update_mode(SInstr,ModeIn,ModeMid),
%                         sort_desc(SDesc,CodeRest,ModeMid,ModeOut)
%  ).

%sort_desc_act([],Instr,_,_,[Instr|CodeRest],ModeIn,ModeOut,SDesc,[]) :-
%  update_mode(Instr,ModeIn,ModeMid),
%  sort_desc(SDesc,CodeRest,ModeMid,ModeOut).
%sort_desc_act([Instr|SDesc],BestInstr,BestCost,BestPath,Code,ModeIn,ModeOut,
%	      PrevSDesc,PrevSDescMid) :-
%  arg(1,Instr,Status),
%  arg(2,Instr,IPath),
%  sort_instr(Instr,SInstr,ModeIn),
%  ( var(Status) -> on_exception(nonmono,(disj_cost(SInstr,ICost,ModeIn),
%					 disj_cost_act(ICost,BestCost,SDesc,SInstr,IPath,Code,
%						       ModeIn,ModeOut,BestInstr,PrevSDesc,
%						       PrevSDescMid,BestPath)),
%				(Status = nonmono,
%  			         Code = [BestInstr|CodeRest],
%				 update_mode(BestInstr,ModeIn,ModeMid),
%				 PrevSDescMid = [SInstr|SDesc],
%				 sort_desc(PrevSDesc,CodeRest,ModeMid,ModeOut)))
%  ; Status == nonmono -> Code = [BestInstr|CodeRest],
%                         update_mode(BestInstr,ModeIn,ModeMid),
%                         PrevSDescMid = [SInstr|SDesc],
%			 sort_desc(PrevSDesc,CodeRest,ModeMid,ModeOut)
%  ).

%sort_instr(Instr,SInstr,Mode) :-
%  functor(Instr,DKind,_),
%  ( DKind == var -> SInstr = Instr
%  ; DKind == type -> SInstr = Instr
%  ; DKind == ineq -> SInstr = Instr
%  ; DKind == fun -> SInstr = Instr
%  ; DKind == fs -> SInstr = Instr
%  ; Instr = or(Status,Path,SDesc1,SDesc2),
%    SInstr = or(Status,Path,SortedDesc1,SortedDesc2),
%    sort_desc(SDesc1,SortedDesc1,Mode,_),
%    sort_desc(SDesc2,SortedDesc2,Mode,_)
%  ).

%disj_cost(var(_,Path,Var),ICost,Mode) :-
%  path_cost(Path,Mode,PathType,PathCost),
%  ( get_mode(Var,Mode,VarType) -> true
%  ; VarType = bot
%  ),
%  unify_type(PathType,VarType,ResultType),
%  ucons(ResultType,PathType,VarType,ConsTypes),
%  disj_cost_types(ConsTypes,1,ConsCost),
%  approp_cost(PathType,ResultType,AppropCost),
%  ICost is PathCost * AppropCost * ConsCost.
%disj_cost(type(_,Path,Type),ICost,Mode) :-
%  path_cost(Path,Mode,PathType,PathCost),
%  unify_type(PathType,Type,ResultType),
%  ucons(ResultType,PathType,Type,ConsTypes),
%  disj_cost_types(ConsTypes,1,ConsCost),
%  approp_cost(PathType,ResultType,AppropCost),
%  ICost is PathCost * AppropCost * ConsCost.
%disj_cost(ineq(_,Path,_),ICost,Mode) :-
%  path_cost(Path,Mode,_,ICost).
%disj_cost(fun(_,Path,Rel,Arity,ArgPaths),Cost,Mode) :-
%  get_arg_modes(ArgPaths,Path,Mode,ArgModes),
%  path_cost(Path,Mode,ResMode,ResPathCost),
%  findall(C,(clause(fun_spec(Rel,Arity,ResArg),true),
%	     PreLen is ResArg - 1, PostLen is Arity - ResArg + 1,
%	     length(PreArgs,PreLen), length(PostArgs,PostLen),
%	     append(PreArgs,PostArgs,ArgModes),
%	     append(PreArgs,[ResMode|PostArgs],RelArgModes),
%	     RelSpec =.. [Rel|RelArgModes],
%	     disj_cost_rel(RelSpec,RelCost),
%	     C is ResPathCost * RelCost),Cs),
%  sumlist(Cs,Cost).
%disj_cost(fs(_,Path,FS),Cost,Mode) :-
%  ( get_mode(Path,Mode,PathType) -> true
%  ; PathType = bot
%  ),
%  get_type(FS,FSType),
%  unify_type(PathType,FSType,ResultType),
%  ucons(ResultType,PathType,FSType,ConsTypes),
%  disj_cost_types(ConsTypes,1,ICost).
%disj_cost(or(_,Path,SDesc1,SDesc2),Cost,Mode) :-
%  ( disj_cost_list(SDesc1,1,Cost1,Mode) -> ( disj_cost_list(SDesc2,1,Cost2,Mode)
%				 	   -> Cost is Cost1 + Cost2
%					   ; Cost = Cost1
%					   )
%  ; disj_cost_list(SDesc2,1,Cost,Mode)
%  ).

%disj_cost_act(ICost,BestCost,SDesc,Instr,IPath,Code,ModeIn,ModeOut,BestInstr,PrevSDesc,
%	      PrevSDescMid,BestPath) :-
%  ( ICost < BestCost -> sort_desc_act(SDesc,Instr,ICost,IPath,Code,ModeIn,ModeOut,
%				      [BestInstr|PrevSDesc],PrevSDescMid)
%  ; ICost > BestCost -> PrevSDescMid = [Instr|PrevSDescRest],
%                        sort_desc_act(SDesc,BestInstr,BestCost,BestPath,Code,ModeIn,ModeOut,
%				      PrevSDesc,PrevSDescRest)
%  ; prior_path(IPath,BestPath) -> sort_desc_act(SDesc,Instr,ICost,IPath,Code,ModeIn,ModeOut,
%						[BestInstr|PrevSDesc],PrevSDescMid)
%  ; prior_path(BestPath,IPath) -> PrevSDescMid = [Instr|PrevSDescRest],
%                                  sort_desc_act(SDesc,BestInstr,BestCost,BestPath,Code,ModeIn,
%						ModeOut,PrevSDesc,PrevSDescRest)
%  ; prior_instr(Instr,BestInstr) -> sort_desc_act(SDesc,Instr,ICost,IPath,Code,ModeIn,ModeOut,
%						  [BestInstr|PrevSDesc],PrevSDescMid)
%  ; PrevSDescMid = [Instr|PrevSDescRest],
%    sort_desc_act(SDesc,BestInstr,BestCost,BestPath,Code,ModeIn,ModeOut,PrevSDesc,PrevSDescRest)
%  ).

%disj_cost_list([],Cost,Cost,_).
%disj_cost_list([Instr|SDesc],Accum,Cost,Mode) :-
%  disj_cost(Instr,ICost,Mode),
%  NewAccum is Accum * ICost,
%  disj_cost_list(SDesc,NewAccum,Cost,Mode).

%disj_cost_types([],Cost,Cost).
%disj_cost_types([T|Types],Accum,Cost) :-
%  disj_cost_type(T,TCost),
%  NewAccum is TCost * Accum,
%  disj_cost_types(Types,NewAccum,Cost).

%disj_cost_type(Type,Cost) :-
  

%prior_path(Path1,Path2) :-
%  path_length(Path1,Len1),
%  path_length(Path2,Len2),
%  ( Len1 < Len2 -> true
%  ; Len2 < Len1 -> fail
%  ; Path1 @> Path2
%  ).
      
%path_length([_|L],N) :-
%  !,path_length(L,NMinus1),
%  N is NMinus1 + 1.
%path_length(_,0).

%prior_instr(var(_,_,_),_).
%prior_instr(fs(_,_,_),type(_,_,_)) :- !.
%prior_instr(fs(_,_,_),ineq(_,_,_)) :- !.
%prior_instr(fs(_,_,_),fun(_,_,_,_,_)) :- !.
%prior_instr(fs(_,_,_),or(_,_,_,_)).
%prior_instr(type(_,_,_),ineq(_,_,_)) :- !.
%prior_instr(type(_,_,_),fun(_,_,_,_,_)) :- !.
%prior_instr(type(_,_,_),or(_,_,_,_)).
%prior_instr(ineq(_,_,_),fun(_,_,_,_,_)) :- !.
%prior_instr(ineq(_,_,_),or(_,_,_,_)).
%prior_instr(fun(_,_,_,_,_),or(_,_,_,_)).

%get_arg_modes([],_,_,[]).
%get_arg_modes([N|ArgPaths],Path,Mode,[T|ArgModes]) :-
%  get_mode([N|Path],Mode,T),
%  get_arg_modes(ArgPaths,Path,Mode,ArgModes).

get_type(FS,Type) :-
  deref(FS,_,Type,_).

get_type(FS,VType,Type) :-
  deref(FS,_,Type0,_),
  ( Type0 == 0 -> Type = VType
  ; Type = Type0
  ).

% get_feat/3 assumes we know that F is appropriate to FS
get_feat(F,FS,Val) :-
  clause(fcolour(F,K,_),true),
  arg(K,FS,Val).

get_vals([],_,[]).  % HACK: definitely should compile this FRs traversal out.
get_vals([F:_R|FRs],FS,[V|Vs]) :-
  clause(fcolour(F,K,_),true), arg(K,FS,V),
  get_vals(FRs,FS,Vs).
	 
% ------------------------------------------------------------------------------
% compile_desc(Desc:<desc>, Tag:<ref>, SVs:<svs>, IqsIn:<ineq>s, 
%              IqsOut:<ineq>s, Goals:<goal>s, GoalsRest:<goal>s, CBSafe:<bool>,
%              VarsIn:<avl>, VarsOut:<avl>, FSPal:<var>, FSsIn:<fs>s,
%              FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% 12-place version of compile_desc/11
% ------------------------------------------------------------------------------
%compile_desc(Desc,Tag,SVs,Goals,GoalsRest,Path,Context,VarsIn,VarsOut,
%	     FSPal,FSsIn,FSsOut,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
%  empty_avl(EAssoc),
%  avl_store(Path,EAssoc,tagpair(Tag,SVs),ImplicitVars),
%  compile_desc_act(Desc,ImplicitVars,_,Goals,GoalsRest,Path,Context,VarsIn,VarsOut,
%		   FSPal,FSsIn,FSsOut,ModeIn,ModeOut,MFSIn,MFSOut,NVs).

serial_desc(X,Path,SDesc,SRest,Mode,Mode,MFS,MFS,NVs) :-
  var(X),
  !,
  '$get_attributes'(X,TFS,_),
  ( var(TFS) -> ( avl_fetch(X,NVs,seen(Var)) -> true
		; Var = X
		),
                SDesc = [var(_,Path,Var)|SRest]
  ; ( avl_fetch(X,NVs,seen(Var)) -> SDesc = [var(_,Path,Var)|SRest]
    ; SDesc = [fs(fsstatus(_,_,_,_),Path,X)|SRest]
    )
  ).
serial_desc([],Path,[type(tstatus(explicit,_),Path,e_list)|SRest],SRest,Mode,Mode,MFS,MFS,_) :-
  !.
serial_desc([H|T],Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  !,serial_desc((hd:H,tl:T),Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs).
serial_desc(Path1 == Path2,PathPrefix,SDesc,SRest,Mode,Mode,MFS,MFS,_) :-
  !,serial_path(Path1,PathPrefix,NewVar,SDesc,SDescMid),
  serial_path(Path2,PathPrefix,NewVar,SDescMid,SRest).
serial_desc(@ MacroName,Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  !,( (current_predicate(macro,(_ macro _)), (MacroName macro Desc))
      -> serial_desc(Desc,Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs)
       ; raise_exception(ale(undef_macro(MacroName)))
    ).
serial_desc(=\= Desc,Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  !, genindex(N),
  initialise_mode(N,ModeIn,ModeMid,MFSIn,MFSMid),
  serial_desc(Desc,N,SDesc,[ineq(ineqstatus(_),Path,N)|SRest],ModeMid,ModeOut,MFSMid,MFSOut,NVs).
serial_desc(F:Desc,Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  !, ( var(F) -> raise_exception(ale(feat_notatom(F,F:Desc)))
     ; approp(F,_,_) -> clause(introduce(F,Intro),true),
                        SDesc = [type(tstatus(implicit,_),Path,Intro)|SMid],
	                serial_desc(Desc,[F|Path],SMid,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs)
     ; raise_exception(ale(undef_feat(F)))
     ).
serial_desc((Desc1,Desc2),Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  !,serial_desc(Desc1,Path,SDesc,SDescMid,ModeIn,ModeMid,MFSIn,MFSMid,NVs),
  serial_desc(Desc2,Path,SDescMid,SRest,ModeMid,ModeOut,MFSMid,MFSOut,NVs).
serial_desc((Desc1;Desc2),Path,[or(_,Path,SDesc1,SDesc2)|SRest],SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  !,serial_desc(Desc1,Path,SDesc1,[],ModeIn,ModeMid,MFSIn,MFSMid,NVs),  % in this step, we are only seeding
  serial_desc(Desc2,Path,SDesc2,[],ModeMid,ModeOut,MFSMid,MFSOut,NVs).  %  Mode with terminal paths, so continue
serial_desc(X,Path,SDesc,SRest,Mode,Mode,MFS,MFS,NVs) :-
  functor(X,Module,Arity),
  clause(marity(Module,Arity),true),
  !,
  ( avl_fetch(X,NVs,seen(Var)) -> SDesc = [var(_,Path,Var)|SRest]
  ; SDesc = [fs(fsstatus(_,_,_,_),Path,X)|SRest]
  ).
serial_desc(FunDesc,Path,SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  functor(FunDesc,Rel,Arity),
  findall(ResArg,clause(fun_spec(Rel,Arity,ResArg),true),ResArgs),
  ResArgs \== [],
  !,serial_desc_fun(0,Arity,FunDesc,Path,ArgPaths,SDesc,
		    [fun(funstatus(_),Path,Rel,Arity,ArgPaths,_,ResArgs)|SRest],ModeIn,ModeOut,MFSIn,MFSOut,NVs).
serial_desc(Type,Path,SDesc,SRest,Mode,Mode,MFS,MFS,_) :-
  type(Type),
  !, SDesc = [type(tstatus(explicit,_),Path,Type)|SRest].
serial_desc(X,_,_,_,_,_,_,_,_) :-
  atom(X) -> raise_exception(ale(undef_type(X)))
  ; raise_exception(ale(ill_desc(X))).

serial_desc_fun(A,A,_,_,[],SRest,SRest,Mode,Mode,MFS,MFS,_) :- !.
serial_desc_fun(OldP,A,FunDesc,Path,[N|ArgPaths],SDesc,SRest,ModeIn,ModeOut,MFSIn,MFSOut,NVs) :-
  P is OldP + 1,
  arg(P,FunDesc,ArgDesc),
  genindex(N),
  initialise_mode(N,ModeIn,ModeMid,MFSIn,MFSMid),
  serial_desc(ArgDesc,N,SDesc,SDescMid,ModeMid,ModeMid2,MFSMid,MFSMid2,NVs),
  serial_desc_fun(P,A,FunDesc,Path,ArgPaths,SDescMid,SRest,ModeMid2,ModeOut,MFSMid2,MFSOut,NVs).

serial_path([],Path,Var,[var(_,Path,Var)|SRest],SRest).
serial_path([F|Path],PathPrefix,Var,SDesc,SRest) :-
  ( approp(F,_,_) -> serial_path(Path,[F|PathPrefix],Var,SDesc,SRest)
  ; raise_exception(ale(undef_feat(F)))
  ).

% ------------------------------------------------------------------------------
% desc_varfs_body(+GoalDesc,-DescVars)
% ------------------------------------------------------------------------------
% DescVars is the set of ALE description variables in GoalDesc.
% ------------------------------------------------------------------------------

desc_varfs_body(GD,SortedDVs,SortedDFSs,OuterNVs) :-
  desc_varfs_body(GD,[],DVs,[],DFSs,[],OuterNVs),
  sort(DVs,SortedDVs),
  sort(DFSs,SortedDFSs).
desc_varfs_body((GD1,GD2),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_body(GD1,DVsIn,DVsMid,DFSsIn,DFSsOut,NVs,OuterNVs),
  desc_varfs_body(GD2,DVsMid,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).
desc_varfs_body((GD1;GD2),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_body(GD1,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_body(GD2,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_body((IfD -> ThenD ; ElseD),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_body(IfD,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_body(ThenD,DVsMid,DVsMid2,DFSsMid,DFSsMid2,NVs,OuterNVs),
  desc_varfs_body(ElseD,DVsMid2,DVsOut,DFSsMid2,DFSsOut,NVs,OuterNVs).
desc_varfs_body(\+ GD,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_body(GD,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).
desc_varfs_body(D1 =@ D2,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_desc(D1,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_desc(D2,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_body(true,DVs,DVs,DFSs,DFSs,_,_) :- !.
desc_varfs_body(fail,DVs,DVs,DFSs,DFSs,_,_) :- !.
desc_varfs_body(!,DVs,DVs,DFSs,DFSs,_,_) :- !.
desc_varfs_body((IfD -> ThenD),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_body(IfD,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_body(ThenD,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_body(prolog(_),DVs,DVs,DFSs,DFSs,_,_) :- !. % skip hooks - they might not be
                                                       %  ALE desc vars
desc_varfs_body(prolog(_,_),DVs,DVs,DFSs,DFSs,_,_) :- !. % skip hooks - they might not be
                                                       %  ALE desc vars
desc_varfs_body(when(Cond,Body),DVsIn,DVsOut,DFSsIn,DFSsOut,NVsIn,OuterNVs) :-
  !,desc_varfs_cond(Cond,DVsIn,DVsMid,DFSsIn,DFSsMid,NVsIn,NVsBody,OuterNVs),
  desc_varfs_body(Body,DVsMid,DVsOut,DFSsMid,DFSsOut,NVsBody,OuterNVs).
desc_varfs_body(AGD,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  AGD =.. [_|ArgDescs],
  desc_varfs_desc_list(ArgDescs,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).

desc_varfs_desc_list([],DVs,DVs,DFSs,DFSs,_,_).
desc_varfs_desc_list([D|DList],DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  desc_varfs_desc(D,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_desc_list(DList,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).

desc_varfs_desc(X,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  var(X),
  !, '$get_attributes'(X,TFS,_),
  (var(TFS) -> DFSsOut = DFSsIn,
               ( member_eq(X,NVs) -> DVsOut = DVsIn % ignore variables with narrower scope - if
                                           %  they appear outside when/2, they refer to
                                           %  something else
	       ; avl_fetch(X,OuterNVs,seen(FreshVar)) -> DVsOut = [FreshVar|DVsIn] % but if we are in
                                           % that scope, then map to its fresh name
	       ; DVsOut = [X|DVsIn]                  
	       )
  ; DVsOut = DVsIn, DFSsOut = [X|DFSsIn]
  ).
desc_varfs_desc([],DVs,DVs,DFSs,DFSs,_,_) :- !.
desc_varfs_desc([H|T],DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_desc(H,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_desc(T,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_desc(_ == _,DVs,DVs,DFSs,DFSs,_,_) :- !.
desc_varfs_desc(=\= Desc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_desc(Desc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).
desc_varfs_desc(_:Desc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_desc(Desc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).
desc_varfs_desc((D1,D2),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_desc(D1,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_desc(D2,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_desc((D1;D2),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,desc_varfs_desc(D1,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_desc(D2,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_desc(@ MacroName,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  !,(MacroName macro Desc),
  desc_varfs_desc(Desc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).
desc_varfs_desc(a_ _,DVs,DVs,DFSs,DFSs,_,_) :- !.
desc_varfs_desc(X,DVsIn,DVsOut,DFSsIn,DFSsOut,_NVs,_OuterNVs) :-
  functor(X,Module,Arity),
  clause(marity(Module,Arity),true),
  !,
  DVsOut = DVsIn, DFSsOut = [X|DFSsIn].
desc_varfs_desc(FunDesc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  functor(FunDesc,Functor,FunArity),
  clause(fun_spec(Functor,FunArity,_),true),
  !, FunDesc =.. [_|ArgDescs],
  desc_varfs_desc_list(ArgDescs,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).
desc_varfs_desc(_Type,DVs,DVs,DFSs,DFSs,_,_).  

desc_varfs_cond(X^Cond,DVsIn,DVsOut,DFSsIn,DFSsOut,NVsIn,NVsOut,OuterNVs) :-
  !,desc_varfs_cond(Cond,DVsIn,DVsOut,DFSsIn,DFSsOut,[X|NVsIn],NVsOut,OuterNVs).
desc_varfs_cond(Cond,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,NVs,OuterNVs) :-
  desc_varfs_cond0(Cond,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs).

desc_varfs_cond0((C1,C2),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  desc_varfs_cond0(C1,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_cond0(C2,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_cond0((C1;C2),DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  desc_varfs_cond0(C1,DVsIn,DVsMid,DFSsIn,DFSsMid,NVs,OuterNVs),
  desc_varfs_cond0(C2,DVsMid,DVsOut,DFSsMid,DFSsOut,NVs,OuterNVs).
desc_varfs_cond0(FS=Desc,DVsIn,DVsOut,DFSsIn,DFSsOut,NVs,OuterNVs) :-
  desc_varfs_desc(Desc,DVsIn,DVsMid,DFSsIn,DFSsOut,NVs,OuterNVs),
  ( member_eq(FS,NVs)
  -> error_msg((nl,write('narrowly quantified variable used on LHS of delay:' ),
		write(FS=Desc),nl))
  ; avl_fetch(FS,OuterNVs,seen(FreshVar)) -> DVsOut = [FreshVar|DVsMid]
  ; DVsOut = [FS|DVsMid]
  ).

map_vars([],[],_).
map_vars([V|Vs],[NV|NVs],Assoc) :-
    avl_fetch(V,Assoc,seen(NV)) -> map_vars(Vs,NVs,Assoc)
  ; NV = V, map_vars(Vs,NVs,Assoc).

nv_fresh(unseen,seen(_)).
nv_fresh(seen(Var),seen(Var)).

list_to_nv_unseen(Vars,Assoc) :-
  empty_avl(EAssoc),
  list_to_nv_unseen(Vars,EAssoc,Assoc).
list_to_nv_unseen([],A,A).
list_to_nv_unseen([V|Vs],AssocIn,AssocOut) :-
  avl_store(V,AssocIn,unseen,AssocMid),
  list_to_nv_unseen(Vs,AssocMid,AssocOut).

nv_replace_desc(X,NX,Args,ArgsRest,NVs) :-
  var(X),
  !, ( avl_fetch(X,NVs,seen(NX)) -> true
     ; NX = X
     ),
  Args = [NX|ArgsRest].
nv_replace_desc([],[],Args,Args,_) :- !.
nv_replace_desc([H|T],[NH|NT],Args,ArgsRest,NVs) :-
  !,nv_replace_desc(H,NH,Args,ArgsMid,NVs),
  nv_replace_desc(T,NT,ArgsMid,ArgsRest,NVs).
nv_replace_desc(P1==P2,P1==P2,Args,Args,_) :- !.
nv_replace_desc(=\= Desc,=\= NDesc,Args,ArgsRest,NVs) :-
  !,nv_replace_desc(Desc,NDesc,Args,ArgsRest,NVs).
nv_replace_desc(Feat:Desc,Feat:NDesc,Args,ArgsRest,NVs) :-
  !,nv_replace_desc(Desc,NDesc,Args,ArgsRest,NVs).
nv_replace_desc((D1,D2),(ND1,ND2),Args,ArgsRest,NVs) :-
  !,nv_replace_desc(D1,ND1,Args,ArgsMid,NVs),
  nv_replace_desc(D2,ND2,ArgsMid,ArgsRest,NVs).
nv_replace_desc((D1;D2),(ND1;ND2),Args,ArgsRest,NVs) :-
  !,nv_replace_desc(D1,ND1,Args,ArgsMid,NVs),
  nv_replace_desc(D2,ND2,ArgsMid,ArgsRest,NVs).
nv_replace_desc(@ Macro,@ NMacro,Args,ArgsRest,NVs) :-
  !, Macro =.. [Name|Descs],
  nv_replace_descs(Descs,NDescs,Args,ArgsRest,NVs),
  NMacro =.. [Name|NDescs].
nv_replace_desc(a_ X,a_ X,Args,Args,_) :- !.
nv_replace_desc(X,NX,Args,ArgsRest,NVs) :-
  functor(X,Module,Arity),
  clause(marity(Module,Arity),true),
  !, ( avl_fetch(X,NVs,seen(NX)) -> true
     ; NX = X
     ),
  Args = [NX|ArgsRest].
nv_replace_desc(FunDesc,NF,Args,ArgsRest,NVs) :-
  functor(FunDesc,Functor,FunArity),
  clause(fun_spec(Functor,FunArity,_),true),
  !, FunDesc =.. [_|ArgDescs],
  nv_replace_descs(ArgDescs,NArgDescs,Args,ArgsRest,NVs),
  NF =.. [Functor|NArgDescs].
nv_replace_desc(Type,ND,Args,Args,_) :-
  type(Type) -> ND = Type
  ; error_msg((nl,write('undefined type '),write(Type),write('used in description'),nl)).


nv_replace_body((GD1,GD2),(NG1,NG2),Args,ArgsRest,NVs) :-
  !,nv_replace_body(GD1,NG1,Args,ArgsMid,NVs),
    nv_replace_body(GD2,NG2,ArgsMid,ArgsRest,NVs).
nv_replace_body((GD1;GD2),(NG1;NG2),Args,ArgsRest,NVs) :-
  !,nv_replace_body(GD1,NG1,Args,ArgsMid,NVs),
    nv_replace_body(GD2,NG2,ArgsMid,ArgsRest,NVs).
nv_replace_body((G1 -> G2 ; G3),(NG1 -> NG2 ; NG3),Args,ArgsRest,NVs) :-
  !,nv_replace_body(G1,NG1,Args,ArgsMid,NVs),
  nv_replace_body(G2,NG2,ArgsMid,ArgsMid2,NVs),
  nv_replace_body(G3,NG3,ArgsMid2,ArgsRest,NVs).
nv_replace_body((G1 -> G2),(NG1 -> NG2),Args,ArgsRest,NVs) :-
  !,nv_replace_body(G1,NG1,Args,ArgsMid,NVs),
  nv_replace_body(G2,NG2,ArgsMid,ArgsRest,NVs).
nv_replace_body((\+ G1),(\+ NG1),Args,ArgsRest,NVs) :-
  !,nv_replace_body(G1,NG1,Args,ArgsRest,NVs).
nv_replace_body(prolog(Hook),prolog(Hook),Args,Args,_) :-
  !.
nv_replace_body(prolog(NVs,Hook),prolog(NVs,Hook),Args,Args,_) :-
  !.
nv_replace_body(when(Cond,Body),when(NCond,NBody),Args,ArgsRest,NVs) :-
  !, nv_replace_cond(Cond,NCond,Args,ArgsMid,NVs,NewNVs),
  nv_replace_body(Body,NBody,ArgsMid,ArgsRest,NewNVs).
nv_replace_body(AtGoal,NAtGoal,FSs,FSsRest,NVs) :-  % also handles =@,true,false,!,=
  AtGoal =.. [Rel|Args],
  nv_replace_descs(Args,NArgs,FSs,FSsRest,NVs),
  NAtGoal =.. [Rel|NArgs].
  
nv_replace_cond(X^(Cond),FreshVar^(NCond),Args,ArgsRest,NVs,NewNVs) :-
  !, avl_store(X,NVs,seen(FreshVar),NVsMid),
  nv_replace_cond(Cond,NCond,Args,ArgsRest,NVsMid,NewNVs).
nv_replace_cond(Cond,NCond,Args,ArgsRest,NVs,NVs) :-
  nv_replace_cond0(Cond,NCond,Args,ArgsRest,NVs).

nv_replace_cond0((C1,C2),(NC1,NC2),Args,ArgsRest,NVs) :-
  nv_replace_cond0(C1,NC1,Args,ArgsMid,NVs),
  nv_replace_cond0(C2,NC2,ArgsMid,ArgsRest,NVs).
nv_replace_cond0((C1;C2),(NC1;NC2),Args,ArgsRest,NVs) :-
  nv_replace_cond0(C1,NC1,Args,ArgsMid,NVs),
  nv_replace_cond0(C2,NC2,ArgsMid,ArgsRest,NVs).
nv_replace_cond0(FS=Desc,FS=NDesc,Args,ArgsRest,NVs) :-
  (var(FS) -> ArgsMid = Args ; Args = [FS|ArgsMid]), % KNOWN BUG: Why not add FS all the time?
  nv_replace_desc(Desc,NDesc,ArgsMid,ArgsRest,NVs).

nv_replace_descs([],[],Args,Args,_).
nv_replace_descs([D|Ds],[ND|NDs],Args,ArgsRest,NVs) :-
  nv_replace_desc(D,ND,Args,ArgsMid,NVs),
  nv_replace_descs(Ds,NDs,ArgsMid,ArgsRest,NVs).

%nv_replace_hook(Hook,NHook,NVs) :-
%  empty_avl(VisIn),
%  nv_replace_hook(Hook,NHook,NVs,VisIn,_).
	      
%nv_replace_hook(Hook,NHook,NVs,VisIn,VisOut) :-
%    avl_fetch(Hook,VisIn,NHook) -> VisOut = VisIn
%  ; var(Hook) -> NHook = Hook,
%                 avl_store(Hook,VisIn,NHook,VisOut)
%  ; avl_store(Hook,VisIn,NHook,VisMid),
%    functor(Hook,Functor,N),
%    functor(NHook,Functor,N),
%    nv_replace_args(0,N,Hook,NHook,NVs,VisMid,VisOut).

%nv_replace_args(N,N,_,_,_,Vis,Vis) :- !.
%nv_replace_args(I,N,Hook,NHook,NVs,VisIn,VisOut) :-
%  NewI is I + 1,
%  arg(NewI,Hook,Arg),
%  arg(NewI,NHook,NArg),
%  ( avl_fetch(Arg,NVs,seen(NArg)) -> VisMid = VisIn
%  ; nv_replace_hook(Arg,NArg,NVs,VisIn,VisMid)
%  ),
%  nv_replace_args(NewI,N,Hook,NHook,NVs,VisMid,VisOut).

nv_replace_goals(gdone).
nv_replace_goals(goal(GoalDesc,Goal,Args,ArgsRest,GoalsRest)) :-
  empty_avl(NVs),
  nv_replace_body(GoalDesc,Goal,Args,ArgsRest,NVs),
  nv_replace_goals(GoalsRest).
  
replace_hook_fss(Goal,DFSs,PGoal,PGoals,PGoalsRest,FSPal,FSsIn,FSsOut,MFSIn,MFSOut) :-
  functor(Goal,Fun,N),
  functor(PGoal,Fun,N),
  replace_hook_fss_act(0,N,Goal,DFSs,PGoal,PGoals,PGoalsRest,FSPal,FSsIn,FSsOut,MFSIn,MFSOut).

replace_hook_fss_act(N,N,_,_,_,PGoals,PGoals,_,FSs,FSs,MFS,MFS) :- !.
replace_hook_fss_act(I,N,Goal,DFSs,PGoal,PGoals,PGoalsRest,FSPal,FSsIn,FSsOut,MFSIn,MFSOut) :-
  NewI is I + 1,
  arg(NewI,Goal,A),
  arg(NewI,PGoal,PA),
  ( var(A) -> '$get_attributes'(A,TFS,_),
              ( var(TFS) -> PA=A, PGoalsMid = PGoals, FSsMid = FSsIn, MFSMid = MFSIn
	      ; functor(TFS,tfs,2) -> track_fs(A,PA,_FSVarMode,FSSeen,Arg,FSsIn,FSsMid,MFSIn,MFSMid),
                                      bind_fs(FSSeen,PA,Arg,FSPal,PGoals,PGoalsMid)
	      )
  ; (functor(A,Module,Arity),clause(marity(Module,Arity),true))
    -> track_fs(A,PA,_FSVarMode,FSSeen,Arg,FSsIn,FSsMid,MFSIn,MFSMid),
       bind_fs(FSSeen,PA,Arg,FSPal,PGoals,PGoalsMid)
  ; atomic(A) -> PA=A, PGoalsMid = PGoals, FSsMid = FSsIn, MFSMid = MFSIn
  ; replace_hook_fss(A,DFSs,PA,PGoals,PGoalsMid,FSPal,FSsIn,FSsMid,MFSIn,MFSMid)
    % otherwise, break it down - maybe we will recognise a substructure
  ),
  replace_hook_fss_act(NewI,N,Goal,DFSs,PGoal,PGoalsMid,PGoalsRest,FSPal,FSsMid,FSsOut,MFSMid,MFSOut).

% ---------------------------------------------------------------------------------------
% vars_merge(+VarsIn:<avl>,+Vars1:<avl>,+Vars2:<avl>,+Context:<context>,-VarsMerge:<avl>)
% ---------------------------------------------------------------------------------------
% Given two AVL's of variables marked tricky or seen, produce a new AVL whose
% domain is the union of the two inputs, and whose values are defined as
% follows:
%
% Vs1/Vs2  |  unseen  tricky  seen
% ----------------------------------
% unseen   |  unseen  tricky  tricky
% tricky   |  tricky  tricky  tricky
% seen     |  tricky  tricky  seen
%
% Compile-time binding safety, if not already determined, is set as follows:
%
% Context     | Vs1     | Vs2     | VsIn    | CBSafe
% -----------------------------------------------------
% when_or_neg | --------|---------|-------- | false
% disj        | ~unseen | ~unseen | unseen  | false
% disj        | unseen  | ~unseen | unseen  | abstain
% disj        | ~unseen | unseen  | unseen  | abstain
% disj        | --------|-------- | ~unseen | abstain
% serial      | ~unseen | ~unseen | unseen  | false
% serial      | unseen  | ~unseen | unseen  | true
% serial      | ~unseen | unseen  | unseen  | true
%
% Tricky variables are those that we cannot guarantee we will have seen and
% cannot guarantee that we will have not seen by the execution of the next
% item added to the Goal list.
% ---------------------------------------------------------------------------------------
vars_merge(VarsIn,Vars1,Vars2,Context,VarsMerge,MFSIn,MFSOut) :-
  avl_to_list(Vars1,VarsList1),
  avl_to_list(Vars2,VarsList2),
  vars_merge_list(VarsList1,VarsList2,Context,VarsIn,VarsListMerge,MFSIn,MFSOut),
  ord_list_to_avl(VarsListMerge,VarsMerge).

vars_merge_list([],VarsList,Context,VarsIn,VarsListTricky,MFS,MFS) :-
  vars_merge_tricky(VarsList,Context,VarsIn,VarsListTricky).
vars_merge_list([Var1-Seen1|VarsList1],VarsList2,Context,VarsIn,VarsListMerge,MFSIn,MFSOut) :-
  vars_merge_nelist(VarsList2,Var1,Seen1,VarsList1,Context,VarsIn,VarsListMerge,MFSIn,MFSOut).

% KNOWN BUG: tricky vars can't carry over Mode like this
vars_merge_tricky([],_,_,[]).
vars_merge_tricky([Var-vmode(_,Mode,CBSafe)|VarsList],Context,VarsIn,
		  [Var-vmode(tricky,Mode,CBSafe)|VarsListTricky]) :-
  cbsafe_tricky(Var,VarsIn,Context,CBSafe),
  vars_merge_tricky(VarsList,Context,VarsIn,VarsListTricky).

% KNOWN BUG: tricky vars can't carry over Mode like this
vars_merge_nelist([],Var1,vmode(_,Mode,CBSafe),VarsList1,Context,VarsIn,
		  [Var1-vmode(tricky,Mode,CBSafe)|VarsList1Tricky],MFS,MFS) :-
  cbsafe_tricky(Var1,VarsIn,Context,CBSafe),
  vars_merge_tricky(VarsList1,Context,VarsIn,VarsList1Tricky).
vars_merge_nelist([Var2-Seen2|VarsList2],Var1,Seen1,VarsList1,Context,VarsIn,VarsListMerge,MFSIn,MFSOut) :-
  compare(Comp,Var1,Var2),
  vars_merge_nelist_act(Comp,Var1,Seen1,Var2,Seen2,VarsList1,VarsList2,Context,VarsIn,
                        VarsListMerge,MFSIn,MFSOut).

vars_merge_nelist_act(=,VarMerge,vmode(Seen1,Mode1,CBSafe),_VarMerge,vmode(Seen2,Mode2,CBSafe),VarsList1,
		      VarsList2,Context,VarsIn,[VarMerge-vmode(SeenMerge,ModeMerge,CBSafe)|VarsListMerge],
		      MFSIn,MFSOut) :-
  ( Seen1==seen,Seen2==seen -> SeenMerge = seen
  ; SeenMerge = tricky
  ),
  ( var(CBSafe) -> ( avl_fetch(VarMerge,VarsIn,_) -> true % Context == disj, so abstain
		   ; CBSafe = false % regardless of Context, because neither is unseen
		   )
  ; true
  ),
  ( avl_fetch(VarMerge,VarsIn,vmode(_,ModeIn,_)) -> MFSMid = MFSIn
  ; fresh_mode(ModeIn,MFSIn,MFSMid)
  ),
  mode_merge(ModeIn,Mode1,Mode2,ModeMerge),
  vars_merge_list(VarsList1,VarsList2,Context,VarsIn,VarsListMerge,MFSMid,MFSOut).

% KNOWN BUG: tricky vars can't carry over Mode like this
vars_merge_nelist_act(<,Var1,vmode(_,Mode,CBSafe),Var2,Seen2,VarsList1,VarsList2,Context,VarsIn,
                      [Var1-vmode(tricky,Mode,CBSafe)|VarsListMerge],MFSIn,MFSOut) :-
  cbsafe_tricky(Var1,VarsIn,Context,CBSafe),	
  vars_merge_nelist(VarsList1,Var2,Seen2,VarsList2,Context,VarsIn,VarsListMerge,MFSIn,MFSOut).
% KNOWN BUG: tricky vars can't carry over Mode like this
vars_merge_nelist_act(>,Var1,Seen1,Var2,vmode(_,Mode,CBSafe),VarsList1,VarsList2,Context,VarsIn,
                      [Var2-vmode(tricky,Mode,CBSafe)|VarsListMerge],MFSIn,MFSOut) :-
  cbsafe_tricky(Var2,VarsIn,Context,CBSafe),
  vars_merge_nelist(VarsList2,Var1,Seen1,VarsList1,Context,VarsIn,VarsListMerge,MFSIn,MFSOut).

cbsafe_tricky(Var,VarsIn,Context,CBSafe) :-
  (var(CBSafe) -> ( Context == when_or_neg -> CBSafe = false
		  ; avl_fetch(Var,VarsIn,_) -> true % Context == disj, so abstain
		  ; Context == serial -> CBSafe = true
		  ; true % Context == disj, so abstain
		  )
  ; true
  ).


% ------------------------------------------------------------------------------
% tricky_vars_merge(+HookVarsList:<var>s,+VarsIn:<avl>,-VarsMerge:<avl>)
% ------------------------------------------------------------------------------
% Adds hook variables to AVL of seen/tricky variables.  Since we can only
%  assume that the user leaves a var. unbound or bound to a legitimate FS,
%  it works as follows:
%
%  Hookvar was: -      ---> tricky
%               tricky ---> tricky
%               seen   ---> seen
% ------------------------------------------------------------------------------
tricky_vars_merge([],Vars,Vars,MFS,MFS).
tricky_vars_merge([HVar|HookVarsList],VarsIn,VarsMerge,MFSIn,MFSMerge) :-
   avl_fetch(HVar,VarsIn,_Seen)   % if it is there at all, leave it unchanged
   -> tricky_vars_merge(HookVarsList,VarsIn,VarsMerge,MFSIn,MFSMerge)
    ; avl_store(HVar,VarsIn,vmode(tricky,FMode,_),VarsMid), % otherwise, add it as tricky
      fresh_mode(FMode,MFSIn,MFSMid),
      tricky_vars_merge(HookVarsList,VarsMid,VarsMerge,MFSMid,MFSMerge).


% tricky_fss_merge/3: label members of SortedDFSs as tricky in FSs
tricky_fss_merge(SortedDFSs,FSsIn,FSsOut,MFSIn,MFSOut) :-
  avl_to_list(FSsIn,SortedKFSsIn),
  tricky_kfss_merge(SortedDFSs,SortedKFSsIn,KFSsOut,MFSIn,MFSOut),
  ord_list_to_avl(KFSsOut,FSsOut).

tricky_kfss_merge([],KFSs,KFSs,MFS,MFS).
tricky_kfss_merge([DFS|DFSs],KFSsIn,KFSsOut,MFSIn,MFSOut) :-
  tricky_kfss_merge(KFSsIn,DFS,DFSs,KFSsOut,MFSIn,MFSOut).

tricky_kfss_merge([],DFS,DFSs,KFSsOut,MFSIn,MFSOut) :-
  tricky_kfss_flush(DFSs,DFS,KFSsOut,MFSIn,MFSOut).
tricky_kfss_merge([FS-KEntry|KFSs],DFS,DFSs,KFSsOut,MFSIn,MFSOut) :-
  compare(Comp,FS,DFS),
  tricky_kfss_merge_act(Comp,FS,KEntry,DFS,KFSs,DFSs,KFSsOut,MFSIn,MFSOut).

tricky_kfss_merge_act(=,FS,KEntry,_FS,KFSs,DFSs,[FS-KEntry|KFSsOut],MFSIn,MFSOut) :-
  tricky_kfss_merge(DFSs,KFSs,KFSsOut,MFSIn,MFSOut).
  % regardless of whether FS is tricky or seen, it remains so.
tricky_kfss_merge_act(<,FS,KEntry,DFS,KFSs,DFSs,[FS-KEntry|KFSsOut],MFSIn,MFSOut) :-
  tricky_kfss_merge(KFSs,DFS,DFSs,KFSsOut,MFSIn,MFSOut).
tricky_kfss_merge_act(>,FS,KEntry,DFS,KFSs,DFSs,
		      [DFS-fsmode(tricky,DFSMode,_,_)|KFSsOut],MFSIn,MFSOut) :-
  fs_to_mode(DFS,DFSMode,MFSIn,MFSMid),  	
  (DFSs = [DFS2|DFSsRest]
  -> compare(Comp,FS,DFS2),
     tricky_kfss_merge_act(Comp,FS,KEntry,DFS2,KFSs,DFSsRest,KFSsOut,MFSMid,MFSOut)
   ; % DFSs == []
     KFSsOut = KFSs
  ).

tricky_kfss_flush([],DFS,[DFS-fsmode(tricky,DFSMode,_,_)],MFSIn,MFSOut) :-
  fs_to_mode(DFS,DFSMode,MFSIn,MFSOut).
tricky_kfss_flush([DFS2|DFSs],DFS,[DFS-fsmode(tricky,DFSMode,_,_)|KFSsOut],MFSIn,MFSOut) :-
  fs_to_mode(DFS,DFSMode,MFSIn,MFSMid),
  tricky_kfss_flush(DFSs,DFS2,KFSsOut,MFSMid,MFSOut).

% ------------------------------------------------------------------------------
% find_fs(+FSsIn:<fs>s,+Tag:<tag>,+SVs:<svs>,-Goals:<goal>s,-GoalsRest:<goal>s,
%         -FSVar:<var>,+FSPal:<var>,-FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% Determine whether Tag-SVs has been seen before, or may have been seen before
% (tricky) in the current execution path.  If it was seen, use the same
% variable for it as before.  If it was not seen, add it to the register of
% FSs, FSsOut, and add an arg/3 call to the execution path that binds its
% variable to an argument of the FS palette (which argument will be determined
% by build_fs_palette/4).
% ------------------------------------------------------------------------------
%find_fs(FSsIn,FS,Goals,GoalsRest,FSVar,_,FSsOut) :-
%  find_fs_seen(FSsIn,FS,FSVar),
%  !, FSsOut = FSsIn, GoalsRest = Goals.
%find_fs(FSsIn,FS,Goals,GoalsRest,FSVar,FSPal,FSsOut) :-
%  find_fs_tricky(FSsIn,FS,FSVar,Arg,FSsOut),
%  !, Goals = [(var(FSVar) -> arg(Arg,FSPal,FSVar) ; true)|GoalsRest].
%find_fs(FSsIn,FS,[arg(Arg,FSPal,FSVar)|GoalsRest],GoalsRest,FSVar,FSPal,
%        [seen(FS,FSVar,Arg)|FSsIn]).

%find_fs_seen(FSs,FS,FSVar) :-
%  FSs = [FSFirst|FSsRest],
%  ( FSFirst = seen(SeenFS,STVar,_)
%  -> ( SeenFS == FS -> FSVar = STVar
%      ; find_fs_seen(FSsRest,FS,FSVar)
%     )
%   ; find_fs_seen(FSsRest,FS,FSVar)
%  ).

%find_fs_tricky(FSsIn,FS,FSVar,Arg,FSsOut) :-
%  FSsIn = [FSInFirst|FSsInRest],
%  ( FSInFirst = tricky(TrickyFS,TTVar,Arg)
%  -> ( TrickyFS == FS
%     -> FSVar = TTVar,
%        FSsOut = [seen(TrickyFS,TTVar,Arg)|FSsInRest]
%      ; FSsOut = [FSInFirst|FSsOutRest],
%        find_fs_tricky(FSsInRest,FS,FSVar,Arg,FSsOutRest)
%     )
%   ; FSsOut = [FSInFirst|FSsOutRest],
%     find_fs_tricky(FSsInRest,FS,FSVar,Arg,FSsOutRest)
%  ).

track_fs(FS,FSVar,FSMode,FSSeen,Arg,FSsIn,FSsOut,MFSIn,MFSOut) :-
  avl_fetch(FS,FSsIn,fsmode(FSSeen,FSMode,FSVar,Arg))
  -> MFSOut = MFSIn,
     ( FSSeen == seen -> FSsOut = FSsIn
     ; % FSSeen == tricky,
       avl_store(FS,FSsIn,fsmode(seen,FSMode,FSVar,Arg),FSsOut)
     )
  ; FSSeen = unseen,
    fs_to_mode(FS,FSMode,MFSIn,MFSOut),
    avl_store(FS,FSsIn,fsmode(seen,FSMode,FSVar,Arg),FSsOut).

bind_fs(seen,_,_,_,Goals,Goals).
bind_fs(tricky,FSVar,Arg,FSPal,[tricky_bind_fs(FSVar,Arg,FSPal)|Goals],Goals).
bind_fs(unseen,FSVar,Arg,FSPal,[arg(Arg,FSPal,FSVar)|Goals],Goals).

tricky_bind_fs(FSVar,Arg,FSPal) :-
  var(FSVar) -> '$get_attributes'(FSVar,TFS,_),
                ( var(TFS) -> arg(Arg,FSPal,FSVar)
		; true
		)
  ; true.

% ------------------------------------------------------------------------------
% build_fs_palette(+FSs:<fs>s,+FSPal:<var>,-Goals:<goal>s,+GoalsRest:<goal>s,
%                  +Iqs:<ineq>s)
% ------------------------------------------------------------------------------
% The FS-palette is a collection of instantiated feature structures that occur
%  in compiled code as a result of EFD-closure in the parser compiler, or
%  lexical rule closure in the generator compiler.  These are asserted into
%  the internal database and reloaded at run-time at the neck of every FS-
%  bearing rule in order to improve compile-time efficiency, and reduce copying
%  of structure in the compiled code.
% Building the FS-palette involves determining which argument position each
%  FS occurs in (this position is linked to the arg/3 call in the code that
%  binds a variable to its FS), and adding extra tags to the palette and 
%  arg/3 calls at the neck to ensure that structure-sharing with tags in
%  inequations is not lost.
% ------------------------------------------------------------------------------
build_fs_palette(FSAssoc,FSPal,Goals,GoalsRest,Source) :-
  avl_to_list(FSAssoc,FSs),
  residuate_term(FSs,FSsResidueSeq),
  build_fs_pal_list(FSs,FSPal,FSsResidueSeq,Goals,GoalsRest,Source).

build_fs_pal_list([],_,_,Goals,Goals,_).
build_fs_pal_list([SeenorTricky|FSs],FSPal,FSsResidueSeq,[instance(Ref,Inst),
                                                          arg(1,Inst,FSPal)|GoalsMid],
                  GoalsRest,Source) :-
  build_fs_palette_args(FSs,SeenorTricky,1,ResNum,PalArgs,PalArgsRest),
  ( FSsResidueSeq == true -> PalArgsRest = [], GoalsMid = GoalsRest
  ; PalArgsRest = [FSsResidueSeq], GoalsMid = [arg(ResNum,FSPal,ResidueCopy),
                                               call(ResidueCopy)|GoalsRest]
  ),  % HACK: SP4: we really should consult palette code with residue as body
  AssertedFSPal =.. [fspal|PalArgs], 
  assert(AssertedFSPal,Ref),
  assert(fspal_ref(Source,Ref)).

build_fs_palette_args([],FS-fsmode(_,_,_,ArgIn),ArgIn,ArgOut,[FS|Rest],Rest) :-
  ArgOut is ArgIn + 1.
build_fs_palette_args([SeenorTricky2|FSs],FS-fsmode(_,_,_,ArgIn),ArgIn,ArgOut,
                      [FS|PalArgs],Rest) :-
  NewArg is ArgIn + 1,
  build_fs_palette_args(FSs,SeenorTricky2,NewArg,ArgOut,PalArgs,Rest).

bind_dtrs([],_,FSs,FSs,MFS,MFS,ArgStore,ArgStore,PGoals,PGoals).
bind_dtrs([FS|FSs],FSPal,FSsIn,FSsOut,MFSIn,MFSOut,ArgStore,ArgStoreRest,PGoals,PGoalsRest) :-
  track_fs(FS,FSVar,_,FSSeen,Arg,FSsIn,FSsMid,MFSIn,MFSMid),
  bind_fs(FSSeen,FSVar,Arg,FSPal,PGoals,PGoalsMid),
  add_to_store(ArgStore,FSVar,ArgStoreMid),
  bind_dtrs(FSs,FSPal,FSsMid,FSsOut,MFSMid,MFSOut,ArgStoreMid,ArgStoreRest,PGoalsMid,PGoalsRest).

%init_fs_palette_dtrs(Store,FSsOut,MFSOut,ArgStore,ArgStoreRest) :-
%  empty_avl(FSsIn),
%  empty_avl(MFSIn),
%  init_fs_palette_dtrs(Store,FSsIn,FSsOut,MFSIn,MFSOut,ArgStore,ArgStoreRest).
%init_fs_palette_dtrs([],FSs,FSs,MFS,MFS,ArgStore,ArgStore).
%init_fs_palette_dtrs([FS|Rest],FSsIn,FSsOut,MFSIn,MFSOut,[FSVar|ASMid],ASRest) :-
%  track_fs(FS,FSVar,_,_,_,FSsIn,FSsMid,MFSIn,MFSMid),
%  init_fs_palette_dtrs(Rest,FSsMid,FSsOut,MFSMid,MFSOut,ASMid,ASRest).

ivars_merge(IVars1,IVars2,IVarsMerge) :-
  avl_to_list(IVars1,IVarsList1),
  avl_to_list(IVars2,IVarsList2),
  ord_merge(IVarsList1,IVarsList2,IVarsListMerge),
  ord_list_to_avl(IVarsListMerge,IVarsMerge).

% We have to unify those implicit variables that are referenced outside the
%  scope of the disjunction so that we have a stable reference to those paths.
%  No apparent harm in unifying all of them.
ord_merge([],_KVs,[]).
ord_merge([K1-V1|KVs1],KVs2,KVsMerge) :-
  ord_merge_act(KVs2,K1,V1,KVs1,KVsMerge).

ord_merge_act([],_K1,_V1,_KVs1,[]).
ord_merge_act([K2-V2|KVs2],K1,V1,KVs1,KVsMerge) :-
  compare(Comp,K2,K1),
  ord_merge_act(Comp,K2,V2,KVs2,K1,V1,KVs1,KVsMerge).

ord_merge_act(=,K,V,KVs1,_K,V,KVs2,[K-V|KVsMerge]) :-
  % unify variables associated to identical keys
  ord_merge(KVs1,KVs2,KVsMerge).
ord_merge_act(<,_K1,_V1,KVs1,K2,V2,KVs2,KVsMerge) :-
  ord_merge_act(KVs1,K2,V2,KVs2,KVsMerge).
ord_merge_act(>,K1,V1,KVs1,_K2,_V2,KVs2,KVsMerge) :-
  ord_merge_act(KVs2,K1,V1,KVs1,KVsMerge).

% ------------------------------------------------------------------------------
% fss_merge(+FSs1:<fs>s,+FSs2:<fs>s,-MergedFSs:<fs>s)
% ------------------------------------------------------------------------------
% Merge two lists of seen/tricky FSs (used to build FS-palette).
% ------------------------------------------------------------------------------
fss_merge(FSsIn,FSs1,FSs2,FSsMerge,MFSIn,MFSOut) :-
  avl_to_list(FSs1,FSsList1),
  avl_to_list(FSs2,FSsList2),
  fss_merge_list(FSsList1,FSsList2,FSsIn,FSsListMerge,MFSIn,MFSOut),
  ord_list_to_avl(FSsListMerge,FSsMerge).

fss_merge_tricky([],[],MFS,MFS).
fss_merge_tricky([FS-fsmode(_,_,FSVar,Arg)|FSsList],[FS-fsmode(tricky,FreshMode,FSVar,Arg)|FSsListMerge],
		 MFSIn,MFSOut) :-
  fresh_mode(FreshMode,MFSIn,MFSMid),
  fss_merge_tricky(FSsList,FSsListMerge,MFSMid,MFSOut).

fss_merge_list([],FSsList,_,FSsListMerge,MFSIn,MFSOut) :-
  fss_merge_tricky(FSsList,FSsListMerge,MFSIn,MFSOut).
fss_merge_list([FS1-Entry1|FSsList1],FSsList2,FSsIn,FSsListMerge,MFSIn,MFSOut) :-
  fss_merge_nelist(FSsList2,FS1,Entry1,FSsList1,FSsIn,FSsListMerge,MFSIn,MFSOut).

fss_merge_nelist([],FS1,fsmode(_,_,FSVar,Arg),FSsList1,_,
		 [FS1-fsmode(tricky,FreshMode,FSVar,Arg)|FSsListMerge],MFSIn,MFSOut) :-
  fresh_mode(FreshMode,MFSIn,MFSMid),
  fss_merge_tricky(FSsList1,FSsListMerge,MFSMid,MFSOut).
fss_merge_nelist([FS2-Entry2|FSsList2],FS1,Entry1,FSsList1,FSsIn,FSsListMerge,MFSIn,MFSOut) :-
  compare(Comp,FS1,FS2),
  fss_merge_nelist_act(Comp,FS1,Entry1,FS2,Entry2,FSsList1,FSsList2,FSsIn,FSsListMerge,MFSIn,MFSOut).

fss_merge_nelist_act(=,FS,fsmode(Seen1,Mode1,FSVar,Arg),_FS,fsmode(Seen2,Mode2,FSVar,Arg),FSsList1,
		     FSsList2,FSsIn,[FS-fsmode(Seen,Mode,FSVar,Arg)|FSsListMerge],MFSIn,MFSOut) :-
  ( (Seen1==seen,Seen2==seen) -> Seen = seen
  ; Seen = tricky
  ),
  ( avl_fetch(FS,FSsIn,fsmode(_,ModeIn,_,_)) -> MFSMid = MFSIn
  ; fresh_mode(ModeIn,MFSIn,MFSMid)
  ),
  mode_merge(ModeIn,Mode1,Mode2,Mode),
  fss_merge_list(FSsList1,FSsList2,FSsIn,FSsListMerge,MFSMid,MFSOut).
fss_merge_nelist_act(<,FS1,fsmode(_,_,FSVar,Arg),FS2,Entry2,FSsList1,FSsList2,FSsIn,
		     [FS1-fsmode(tricky,FreshMode,FSVar,Arg)|FSsMerge],MFSIn,MFSOut) :-
  fresh_mode(FreshMode,MFSIn,MFSMid),
  fss_merge_nelist(FSsList1,FS2,Entry2,FSsList2,FSsIn,FSsMerge,MFSMid,MFSOut).
fss_merge_nelist_act(>,FS1,Entry1,FS2,fsmode(_,_,FSVar,Arg),FSsList1,FSsList2,FSsIn,
 	             [FS2-fsmode(tricky,FreshMode,FSVar,Arg)|FSsMerge],MFSIn,MFSOut) :-
  fresh_mode(FreshMode,MFSIn,MFSMid),
  fss_merge_nelist(FSsList2,FS1,Entry1,FSsList1,FSsIn,FSsMerge,MFSMid,MFSOut).

% ------------------------------------------------------------------------------
% key_fss(+FSs:<fs>s,-KeyedFSs:<fs>s)
% ------------------------------------------------------------------------------
% Key a list of FSs by their tags.
% ------------------------------------------------------------------------------
key_fss([],[]).
key_fss([FSEntry|FSs],[FS-FSEntry|KFSs]) :-
  arg(1,FSEntry,FS),
  key_fss(FSs,KFSs).

dekey_list([],[]).
dekey_list([_-FSEntry|KFSs],[FSEntry|FSsMerge]) :-
  dekey_list(KFSs,FSsMerge).

% ------------------------------------------------------------------------------
% compile_pathval(Path:<path>,FSIn:<fs>,FSOut:<fs>,
%                 IqsIn:<ineq>s,IqsOut:<ineq>s,
%                 Goals:<goal>s, GoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% Goals-GoalsRest is difference list of goals needed to determine that
% FSOut is the (undereferenced) value of dereferenced FSIn at Path;
% might instantiate Tag or substructures in SVs in finding path value
% ------------------------------------------------------------------------------
%compile_pathval([],FS,FS,Goals,Goals) :- !.
%compile_pathval([Feat|Feats],FS,FSAtPath,
%                [Goal|GoalsMid],GoalsRest):-
%  !, ( approp(Feat,_,_) -> true
%     ; error_msg((nl,write_list([undefined,feature,Feat,used,in,path,[Feat|Feats]]),nl))
%     ),
%  cat_atoms('featvald_',Feat,Rel),
%  Goal =.. [Rel,FS,FSAtFeat],
%  compile_pathval(Feats,FSAtFeat,FSAtPath,GoalsMid,GoalsRest).
%compile_pathval(P,_,_,_,_,_,_) :-
%  error_msg((nl,write('pathval: illegal path specified - '),
%                write(P))).

% ------------------------------------------------------------------------------
% compile_pathval(Path:<path>,RefIn:<ref>,SVsIn:<svs>,FSOut:<fs>,
%                 IqsIn:<ineq>s,IqsOut:<ineq>s,
%                 Goals:<goal>s, GoalsRest:<goal>s)
% ------------------------------------------------------------------------------
% 6-place version of compile_pathval/5
% ------------------------------------------------------------------------------
%compile_pathval([],Tag,SVs,Tag-SVs,Goals,Goals) :- !.
%compile_pathval([Feat|Feats],Tag,SVs,FSAtPath,
%                [Goal|GoalsMid],GoalsRest):-
%  !, ( approp(Feat,_,_) -> true
%     ; error_msg((nl,write_list([undefined,feature,Feat,used,in,path,[Feat|Feats]]),nl))
%     ),
%  cat_atoms('featvald_',Feat,Rel),
%  Goal =.. [Rel,SVs,Tag,FSAtFeat],
%  compile_pathval(Feats,FSAtFeat,FSAtPath,GoalsMid,GoalsRest).
%compile_pathval(P,_,_,_,_,_) :-
%  error_msg((nl,write('illegal path specified - '),
%                write(P))).

% ------------------------------------------------------------------------------
% compile_fun(Fun:<fun>,FS:<fs>,IqsIn:<ineq>s,IqsOut:<ineq>s,
%             Goals:<goal>s,GoalsRest:<goal>s,CBSafe:<bool>,VarsIn:<var>s,
%             VarsOut:<var>s,FSPal:<var>,FSsIn:<fs>s,FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% Goals-RoalsRest is difference list of goals needed to determine that FS
%  satisfies functional constraint Fun
% ------------------------------------------------------------------------------
compile_funs([],ResArg,Rel,FS,FunArgs,FunArity,SpecGoal) :-
  compile_fun(ResArg,Rel,FS,FunArgs,FunArity,SpecGoal).
compile_funs([RA2|ResArgs],ResArg,Rel,FS,FunArgs,FunArity,(SpecGoal;GoalsRest)) :-
  compile_fun(ResArg,Rel,FS,FunArgs,FunArity,SpecGoal),
  compile_funs(ResArgs,RA2,Rel,FS,FunArgs,FunArity,GoalsRest).

compile_fun(ResArg,Rel,FS,FunArgs,FunArity,SpecGoal) :-
  PreLen is ResArg - 1, PostLen is FunArity - ResArg + 1,  
  length(PreArgs,PreLen), length(PostArgs,PostLen),        
  append(PreArgs,PostArgs,FunArgs),
%                    append(PostArgs,[IqsMid,IqsOut],PostRelArgs),
  append(PreArgs,[FS|PostArgs],RelArgs),
  SpecGoal =.. [Rel|RelArgs].

%compile_fun(FunDesc,FS,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,VarsOut,FSPal,
%            FSsIn,FSsOut,NVs) :-
%  FunDesc =.. [Rel|ArgDescs],
%  compile_descs_fresh(ArgDescs,Args,IqsIn,IqsMid,Goals,
%                      [deref(FS,Tag,SVs),
%                       fsolve(Fun,Tag,SVs,IqsMid,IqsOut)|GoalsRest],
%                      CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,NVs),
%  Fun =.. [Rel|Args].

% ------------------------------------------------------------------------------
% compile_fun(Fun:<fun>,Ref:<ref>,SVs:<svs>,IqsIn:<ineq>s,IqsOut:<ineq>s,
%             Goals:<goal>s,GoalsRest:<goal>s,CBSafe:<bool>,VarsIn:<var>s,
%             VarsOut:<var>s,FSPal:<var>,FSsIn:<fs>s,FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% 7-place version of compile_fun/6
% ------------------------------------------------------------------------------
%compile_fun(FunDesc,Tag,SVs,IqsIn,IqsOut,Goals,GoalsRest,CBSafe,VarsIn,
%            VarsOut,FSPal,FSsIn,FSsOut,NVs) :-
%  FunDesc =.. [Rel|ArgDescs],
%  compile_descs_fresh(ArgDescs,Args,IqsIn,IqsMid,Goals,
%                      [fsolve(Fun,Tag,SVs,IqsMid,IqsOut)|GoalsRest],
%                      CBSafe,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,NVs),
%  Fun =.. [Rel|Args].


% ------------------------------------------------------------------------------
% alex(+Exception)
% ------------------------------------------------------------------------------
% ALE exception handler
% ------------------------------------------------------------------------------
alex(Exception) :-
  format(user_error,'{ALE: ERROR: ',[]),
  try_ale_exception(Exception),
  format(user_error,'}~n~n',[]),
  flush_output(user_error), terminate_alex(Exception).

terminate_alex(Exception) :- recoverable_ale_exception(Exception),!,fail.
terminate_alex(_) :- abort.  % default termination

:- multifile recoverable_ale_exception/1.
recoverable_ale_exception(fsvar_noadd(_,_)).
recoverable_ale_exception(path_noadd(_,_,_)).
recoverable_ale_exception(feat_noadd(_,_)).
recoverable_ale_exception(macro_noadd(_,_)).
recoverable_ale_exception(type_noadd(_,_,_)).
recoverable_ale_exception(featpath_noadd(_,_,_,_)).

try_ale_exception(X) :- ale_exception(X),!.
try_ale_exception(X) :- write(user_error,X).  % default handler

:- multifile ale_exception/1.
ale_exception(upward_closure(Feat,T,VRs)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'incompatible restrictions on feature ~a at type ~a: ~@',
         [Feat,T,write_term(VRs,Options)]).
ale_exception(no_lub(T1,T2,Mins)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'consistent ~a and ~a have multiple mgus: ~@',
         [T1,T2,write_term(Mins,Options)]).
ale_exception(subtype_cycle(T,Path)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'subtyping cycle at ~a: ~@',[T,write_term(Path,Options)]).
ale_exception(approp_cycle(T,Path)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'appropriateness cycle following path ~@ from type ~a',
         [write_term(Path,Options),T]).
ale_exception(sub_lhs_var(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' illegal variable occurrence in ',[]),
  write_term(user_error,Clause,Options).
ale_exception(intro_lhs_var(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' illegal variable occurrence in ',[]),
  write_term(user_error,Clause,Options).
ale_exception(sub_rhs_var(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' illegal variable occurrence in ',[]),
  write_term(user_error,Clause,Options).
ale_exception(intro_rhs_var(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' illegal variable occurrence in ',[]),
  write_term(user_error,Clause,Options).
ale_exception(intro_vr_var(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' illegal variable occurrence in ',[]),
  write_term(user_error,Clause,Options).
ale_exception(ext_rhs_var(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' illegal variable occurrence in ',[]),
  write_term(user_error,Clause,Options).
ale_exception(sub_lhs_abar) :-
  format(user_error,'subtype/feature specification given for a_/1 atom',[]).
ale_exception(intro_lhs_abar) :-
  format(user_error,'subtype/feature specification given for a_/1 atom',[]).
ale_exception(sub_lhs_other(Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Term,Options),
  format(user_error,' sub ... - user-defined types must be Prolog atoms',[]).
ale_exception(intro_lhs_other(Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Term,Options),
  format(user_error,' intro ... - user-defined types must be Prolog atoms',[]).
ale_exception(sub_rhs_other(LHS,Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,
         ' ~a sub [...~@...] - user-defined types must be Prolog atoms',
         [LHS,write_term(Term,Options)]).
ale_exception(ext_rhs_other(Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,
         ' ext [...~@...] - user-defined types must be Prolog atoms',
         [write_term(Term,Options)]).
ale_exception(sub_rhs_notlist(Clause,Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - expected list of types, found: ',[]),
  write_term(user_error,Term,Options).
ale_exception(ext_rhs_notlist(Clause,Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - expected list of types, found: ',[]),
  write_term(user_error,Term,Options).
ale_exception(cyclic_abar_restriction(F,R,Clause,ArgNo)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,'arg ~d: feature ~a has cyclic a_/1 atom ',[ArgNo,F]),
  write_term(user_error,R,Options),
  format(user_error,' as its value restriction',[]).
ale_exception(intro_rhs_notlist(Clause,Term)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - expected list of feature:value_restriction, found: ',
         []),
  write_term(user_error,Term,Options).
ale_exception(bot_feats(Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - bot has appropriate features',[]).
ale_exception(bot_subsumed(S)) :-
  format(user_error,'~a subsumes bot',[S]).
ale_exception(bot_ext) :-
  format(user_error,'bot cannot be extensional',[]).
ale_exception(abar_subsumed(S)) :-
  format(user_error,'a_/1 atom declared subsumed by type ~a',[S]).
ale_exception(feat_notatom(F,Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - features must be Prolog atoms, found ',[]),
  write_term(user_error,F,Options).
ale_exception(vr_other(R,Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,
         ' - value restrictions must be Prolog atoms or a_/1 atoms, found ',
         []),
  write_term(user_error,R,Options).
ale_exception(fr_other(FR,Clause)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - expected feature:value_restriction, found ',[]),
  write_term(user_error,FR,Options).

ale_exception(undef_feat(F)) :-
  format(user_error,' feature ~a undefined',[F]).
ale_exception(undef_type(Type)) :-
  format(user_error,' type ~a undefined',[Type]).
ale_exception(undef_macro(Macro)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Macro,Options),
  format(user_error,' - macro undefined',[]).
ale_exception(ill_desc(D)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,D,Options),
  format(user_error,' - illegal description',[]).
ale_exception(undef_cond_feat(F,Desc)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' feature ~a undefined in conditional description ',[F]),
  write_eterm(user_error,Desc,Options).
ale_exception(ill_cond_desc(Cond,Desc)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Cond,Options),
  format(user_error,' - illegal conditional description in ',[]),
  write_term(user_error,Desc,Options).
ale_exception(ill_cond(C)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,C,Options),
  format(user_error,' - illegal conditional',[]).
ale_exception(narrow_left(FS,Desc)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,' narrowly quantified variable used on LHS of delay: ',[]),
  write_term(user_error,(FS=Desc),Options).

ale_exception(duplicate_sub(S)) :-
  format(user_error,'~a multiply defined',[S]).
ale_exception(duplicate_intro(S)) :-
  format(user_error,'multiple feature specifications for type ~a',[S]).
ale_exception(duplicate_vr(F,S)) :-
  format(user_error,'multiple specification for ~a in declaration of ~a',
           [F,S]).
ale_exception(duplicate_ext(AllEs)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'multiple ext/1 declarations found: ~n',[]),
  ( member(Es,AllEs),
    format(user_error,'  ~@~n',[write_term(user_error,Es,Options)])
  ; true
  ).
ale_exception(no_stmatrix) :-
  format(user_error,
           'compiled code for sub/2 not found: run compile_sub_type/1 first',
           []).
ale_exception(ext_nomax(E)) :-
  format(user_error,'extensional type ~a is not maximal',[E]).
ale_exception(feat_intro(F,Mins)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'feature ~a multiply introduced at ~@',
         [F,write_term(Mins,Options)]).

ale_exception(fsvar_noadd(X,FS)) :-
  tell_user_error((
             \+ \+ (frozen_term(X,Frozen1),
		    frozen_term(FS,Frozen2),
		    ( (current_predicate(portray_unif_failure,portray_unif_failure(_,_,_,_)),
		       portray_unif_failure(X,Frozen1,FS,Frozen2)) -> true
		; filter_iqs(Frozen1,Iqs1,FSGoals1),
		  filter_iqs(Frozen2,Iqs2,FSGoals2),
                  (ale_flag(residue,show) -> residue_args(FSGoals1,ResArgs,[X|ResArgs2]),
		                             residue_args(FSGoals2,ResArgs2,[FS])
		  ; ResArgs = [X,FS]
		  ),
                  empty_avl(AssocIn),
                  duplicates_list(ResArgs,AssocIn,DupsMid,AssocIn,VisMid,0,NumMid),
	          duplicates_iqs(Iqs1,DupsMid,DupsMid2,VisMid,VisMid2,NumMid,NumMid2),
                  duplicates_iqs(Iqs2,DupsMid2,DupsOut,VisMid2,Inf,NumMid2,_),
                  nl, write('add_to could not unify '),
                  nl,tab(5),
  		  pp_fs(X,DupsOut,Inf,AssocIn,Vis2Mid,5,AssocIn,HDMid), nl,
		  pp_iqs(Iqs1,DupsOut,Inf,Vis2Mid,Vis2Mid2,5,HDMid,HDMid2),
		  ((ale_flag(residue,show),FSGoals1 \== [])
		  -> nl,nl, write('Residue:'),
		     pp_residue(FSGoals1,DupsOut,Inf,Vis2Mid2,Vis2Mid3,HDMid2,HDMid3)
		  ; Vis2Mid3 = Vis2Mid2, HDMid3 = HDMid2
		  ),
		  nl, write('and '),
		  nl, tab(5),
		  pp_fs(FS,DupsOut,Inf,Vis2Mid3,Vis2Mid4,5,HDMid3,HDMid4),
		  pp_iqs(Iqs2,DupsOut,Inf,Vis2Mid4,Vis2Out,5,HDMid4,HDOut),
		  ((ale_flag(residue,show),FSGoals2 \== [])
		  -> nl,nl, write('Residue:'),
		     pp_residue(FSGoals2,DupsOut,Inf,Vis2Out,_,HDOut,_)
                  ; true
		  ),nl)))).
ale_exception(path_noadd(Path1,Path2,FS)) :-
  tell_user_error((frozen_term(FS,Frozen),
	             ((current_predicate(portray_path_failure,portray_path_failure(_,_,_,_)),
		       portray_path_failure(Path1,Path2,FS,Frozen)) -> true
		     ; nl, write('add_to could not unify paths '), 
                       write(Path1), write(' and '), 
                       write(Path2), write(' in '),
                       nl, pp_fs_res_col(FS,Frozen,5),
                       nl
	  	     ))).
ale_exception(feat_noadd(Feat,FS)) :-
  tell_user_error((frozen_term(FS,Frozen),
                     ((current_predicate(portray_feat_failure,portray_feat_failure(_,_,_)),
	               portray_feat_failure(Feat,FS,Frozen)) -> true
                     ; nl, write('add_to could not add feature '), write(Feat), 
                       write(' to '), pp_fs_res_col(FS,Frozen,5),
                       nl))).
ale_exception(macro_noadd(MacroName,FS)) :-
  tell_user_error((frozen_term(FS,Frozen),
	             ((current_predicate(portray_macro_failure,portray_macro_failure(_,_,_)),
		       portray_macro_failure(MacroName,FS,Frozen)) -> true
 	             ; nl, write('add_to could not add undefined macro '),
                       write(MacroName),
                       write(' to '), pp_fs_res_col(FS,Frozen,5),
                       nl
	             ))).
ale_exception(type_noadd(Type,FS,MGType)) :-
  tell_user_error((frozen_term(FS,Frozen),
                     ((current_predicate(portray_addtype_failure,portray_addtype_failure(_,_,_,_)),
                       portray_addtype_failure(Type,FS,MGType,Frozen))
		     -> write('(see graphical window)')
                     ; nl, write('add_to could not add incompatible type '), 
                       write(Type),  % this really is Type and not AddType - VType is implicit 
                       nl, write('to '), pp_fs_res_col(FS,Frozen,5,MGType), % in appropriateness
                       nl
                     ))).
ale_exception(featpath_noadd(Feat,Path,FS,MGType)) :-
  tell_user_error((frozen_term(FS,Frozen),
                     ((current_predicate(portray_featpath_failure,portray_featpath_failure(_,_,_,_,_)),
                       portray_featpath_failure(Feat,Path,FS,MGType,Frozen)) -> true
                     ; write('feature '), write(Feat), write(' in path '), 
                       write([Feat|Path]), write('could not be added to '), 
                       pp_fs_res_col(FS,Frozen,5,MGType)
                     ))).

ale_exception(no_lex) :-
  format(user_error,'no lexicon found: run compile_gram/1 in parse mode first',[]).
ale_exception(unk_words(Ws)) :-
  format(user_error,'unknown words: ~w are not in the lexicon',[Ws]).
ale_exception(forall_lex_dup(N)) :-
  format(user_error,'duplicate name: ~a forall --->',[N]).
ale_exception(forall_rule_dup(N)) :-
  format(user_error,'duplicate name: ~a forall ===>',[N]).
ale_exception(forall_lex_rule_dup(N)) :-
  format(user_error,'duplicate name: ~a forall lex_rule',[N]).

ale_exception(cats_no_lists(RuleName,Dtrs)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'lists not defined, but ~a uses cats> ',[RuleName]),
  write_term(user_error,Dtrs,Options).
ale_exception(ill_dtr(Dtr)) :-
  prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Dtr,Options),
  format(user_error,' - illegal RHS directive in rule',[]).


ale_warning(no_types_defined) :-
  !,format(user_error,'no types defined',[]).
ale_warning(duplicate_types(S,Clause,ArgNo)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - arg ~d: ~a appears more than once',[ArgNo,S]).
ale_warning(duplicate_decl(Clause)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,' - declaration appears more than once',[]).
ale_warning(duplicate_feat(F,VR,T)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'feature ~a declared on type ~a with value restriction ',
         [F,T]),
  write_term(user_error,VR,Options),
  format(user_error,' more than once',[]).
ale_warning(implicit_mins(ImplicitMins)) :-
  !,format(user_error,'assuming the following types are immediately subsumed by bot: ',[]),
  write_list(ImplicitMins,user_error).  
ale_warning(implicit_maxs(ImplicitMaxs)) :-
  !,format(user_error,'assuming the following types are maximally specific: ',[]),
  write_list(ImplicitMaxs,user_error).
ale_warning(unary_branch(T,U)) :-
  !,format(user_error,'unary branch from ~a to ~a',[T,U]).
ale_warning(identical_macro_clauses(MacroName,Arity,Head,Body)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'identical clauses defined for macro ~a/~d: ~@',[MacroName,Arity,write_term((Head macro Body),Options)]).
ale_warning(discontiguous_macro_clauses(MacroName,Arity)) :-
  !,format(user_error,'discontiguous clauses defined for macro ~a/~d',[MacroName,Arity]).
ale_warning(multiple_macro_clauses(MacroName,Arity)) :-
  !,format(user_error,'multiple clauses defined for macro ~a/~d',[MacroName,Arity]).
ale_warning(no_features) :-
  !,format(user_error,'no features declared',[]).
ale_warning(ground_abar_restriction(F,R,Clause,ArgNo)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,'arg ~d: feature ~a has ground a_/1 atom ',[ArgNo,F]),
  write_term(user_error,R,Options),
  format(user_error,' as its value restriction',[]).
ale_warning(abar_ext(Clause)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  write_term(user_error,Clause,Options),
  format(user_error,'all a_/1 atoms are automatically extensional',[]).
ale_warning(nontriv_upward_closure(F,T,V,R)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'non-trival upward closure of feature ~a at type ~a: ',[F,T]),
  format(user_error,' declared ~@, closed to ~@',[write_term(V,Options),
                                                  write_term(R,Options)]).
ale_warning(join_nopres(F,T1,T2)) :-
  !,format(user_error,'homomorphism condition fails for ~a in ~a and ~a',[F,T1,T2]).
ale_warning(dcs_failure(Clause)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'definite clause unsatisfiable: ',[]),
  format(user_error,'~@',[write_term(Clause,Options)]).
ale_warning(cond_failure(Cond,Body)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'condition unsatisfiable in when/2 goal - replacing with true/0: ',[]),
  format(user_error,' when(~@,~@)',
	 [write_term(Cond,Options), write_term(Body,Options)]).
ale_warning(shallow_cut_failure_if(Goal)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'if-statement unsatisifiable in shallow cut: ',[]),
  format(user_error,'~@',[write_term(Goal,Options)]).
ale_warning(shallow_cut_failure_then(Goal)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'then-statement unsatisifiable in shallow cut: ',[]),
  format(user_error,'~@',[write_term(Goal,Options)]).
ale_warning(shallow_cut_failure_else(Goal)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'else-statement unsatisifiable in shallow cut: ',[]),
  format(user_error,'~@',[write_term(Goal,Options)]).
ale_warning(neg_arg_failure(Goal)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'negated goal unsatisfiable - replacing with true/0: ',[]),
  format(user_error,'~@',[write_term(Goal,Options)]).
ale_warning(disj1_failure(Goal)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'first disjunct unsatisfiable in: ',[]),
  format(user_error,'~@',[write_term(Goal,Options)]).
ale_warning(disj2_failure(Goal)) :-
  !,prolog_flag(toplevel_print_options,Options,Options),
  format(user_error,'second disjunct unsatisfiable in: ',[]),
  format(user_error,'~@',[write_term(Goal,Options)]).
ale_warning(edgelimit_exceeded(Limit)) :-
  !,format(user_error,'edge limit: ~a has been exceeded',[Limit]).
ale_warning(X) :-
  write(user_error,X).


% ==============================================================================
% Compiler
% ==============================================================================

% ------------------------------------------------------------------------------
% compile_gram(File:<file>)
% ------------------------------------------------------------------------------
% compiles grammar from File;  all commands set up same way, with optional
% argument for file, which is recompiled, if necessary
% ------------------------------------------------------------------------------

:- dynamic alec/1.
:- dynamic sub_rhstype/1, ext_or_intro_rhstype/1, extensional/1.
:- dynamic stmatrix_num/2, stmatrix_dim/1.
:- dynamic num_type/2, type_num/2.
:- dynamic introduce/2.
:- dynamic wpred/2,wpred_compiled/1.
:- dynamic subsume_ready/0.
:- dynamic index/1.
:- multifile alec_catch_hook/2.

alec_announce(Message) :-
  write(user_error,Message),nl(user_error),flush_output(user_error).

touch(File) :-
  file_exists(File,[read]) -> true
  ; open(File,write,S),
    close(S).

alec_catch(Code) :-
  retract(alec(Stage))
  -> on_exception(ale(Exception),alec_catch_hook(Stage,Code),alex(Exception))
   ; (Code = end_of_file).

%alec_catch_hook(subtype,[(:- discontiguous sub_type/2)|Code]) :-
%  !,multi_hash(1,(sub_type)/2,Code,[end_of_file]).
alec_catch_hook(unifytype,[(:- discontiguous unify_type/3)|Code]) :-
  !,multi_hash(1,(unify_type)/3,Code,[end_of_file]).
alec_catch_hook(approp,[(:- discontiguous approp/3)|Code]) :-
  !,multi_hash(1,(approp)/3,Code,[end_of_file]).
alec_catch_hook(approps,Code) :-
  multi_hash(0,(approps)/3,Code,[end_of_file]).
%alec_catch_hook(ext,Code) :-
%  !,compile_ext(Code,[end_of_file]).
%alec_catch_hook(iso,Code) :-
%  !,multi_hash(0,(iso_sub_seq)/5,Code,[end_of_file]).
%alec_catch_hook(check,Code) :-
%%  !,multi_hash(0,(check_sub_seq)/5,Code,CodeMid),
%  multi_hash(0,(check_pre_traverse)/6,Code,CodeRest),
%  multi_hash(0,(check_post_traverse)/6,CodeRest,[end_of_file]).
%alec_catch_hook(fun,Code) :-
%  !,compile_fun(Code,[end_of_file]).
%alec_catch_hook(fsolve,Code) :-
%  !,multi_hash(0,(fsolve)/5,Code,[end_of_file]).
alec_catch_hook(ct,Code) :-
  !,multi_hash(0,(ct)/3,Code,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(mgsc,Code) :-
  !, dynamic_bind_mgsat(Code,CodeMid),
  multi_hash(0,(bind_mgsat)/3,CodeMid,[end_of_file]).
alec_catch_hook(mgsat,Code) :-
  !,findall((bind_mgsat(T,FS,Int) :- OfflineGoal),
            bind_mgsat_offline(T,FS,Int,OfflineGoal),Code,[end_of_file]),
  abolish((bind_mgsat)/3).
alec_catch_hook(deref,Code) :-
  !,multi_hash(0,(deref)/4,Code,[end_of_file]).
alec_catch_hook(addtype,[(:- discontiguous add_to_type/4)|Code]) :-
  !,multi_hash(1,(add_to_type)/4,Code,[end_of_file]).
alec_catch_hook(atd,Code) :-
  !,compile_add_to_typed3(Code,[end_of_file]).
%alec_catch_hook(featval,[(:- discontiguous featval/5)|Code]) :-
%  !,multi_hash(1,(featval)/5,Code,[end_of_file]).
%alec_catch_hook(fvd,Code) :-
%  !,compile_featvald3(Code,[end_of_file]).
alec_catch_hook(u,[(:- discontiguous u/6)|Code]) :-
  !,multi_hash(1,(u)/6,Code,[end_of_file]).
alec_catch_hook(subsume,[(:- discontiguous subsume_type/14)|Code]) :-
  !,multi_hash(1,(subsume_type)/14,Code,[end_of_file]).
alec_catch_hook(dcs,Code) :-
  !,compile_dcs(Code,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
%  multi_hash(0,(when_approp)/2,CodeRest,[end_of_file]).
alec_catch_hook(addstore,Code) :-
  !,multi_hash(0,(add_to_store)/3,Code,CodeMid),
  multi_hash(0,(add_to_store)/2,CodeMid,CodeRest),
  multi_hash(0,(terminate_store)/1,CodeRest,[end_of_file]).
alec_catch_hook(lexrules,Code) :-
  !,multi_hash(0,(lex_rule)/8,Code,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(forall_lex,Code) :-
  !,multi_hash(0,(forall_lex)/3,Code,CodeMid),
  multi_hash(0,(apply_forall_lex)/2,CodeMid,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(forall_rule,Code) :-
  !,multi_hash(0,(forall_rule)/4,Code,CodeMid),
  multi_hash(0,(apply_forall_rule)/3,CodeMid,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(forall_lex_rule,Code) :-
  !,multi_hash(0,(forall_lex_rule)/6,Code,CodeMid),
  multi_hash(0,(apply_forall_lex_rule)/5,CodeMid,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(lex,Code) :-
  !,(ale_flag(lexicon,consult)
     -> (Code = [(:- multifile (lex)/2),(:- dynamic (lex)/2)|CodeMid])
      ; (Code = CodeMid)),
  multi_hash(0,(lex)/2,CodeMid,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(empty,Code) :-
  !,%(ale_flag(lexicon,consult)
    % -> (Code = [(:- multifile (empty_cat)/4),
    %             (:- dynamic (empty_cat)/4)|CodeRest])
    %  ; (Code = CodeRest)),
  multi_hash(0,(empty_cat)/5,Code,[end_of_file]).
alec_catch_hook(rules,Code) :-
  !, multi_hash(0,(rule)/6,Code,CodeMid),
  multi_hash(0,(try_rule)/6,CodeMid,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(chain,Code) :-
  !,multi_hash(0,(chain_rule)/8,Code,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(chained,Code) :-
  !,multi_hash(0,(chained)/4,Code,[end_of_file]).
alec_catch_hook(nochain,Code) :-
  !,multi_hash(0,(non_chain_rule)/4,Code,CodeRest),
  generate_wpreds(CodeRest,[end_of_file]).
alec_catch_hook(generate,Code) :-
  !,multi_hash(0,(generate)/3,Code,[end_of_file]).
%alec_catch_hook(_,Code) :-
%  retract(ale_compiling(_)),
%  (Code = end_of_file).

compile_gram(File) :-
  abolish_preds,
  reconsult(File),
  compile_gram.

abolish_preds :-
  static_abolish((empty)/1), static_abolish((rule)/2), static_abolish((lex_rule)/2), 
  static_abolish(('--->')/2), static_abolish((sub)/2), 
  static_abolish((if)/2), static_abolish((macro)/2), 
  static_abolish((ext)/1), static_abolish((cons)/2),
  static_abolish((intro)/2),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  static_abolish((semantics)/1),
  static_abolish(('+++>')/2), static_abolish((fun)/1),
  static_abolish((forall)/2),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(all)) ; true).

compile_gram :-
  clear_index,
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_sig_act,
  compile_fun_act,
  compile_macro_act,
  compile_cons_act,
  compile_logic_act,
  compile_subsume_act,
  compile_dcs_act,
  compile_mgsat_act,
  compile_grammar_act,
  retract(ale_compiling(_)),
  ( current_predicate(compile_gram_hook,compile_gram_hook) -> call_all(compile_gram_hook) ; true).

compile_sig(File):-
  abolish((sub)/2),abolish((ext)/1),
  abolish((intro)/2),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(sig)) ; true),
  reconsult(File),
  compile_sig.

compile_sig:-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_sig_act,
  retract(ale_compiling(_)).

compile_sig_act :-
  compile_sub_type_act(_,_,_,_), % (SortedSubIntros,SortedIntros,SortedExts,STMatrix),
  compile_approp_act, % (SortedSubIntros,SortedIntros,STMatrix),
  compile_extensional_act, % (SortedExts).
  compile_modules_act,
  ( ale_flag(subtypecover,on) -> compile_deranged_act ; true),
  ( current_predicate(compile_sig_hook,compile_sig_hook) -> call_all(compile_sig_hook) ; true).

compile_sub_type(File):-
  abolish((sub)/2),abolish((intro)/2),
  reconsult(File),
  compile_sub_type.

compile_sub_type :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_sub_type_act(_,_,_,_),
  retract(ale_compiling(_)).  

compile_sub_type_act(SortedSubIntros,SortedIntros,SortedExts,STMatrix) :-
  alec_announce('Compiling type unification...'),
  abolish((unify_type)/3), retractall(sub_rhstype(_)),
  retractall(ext_or_intro_rhstype(_)), retractall(type_num(_,_)),
  retractall(num_type(_,_)), retractall(stmatrix_num(_,_)),
  retractall(stmatrix_dim(_)),
% PHASE 0:  1) Prolog hygiene,
%           2) check that bot and a_/1 atoms are not abused,
%           3) sort sub/intro/ext declarations, warn on RHS duplicates,
%              throw exception on LHS duplicates,
%           4) tabulate types on RHSs of sub/intro/ext declarations
  ((ale(no_types_defined) new_if_warning_else_fail
    (\+current_predicate(sub,(_ sub _)),
     \+current_predicate(intro,(_ intro _)))) -> MarkedSortedSubs = [], 
                                               SortedIntros = []
  ; verify_sub_declarations(MarkedSortedSubs),
    verify_intro_declarations(SortedIntros)
  ),
  verify_ext_declaration(SortedExts),

% PHASE 1: 1) collect default minimal types (RHS of intro or ext or any LHS
%                                            but not RHS of sub),
%          2) collect default maximal types (LHS of intro or any RHS
%                                            but not LHS of sub),
%          3) build subtyping adjacency graph from sorted sub declarations,
%          4) warn on unary branches,
%          5) remove bot from subtyping graph - can be handled specially.
  strip_subs(MarkedSortedSubs,SortedSubLHSs,SortedSubs,SortedSubIntros),
  strip_keys_filter_subrhs(SortedIntros,SortedIntroLHSs),
  ord_union(SortedIntroLHSs,SortedSubLHSs,SortedLHSDefMins),
  esetof(Min,(clause(ext_or_intro_rhstype(Min),true),
              \+ clause(sub_rhstype(Min),true)),SortedRHSDefMins),
  ord_union(SortedLHSDefMins,SortedRHSDefMins,SortedDefMins),
  ( select(bot-DeclaredMins,SortedSubs,SortedMinSubs)
  -> ord_subtract(SortedDefMins,DeclaredMins,ImplicitMins)
  ; SortedMinSubs = SortedSubs,
    ImplicitMins = SortedDefMins
  ),
  ale(implicit_mins(ImplicitMins)) new_if_warning (ImplicitMins \== []),
  esetof(Max,defmax(Max),SortedDefMaxs),
  add_vertices(SortedMinSubs,SortedDefMaxs,SubGraph),
  ale(implicit_maxs(SortedDefMaxs)) new_if_warning (SortedDefMaxs \== []),

% PHASE 2: 1) topologically sort vertices of subtyping graph,
%          2) translate graph to topologically ordered numerical indices
%             and reflexively close (resulting graph is an upper-triangular
%             Boolean matrix),
%          3) transitively close graph, yielding subtype matrix,
%          4) extract and assert rows of subtype matrix.
  ( top_sort(SubGraph,TopSortedTypes) -> true
  ; member(T-Neibs,SubGraph),
    member(S,Neibs),
    min_path(S,T,SubGraph,Path,_),
    raise_exception(ale(subtype_cycle(T,[T|Path])))
  ),

  num_types(TopSortedTypes,1,DimPlus1),  % bot is number 0
  Dim is DimPlus1 - 1,
  seed_refl_close_zmatrix(SubGraph,Dim,SubMatrix),

  upper_tri_trans_close(Dim,SubMatrix,STMatrix),
  
  length(RowMatrix,Dim),
  rconvert_stm(STMatrix,RowMatrix,1,Dim,Dim),
  hash_stm_rows(RowMatrix,1),
  assert(stmatrix_dim(Dim)),

% PHASE 3: compile unify_type/3
  assert(alec(unifytype)),
  \+ \+ consult('.alec_throw').
  

verify_sub_declarations(MarkedSortedSubs) :-
  ( current_predicate(sub,(_ sub _))
  -> findall(S-SubRHS,
     ((S sub Ss),
     % Error checks invariant to structure of Ss:
      ( var(S) -> raise_exception(ale(sub_lhs_var((S sub Ss))))
      ; functor(S,a_,1) -> raise_exception(ale(sub_lhs_abar))
      ; atom(S) -> true
      ; raise_exception(ale(sub_lhs_other(S)))
      ),
     % Error checks for combined sub/intro declarations:
      ( Ss = (Ts intro FRs) ->
        ((S = bot, FRs \== []) -> raise_exception(ale(bot_feats((S sub Ss))))
        ; verify_subtype_list(Ts,S,(S sub Ss),2,SortedSs),
          verify_featrestr_list(FRs,(S sub Ss),3),
          SubRHS = intro(SortedSs,FRs)
        )
     % Error checks for simple sub declarations
      ; % Ss is list of types
        verify_subtype_list(Ss,S,(S sub Ss),2,SortedSs),
        SubRHS = SortedSs
      )
     ),MarkedSubs)
  ; MarkedSubs = []
  ),
  keysort(MarkedSubs,MarkedSortedSubs),      % sort, but dups are still there
  no_duplicates_ksorted(MarkedSortedSubs,
         dup(L1,_,R1,R2,A1,A2,
             ((functor(R1,intro,2) -> arg(1,R1,A1) ; A1 = R1),
              (functor(R2,intro,2) -> arg(1,R2,A2) ; A2 = R2)),
             duplicate_decl(sub(L1,R1)),
             ale(duplicate_sub(L1)))).

verify_intro_declarations(SortedIntros) :-
  ( current_predicate(intro,(_ intro _)) ->
    findall(S-FRs,
     ((S intro FRs),
      ( var(S) -> raise_exception(ale(intro_lhs_var((S intro FRs))))
      ; functor(S,a_,1) -> raise_exception(ale(intro_lhs_abar))
      ; (S = bot, FRs \== []) -> 
                       raise_exception(ale(bot_feats((S intro FRs))))
      ; atom(S) -> true
      ; raise_exception(ale(intro_lhs_other(S)))
      ),    
      verify_featrestr_list(FRs,(S intro FRs),2)
     ),Intros)
  ; Intros = []
  ),
  keysort(Intros,SortedIntros).          % sort, but dups are still there

verify_ext_declaration(SortedExts) :-
  current_predicate(ext,ext(_))
  -> ( exactly_once(Es1,ext(Es1),AllEs,ale(duplicate_ext(AllEs)))
     -> verify_exttype_list(Es1,ext(Es1),1,SortedExts)
     ; true
     )
  ; SortedExts = [].

verify_subtype_list(Ss,LHS,Clause,ArgNo,SortedSs) :-
  is_list(Ss) -> 
    sort_no_dups(Ss,SortedSs,Clause,ArgNo),
    ( member(T,SortedSs), % failure-drive through list to check arguments
      ( var(T) -> raise_exception(ale(sub_rhs_var(Clause)))
      ; (T = bot) -> raise_exception(ale(bot_subsumed(LHS)))
      ; functor(T,a_,1) -> raise_exception(ale(abar_subsumed(LHS)))
      ; atom(T) -> assert(sub_rhstype(T))
      ; raise_exception(ale(sub_rhs_other(LHS,T)))
      ),
      fail
    ; true
    )
  ; raise_exception(ale(sub_rhs_notlist(Clause,Ss))).

verify_exttype_list(Ss,Clause,ArgNo,SortedSs) :-
  is_list(Ss) -> 
    sort_no_dups(Ss,SortedSs,Clause,ArgNo),
    ( member(T,SortedSs), % failure-drive through list to check arguments
      ( var(T) -> raise_exception(ale(ext_rhs_var(Clause)))
      ; (T == bot) -> raise_exception(ale(bot_ext))
      ; functor(T,a_,1) -> (abar_ext(Clause) warning)
      ; atom(T) ->  assert(ext_or_intro_rhstype(T))
      ; raise_exception(ale(ext_rhs_other(T)))
      ),
      fail
    ; true
    )
  ; raise_exception(ale(ext_rhs_notlist(Clause,Ss))).

verify_featrestr_list(FRs,Clause,ArgNo) :-
  ( is_list(FRs) -> % check intro component
    ( member(FR,FRs), % failure-drive through list to check arguments
      ( var(FR) -> raise_exception(ale(intro_rhs_var(Clause)))
      ; (FR = (F:R)) ->
          ( atom(F) -> true
          ; raise_exception(ale(feat_notatom(F,Clause)))
          ),
          ( atom(R) -> (R \== bot -> assert(ext_or_intro_rhstype(R)) ; true)
          ; var(R) -> raise_exception(ale(intro_vr_var(Clause)))
                       % R can be a variable if parametric types are added
          ; (R = (a_ X)) -> ale(cyclic_abar_restriction(F,R,Clause,ArgNo))
	                      if_error cyclic_term(X),
	                    ground_abar_restriction(F,R,Clause,ArgNo) 
                              new_if_warning ground(X)
          ; raise_exception(ale(vr_other(R,Clause)))
          )
      ; raise_exception(ale(fr_other(FR,Clause)))
      ),
      fail
    ; true
    )
  ; raise_exception(ale(intro_rhs_notlist(Clause,FRs)))
  ).

% ------------------------------------------------------------------------------
% sort_no_dups(+List,-Sorted,+Clause,+ArgNo)
% ------------------------------------------------------------------------------
% Sorted is the result of sorting List and removing duplicates.  If a duplicate
%  is found, a warning (duplicate_types/3) is issued with a pointer to argument
%  number ArgNo of user-defined Clause.
% This code is based on the Edinburgh Prolog standard.
% ------------------------------------------------------------------------------
sort_no_dups(List,Sorted,Clause,ArgNo) :-
  sort_no_dups(List,-1,S,[],Clause,ArgNo),
  Sorted = S.

sort_no_dups([],_,[],[],_,_).
sort_no_dups([Head|Tail],Lim,Sorted,Rest,Clause,ArgNo) :-
  samrun_no_dups(Tail,[Head|T],Head,T,Run,Rest0,Clause,ArgNo),
  sort_no_dups(Rest0,1,Lim,Run,Sorted,Rest,Clause,ArgNo).

sort_no_dups([Head|Tail],J,Lim,Run0,Sorted,Rest,Clause,ArgNo) :-
  J =\= Lim, !,
  samrun_no_dups(Tail,[Head|T],Head,T,Run1,Rest0,Clause,ArgNo),
  sort_no_dups(Rest0,1,J,Run1,Run2,Rest1,Clause,ArgNo),
  merge_no_dups(Run0,Run2,Run,Clause,ArgNo),
  K is J<<1,
  sort_no_dups(Rest1,K,Lim,Run,Sorted,Rest,Clause,ArgNo).
sort_no_dups(Rest,_,_,Sorted,Sorted,Rest,_,_).

% ------------------------------------------------------------------------------
% samrun_no_dups(List,Q1,Q2,End,Run,Rest,Clause,ArgNo)
% ------------------------------------------------------------------------------
% List is a list of elements, Rest is some tail of that list,
% Run is an ordered _set_ of the difference between List and Rest,
% Q1 is the ./2 cell containing the first element of List.
% Q2 is the last element of Run.
% End is the tail of Run.
% ------------------------------------------------------------------------------
samrun_no_dups([],Run,_,[],Run,[],_,_).
samrun_no_dups([Head|Tail],Begin,Last,End,Run,Rest,Clause,ArgNo) :-
  compare(X,Head,Last),
  samrunt_no_dups(X,Head,Tail,Begin,Last,End,Run,Rest,Clause,ArgNo).

samrunt_no_dups(>,Head,Tail,Begin,_,[Head|NewEnd],Run,Rest,Clause,ArgNo) :-
  samrun_no_dups(Tail,Begin,Head,NewEnd,Run,Rest,Clause,ArgNo).
samrunt_no_dups(=,_,Tail,Begin,Last,End,Run,Rest,Clause,ArgNo) :-
  (duplicate_types(Last,Clause,ArgNo) warning),
  samrun_no_dups(Tail,Begin,Last,End,Run,Rest,Clause,ArgNo).
samrunt_no_dups(<,Head,Tail,Begin,Last,End,Run,Rest,Clause,ArgNo) :-
  Begin = [First|_],
  compare(X,Head,First),
  samrunh_no_dups(X,Head,Tail,Begin,Last,End,Run,Rest,Clause,ArgNo).

samrunh_no_dups(<,Head,Tail,Begin,Last,End,Run,Rest,Clause,ArgNo) :-
  samrun_no_dups(Tail,[Head|Begin],Last,End,Run,Rest,Clause,ArgNo).
samrunh_no_dups(=,Head,Tail,Begin,Last,End,Run,Rest,Clause,ArgNo) :-
  (duplicate_types(Head,Clause,ArgNo) warning),
  samrun_no_dups(Tail,Begin,Last,End,Run,Rest,Clause,ArgNo).
samrunh_no_dups(>,Head,Tail,Run,_,[],Run,[Head|Tail],_,_).

% ------------------------------------------------------------------------------
% merge_no_dups/5
% ------------------------------------------------------------------------------
% like SICStus ord_union/3 but warns on duplicates
% ------------------------------------------------------------------------------
merge_no_dups([],Set,Set,_,_).
merge_no_dups([O|Os],Ns,Set,Clause,ArgNo) :-
  merge_no_dups(Ns,O,Os,Set,Clause,ArgNo).

merge_no_dups([],O,Os,[O|Os],_,_).
merge_no_dups([N|Ns],O,Os,Set,Clause,ArgNo) :-
  compare(C,O,N), 
  merge_no_dups(C,O,Os,N,Ns,Set,Clause,ArgNo).

merge_no_dups(<,O1,Os,N,Ns,[O1|Set],Clause,ArgNo) :-
  merge_no_dups(Os,N,Ns,Set,Clause,ArgNo).
merge_no_dups(=,_,Os,N,Ns,[N|Set],Clause,ArgNo) :-
  (duplicate_types(N,Clause,ArgNo) warning),
  merge_no_dups(Os,Ns,Set,Clause,ArgNo).
merge_no_dups(>,O,Os,N1,Ns,[N1|Set],Clause,ArgNo) :-
  merge_no_dups(Ns,O,Os,Set,Clause,ArgNo).

% ------------------------------------------------------------------------------
% strip_subs(+MarkedSortedSubs,-SortedSubLHSs,-SortedSubs,-SortedSubIntros)
% ------------------------------------------------------------------------------
% This predicate triages MarkedSortedSubs into sub/2 declarations with
%  (SortedSubIntros) and without (SortedSubs) the optional intro/2 modifier.
%  SortedSubLHSs is a list of the types that occur on the LHS of either kind
%  of declaration but are not found on the RHS of a sub/2 declaration.
% ------------------------------------------------------------------------------
strip_subs([],[],[],[]).
strip_subs([TS-MRHS|MSSubs],SubLHSs,[TS-Ss|Subs],SubIntros) :-
  ( functor(MRHS,intro,2)
  -> arg(1,MRHS,Ss), arg(2,MRHS,FRs),
     SubIntros = [TS-FRs|SubIntrosRest]
  ; MRHS = Ss, SubIntros = SubIntrosRest
  ),
  ale(unary_branch(TS,U)) new_if_warning (Ss = [U]),
  ( clause(sub_rhstype(TS),true) -> SubLHSs = SubLHSsRest
  ; TS = bot -> SubLHSs = SubLHSsRest
  ; SubLHSs = [TS|SubLHSsRest]
  ),
  strip_subs(MSSubs,SubLHSsRest,Subs,SubIntrosRest).

% ------------------------------------------------------------------------------
% strip_keys_filter_subrhs(+KeyedList,-List)
% ------------------------------------------------------------------------------
% List is KeyedList without its keys.
% ------------------------------------------------------------------------------
strip_keys_filter_subrhs([],[]).
strip_keys_filter_subrhs([T-_|KeySs],LHSs) :-
  ( clause(sub_rhstype(T),true) -> LHSs = LHSsRest
  ; LHSs = [T|LHSsRest]
  ),
  strip_keys_filter_subrhs(KeySs,LHSsRest).

% ------------------------------------------------------------------------------
% defmax(?Max)
% ------------------------------------------------------------------------------
% Max is a default maximally specific type.
% ------------------------------------------------------------------------------
defmax(Max) :-
  current_predicate(sub,(_ sub _))
  -> ( clause(sub_rhstype(Max),true)
     ; clause(ext_or_intro_rhstype(Max),true)
     ; current_predicate(intro,(_ intro _)) -> (Max intro _)
     ),
     \+ (Max sub _)
  ; ( clause(sub_rhstype(Max),true)
    ; clause(ext_or_intro_rhstype(Max),true)
    ; current_predicate(intro,(_ intro _)) -> (Max intro _)
    ).

% ------------------------------------------------------------------------------
% no_duplicates_ksorted(+KeyedList,dup(-K1,-K2,-RHS1,-RHS2,?Arg1,?Arg2,+ArgBindGoal,
%                                      +Warning,+Exception))
% ------------------------------------------------------------------------------
% For every pair of adjacent keys on KeyedList, K1 and K2, with right-hand-sides
%  RHS1 and RHS2, if K1 = K2 and ArgBindGoal is true, then Warning is issued (if
%  Arg1 and Arg2 are variants) or Exception is raised (not variants).  Typically,
%  ArgBindGoal, Warning and Exception contain one or more of K1, K2, RHS1, RHS2,
%  Arg1 or Arg2 upon invocation.
% ------------------------------------------------------------------------------
no_duplicates_ksorted([],_).
no_duplicates_ksorted([T-RHS|Ks],Dup) :-
  no_duplicates_ksorted_act(Ks,T,RHS,Dup).
no_duplicates_ksorted_act([],_,_,_).
no_duplicates_ksorted_act([T2-RHS2|Ks],T1,RHS1,Dup) :-
 T1 = T2
 -> \+ \+ (Dup = dup(T1,T2,RHS1,RHS2,Arg1,Arg2,ArgBindGoal,Warning,Exception),
           call(ArgBindGoal),
           ( Warning new_if_warning_else_fail variant(Arg1,Arg2)
           -> true
           ; raise_exception(Exception)
           )
          )
 ; no_duplicates_ksorted_act(Ks,T2,RHS2,Dup).

% ------------------------------------------------------------------------------
% has_duplicates(+List)
% ------------------------------------------------------------------------------
% List has duplicate member (according to ==).
% ------------------------------------------------------------------------------
has_duplicates(List) :-
  length(List,N),
  sort(List,Sorted),
  length(Sorted,SN),
  SN < N.

% ------------------------------------------------------------------------------
% exactly_once(-Sol,+Goal,-AllSolutions,+Exception)
% ------------------------------------------------------------------------------
% Goal succeeds exactly once with Sol.  If it does not succed, then fail.  If
%  it succeeds more than once, then AllSolutions are the solutions and Exception
%  is raised.
% ------------------------------------------------------------------------------
% fail if 0, succeed if 1, throw exception if >1.
exactly_once(Sol,Goal,AllSols,Exception) :-
  findall(Sol,call(Goal),AllSols),
  ( AllSols == [] -> fail
  ; AllSols = [Sol] -> true
  ; raise_exception(Exception)
  ).

% ------------------------------------------------------------------------------
% num_types(+Types,+In:<int>,-Out:<int>)
% ------------------------------------------------------------------------------
% Types is sorted in topological order.  Its members are assigned the integers
%  from In (inclusive) to Out (exclusive).
% ------------------------------------------------------------------------------
num_types([],N,N).
num_types([T|Types],NIn,NOut) :-
  assertz(type_num(T,NIn)),
  assertz(num_type(NIn,T)),
  NMid is NIn + 1,
  num_types(Types,NMid,NOut).

% ==============================================================================
% ZCQ MATRIX ARITHMETIC
% ==============================================================================

% ------------------------------------------------------------------------------
% seed_refl_close_zmatrix(+RowGraph,+Dim,-ZM)
% ------------------------------------------------------------------------------
% Build a Dim x Dim ZCQ matrix from its row-indexed representation, and 
%  reflexively close it.
% ------------------------------------------------------------------------------
seed_refl_close_zmatrix([],_,_).
seed_refl_close_zmatrix([T-Neibs|GraphRest],Dim,ZM) :-
  clause(type_num(T,N),true),
  seed_elt_zcu(N,N,Dim,ZM),  % reflexive closure occurs here
  seed_row_zmatrix(Neibs,N,GraphRest,Dim,ZM).

seed_row_zmatrix([],_,GraphRest,Dim,ZM) :-
  seed_refl_close_zmatrix(GraphRest,Dim,ZM).
seed_row_zmatrix([T|Neibs],N,GraphRest,Dim,ZM) :-
  clause(type_num(T,M),true),
  seed_elt_zcu(N,M,Dim,ZM),
  seed_row_zmatrix(Neibs,N,GraphRest,Dim,ZM).

% ------------------------------------------------------------------------------
% seed_elt_zcu(+I,+J,+Dim,?ZM)
% ------------------------------------------------------------------------------
% Place a 1 in ZM[I,J].  ZM is Dim x Dim.
% Preconditions: 1) 1 <= I <= Dim,
%            and 2) 1 <= J <= Dim.
% ------------------------------------------------------------------------------
seed_elt_zcu(1,J,Dim,ZM) :-
  !,seed_elt_zcu1(J,Dim,ZM).
seed_elt_zcu(I,J,Dim,zcu(A,B,C)) :-
  D2 is (Dim+1) >> 1,
  ( I > D2 -> NewI is I - D2, NewJ is J - D2,
              NewDim is Dim - D2,
              seed_elt_zcu(NewI,NewJ,NewDim,C)
  ; J > D2 -> NewJ is J - D2, CDim is Dim - D2,
              seed_elt_zmatrix(I,NewJ,D2,CDim,B)
  ; seed_elt_zcu(I,J,D2,A)
  ).

seed_elt_zcu1(1,Dim,ZM) :-
  !,seed_origin_zcu(Dim,ZM).
seed_elt_zcu1(J,Dim,zcu(A,B,_)) :-
  D2 is (Dim+1) >> 1,
  ( J > D2 -> NewJ is J - D2, CDim is Dim - D2,
              seed_elt_zmatrix1(NewJ,D2,CDim,B)
  ; seed_elt_zcu1(J,D2,A)
  ).  

seed_origin_zcu(1,1) :- !.
seed_origin_zcu(Dim,zcu(A,_,_)) :-
  NewDim is (Dim+1) >> 1,
  seed_origin_zcu(NewDim,A).

% ------------------------------------------------------------------------------
% seed_elt_zmatrix(I,J,RDim,CDim,ZM)
% ------------------------------------------------------------------------------
% Place a 1 in ZM[I,J].  ZM is a RDim x Cdim submatrix.
% Preconditions: 1) 1 <= I <= RDim,
%                2) 1 <= J <= CDim,
%            and 3) either RDim==CDim or they differ by 1
% ------------------------------------------------------------------------------
seed_elt_zmatrix(1,J,RDim,CDim,ZM) :-
  !,seed_elt_zmatrix1(J,RDim,CDim,ZM).
seed_elt_zmatrix(2,J,RDim,CDim,ZM) :-
  !,seed_elt_zmatrix2(J,RDim,CDim,ZM).
seed_elt_zmatrix(I,J,RDim,CDim,zcm(A,B,D,C)) :-
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  ( I > RD2 -> ( J > CD2 -> NewI is I - RD2, NewJ is J-CD2,
                            NewRDim is RDim - RD2, NewCDim is CDim - CD2,
                            seed_elt_zmatrix(NewI,NewJ,NewRDim,NewCDim,C)
	       ; NewI is I - RD2, NewRDim is RDim - RD2,
		 seed_elt_zmatrix(NewI,J,NewRDim,CD2,D)
               )
  ; J > CD2 -> NewJ is J - CD2, NewCDim is CDim - CD2,
               seed_elt_zmatrix(I,NewJ,RD2,NewCDim,B)
  ; seed_elt_zmatrix(I,J,RD2,CD2,A)
  ).

seed_elt_zmatrix1(1,RDim,CDim,ZM) :-
  !,seed_origin_zmatrix(RDim,CDim,ZM).
seed_elt_zmatrix1(2,RDim,CDim,ZM) :-
  !,seed_elt_zmatrix12(RDim,CDim,ZM).
seed_elt_zmatrix1(J,RDim,CDim,zcm(A,B,_,_)) :-
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  ( J > CD2 -> NewJ is J - CD2, NewCDim is CDim - CD2,
               seed_elt_zmatrix1(NewJ,RD2,NewCDim,B)
  ; seed_elt_zmatrix1(J,RD2,CD2,A)
  ).  

seed_elt_zmatrix2(1,RDim,CDim,ZM) :-
  !,seed_elt_zmatrix21(CDim,RDim,ZM). % swap column and row dimensions
seed_elt_zmatrix2(2,RDim,CDim,ZM) :-
  !,seed_elt_zmatrix22(RDim,CDim,ZM).
seed_elt_zmatrix2(3,RDim,CDim,ZM) :-
  !,seed_elt_zmatrix23(RDim,CDim,ZM).
seed_elt_zmatrix2(J,RDim,CDim,zcm(A,B,_,_)) :- % J > 3, so CDim > 3, so RDim > 2
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  ( J > CD2 -> NewJ is J - CD2, NewCDim is CDim - CD2,
               seed_elt_zmatrix2(NewJ,RD2,NewCDim,B)
  ; seed_elt_zmatrix2(J,RD2,CD2,A)
  ).

% column and row dimensions swapped
seed_elt_zmatrix21(1,_2,zc21(_,1)) :- !.
seed_elt_zmatrix21(2,RDim,ZM) :-
  !,seed_elt_zmatrix21_x2(RDim,ZM).
seed_elt_zmatrix21(3,RDim,ZM) :-
  !,seed_elt_zmatrix21_x3(RDim,ZM).
seed_elt_zmatrix21(CDim,RDim,zcm(A,_,_,_)) :-  % CDim > 3, so RDim > 2
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  seed_elt_zmatrix21(CD2,RD2,A).

seed_elt_zmatrix21_x2(2,zcm(_,_,1,_)).
seed_elt_zmatrix21_x2(3,zcm(zc21(_,1),_,_,_)).

seed_elt_zmatrix21_x3(2,zcm(_,_,zc12(1,_),_)) :- !.
seed_elt_zmatrix21_x3(_3or4,zcm(zcm(_,_,1,_),_,_,_)).
		   
seed_elt_zmatrix22(2,CDim,ZM) :-
  !,seed_elt_zmatrix22_2(CDim,ZM).
seed_elt_zmatrix22(3,CDim,ZM) :-
  !,seed_elt_zmatrix22_3(CDim,ZM).
seed_elt_zmatrix22(RDim,CDim,zcm(A,_,_,_)) :-  % RDim > 3, so CDim > 2
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  seed_elt_zmatrix22(RD2,CD2,A).

seed_elt_zmatrix22_2(2,zcm(_,_,_,1)).
seed_elt_zmatrix22_2(3,zcm(_,_,zc12(_,1),_)).

seed_elt_zmatrix22_3(2,zcm(_,zc21(_,1),_,_)) :- !.
seed_elt_zmatrix22_3(_3or4,zcm(zcm(_,_,_,1),_,_,_)).

seed_elt_zmatrix23(2,_3,zcm(_,_,_,1)) :- !.  % probably should have column-indexed
seed_elt_zmatrix23(3,CDim,ZM) :-             %  this one like seed_elt_zmatrix21/3.
  !,seed_elt_zmatrix23_3(CDim,ZM).
seed_elt_zmatrix23(4,CDim,ZM) :-
  !,seed_elt_zmatrix23_4(CDim,ZM).
seed_elt_zmatrix23(5,CDim,ZM) :-
  !,seed_elt_zmatrix23_5(CDim,ZM).
seed_elt_zmatrix23(RDim,CDim,zcm(A,_,_,_)) :- % RDim > 5, so CDim > 4
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  seed_elt_zmatrix23(RD2,CD2,A).

seed_elt_zmatrix23_3(3,zcm(_,zc21(_,1),_,_)).
seed_elt_zmatrix23_3(4,zcm(_,zcm(_,_,1,_),_,_)).

seed_elt_zmatrix23_4(3,zcm(_,zc21(_,1),_,_)).
seed_elt_zmatrix23_4(4,zcm(_,zcm(_,_,1,_),_,_)).
seed_elt_zmatrix23_4(5,zcm(zcm(_,_,_,1),_,_,_)).

seed_elt_zmatrix23_5(4,zcm(_,zcm(zc21(_,1),_,_,_),_,_)) :- !.
seed_elt_zmatrix23_5(_5or6,zcm(zcm(_,zc21(_,1),_,_),_,_,_)).

seed_origin_zmatrix(1,CDim,ZM) :-
  !,seed_origin_zmatrix1(CDim,ZM).
seed_origin_zmatrix(2,CDim,ZM) :-
  !,seed_origin_zmatrix2(CDim,ZM).
seed_origin_zmatrix(RDim,CDim,zcm(A,_,_,_)) :-
  NewRDim is (RDim+1) >> 1,
  NewCDim is (CDim+1) >> 1,
  seed_origin_zmatrix(NewRDim,NewCDim,A).

seed_origin_zmatrix1(1,1).
seed_origin_zmatrix1(2,zc12(1,_)).

seed_origin_zmatrix2(1,zc21(1,_)).
seed_origin_zmatrix2(2,zcm(1,_,_,_)).
seed_origin_zmatrix2(3,zcm(zc12(1,_),_,_,_)).

seed_elt_zmatrix12(1,_2,zc12(_,1)) :- !.
seed_elt_zmatrix12(2,CDim,ZM) :-
  !,seed_elt_zmatrix12_2(CDim,ZM).
seed_elt_zmatrix12(3,CDim,ZM) :-
  !,seed_elt_zmatrix12_3(CDim,ZM).
seed_elt_zmatrix12(RDim,CDim,zcm(A,_,_,_)) :-  % RDim > 3, therefore CDim > 2
  RD2 is (RDim+1) >> 1,
  CD2 is (CDim+1) >> 1,
  seed_elt_zmatrix12(RD2,CD2,A).

% CDim==1 not possible: we asked for I==1,J==2
seed_elt_zmatrix12_2(2,zcm(_,1,_,_)).
seed_elt_zmatrix12_2(3,zcm(zc12(_,1),_,_,_)).

seed_elt_zmatrix12_3(2,zcm(_,zc21(1,_),_,_)) :- !.
seed_elt_zmatrix12_3(_3or4,zcm(zcm(_,1,_,_),_,_,_)).

% ------------------------------------------------------------------------------
% upper_tri_trans_close(+Dim,+Matrix,-StarMatrix)
% ------------------------------------------------------------------------------
% StartMatrix is transitive closure of Matrix.  Matrix has 1s on its diagonal,
%   and is upper-triangular.  Both Matrix and StartMatrix are Dim x Dim.
% In a Boolean semiring: (A B) = (A* A*BC*)
%                        (0 C) = (0    C* )
% ------------------------------------------------------------------------------
upper_tri_trans_close(1,ZM,ZM) :- !.
upper_tri_trans_close(Dim,zcu(A,B,C),zcu(AStar,D,CStar)) :-
  ADim is (Dim+1) >> 1,
  CDim is Dim - ADim,
  upper_tri_trans_close(ADim,A,AStar),
  upper_tri_trans_close(CDim,C,CStar),
  mult_um(B,AStar,AStarB),
  mult_mu(AStarB,CStar,D).

% calcuate C = A*B, A is upper-triangular with 1s on diagonal
% (AA AB) (BA BB) = (AA*BA + AB*BD  AA*BB + AB*BC)
% ( 0 AC) (BD BC)   (    AC*BD          AC*BC    )
%
mult_um(V,_,_) :- var(V),!.
mult_um(1,A,Ac) :- copy_term(A,Ac).
mult_um(zc12(BA,BB),_1,zc12(BAc,BBc)) :- copy_term(BA,BAc), copy_term(BB,BBc).
mult_um(zc21(BA,BD),zcu(_1,AB,_Also1),C) :-
    var(AB) -> ( (var(BA),var(BD)) -> true ; copy_term(BA,BAc),
		                             copy_term(BD,BDc),
		                             C = zc21(BAc,BDc))
  ; BA == 1 -> copy_term(BD,BDc), C = zc21(1,BDc)
  ; BD == 1 -> copy_term(BD,BDc), C = zc21(1,BDc)
  ; (var(BD) -> true ; C = zc21(_,1)).
    
mult_um(zcm(BA,BB,BD,BC),zcu(AA,AB,AC),C) :-
  mult_um(BA,AA,CA1),  % A can't be 0, zc12 or zc21, and because 
  mult_mm(AB,BD,CA2),  %  B is not 0, 1 or zc12, A can't be 1
  CA1 = CA2,  % sum(CA1,CA2,CA),
  mult_um(BB,AA,CB1),
  mult_mm(AB,BC,CB2),
  CB1 = CB2,  % sum(CB1,CB2,CB),
  mult_um(BD,AC,CD),
  mult_um(BC,AC,CC),
  ( (var(CA1),var(CB1),var(CD),var(CC)) -> true % C = 0
  ; C = zcm(CA1,CB1,CD,CC)
  ).

% calcuate C = A*B
% (AA AB) (BA BB) = (AA*BA + AB*BD  AA*BB + AB*BC)
% (AD AC) (BD BC)   (AD*BA + AC*BD  AD*BB + AC*BC)
%
mult_mm(V,_,_) :- var(V),!.
mult_mm(1,B,Bc) :- copy_term(B,Bc).
mult_mm(zc21(AA,AD),B,C) :-
  mult_mm_zc21(B,AA,AD,C).
mult_mm(zc12(AA,AB),B,C) :-
  mult_mm_zc12(B,AA,AB,C).
mult_mm(zcm(AA,AB,AD,AC),B,C) :-
  mult_mm_zcm(B,AA,AB,AD,AC,C).

mult_mm_zc21(V,_,_,_) :- var(V),!.
mult_mm_zc21(1,CA,CD,zc21(CAc,CDc)) :- copy_term(CA,CAc), copy_term(CD,CDc).
mult_mm_zc21(zc12(BA,BB),AA,AD,C) :-
  ( var(AA) -> ( var(AD) -> true
	      ; BA == 1 -> copy_term(BB,BBc), C = zcm(_,_,1,BBc)
	      ; BB == 1 -> C = zcm(_,_,_,1)
	      ; true
	      )
  ; var(AD) -> ( BA == 1 -> copy_term(BB,BBc), C = zcm(1,BBc,_,_)
	      ; BB == 1 -> C = zcm(_,1,_,_)
	      ; true
	      )
  ; BA == 1 -> copy_term(BB,BBc), copy_term(BB,BBc2), C = zcm(1,BBc,1,BBc2)
  ; BB == 1 -> C = zcm(_,1,_,1)
  ; true
  ).

mult_mm_zc12(V,_,_,_) :- var(V),!.
mult_mm_zc12(zc21(BA,BD),AA,AB,C) :-
  var(AA) -> ( var(AB) -> true  % should we require sparseness, i.e. AA || AB?
	    ; var(BD) -> true
	    ; C = 1
	    )
  ; var(BA) -> ( var(AB) -> true
	      ; var(BD) -> true
	      ; C = 1
	      )
  ; C = 1.
mult_mm_zc12(zcm(BA,BB,BD,BC),AA,AB,C) :-
  var(AA) -> ( var(AB) -> true  % B must be 2x2, or else CDim > RDim + 1
	    ; BD == 1 -> copy_term(BC,BCc), C = zc12(1,BCc)
	    ; BC == 1 -> C = zc12(_,1)
	    ; true
	    )
  ; var(AB) -> ( BA == 1 -> copy_term(BB,BBc), C = zc12(1,BBc)
	      ; BB == 1 -> C = zc12(_,1)
	      ; true
	      )
  ; BA == 1 -> ( BB == 1 -> C = zc12(1,1)
	       ; BC == 1 -> C = zc12(1,1)
	       ; C = zc12(1,_)
	       )
  ; BD == 1 -> ( BB == 1 -> C = zc12(1,1)
	       ; BC == 1 -> C = zc12(1,1)
	       ; C = zc12(1,_)
	       )
  ; BB == 1 -> C = zc12(_,1)
  ; BC == 1 -> C = zc12(_,1)
  ; true.

mult_mm_zcm(V,_,_,_,_,_) :- var(V),!.
mult_mm_zcm(zc21(BA,BD),AA,AB,AD,AC,C) :-  % then A is 2x2
  var(BA) -> ( var(BD) -> true
	    ; AB == 1 -> copy_term(AC,ACc), C = zc21(1,ACc)
	    ; AC == 1 -> C = zc21(_,1)
	    ; true
	    )
  ; var(BD) -> ( AA == 1 -> copy_term(AD,ADc), C = zc21(1,ADc)
	      ; AD == 1 -> C = zc21(_,1)
	      ; true
	      )
  ; AA == 1 -> ( AD == 1 -> C = zc21(1,1)
	       ; AC == 1 -> C = zc21(1,1)
	       ; C = zc21(1,_)
	       )
  ; AB == 1 -> ( AD == 1 -> C = zc21(1,1)
	       ; AC == 1 -> C = zc21(1,1)
	       ; C = zc21(1,_)
	       )
  ; AD == 1 -> C = zc21(_,1)
  ; AC == 1 -> C = zc21(_,1)
  ; true.
mult_mm_zcm(zcm(BA,BB,BD,BC),AA,AB,AD,AC,C) :-	
  mult_mm(AA,BA,CA1),    
  mult_mm(AB,BD,CA2),    
  CA1 = CA2, % sum(CA1,CA2,CA),
  mult_mm(AA,BB,CB1),
  mult_mm(AB,BC,CB2),
  CB1 = CB2, % sum(CB1,CB2,CB),
  mult_mm(AD,BA,CD1),
  mult_mm(AC,BD,CD2),
  CD1 = CD2, % sum(CD1,CD2,CD),
  mult_mm(AD,BB,CC1),
  mult_mm(AC,BC,CC2),
  CC1 = CC2, % sum(CC1,CC2,CC),
  ( (var(CA1),var(CB1),var(CD1),var(CC1)) -> true % C = 0  % Remove this to make closure 5-10x slower
  ; C = zcm(CA1,CB1,CD1,CC1)            % - this keeps matrices sparse
  ).

% calcuate C = A*B, B is upper-triangular with 1s on diagonal
% (AA AB) (BA BB) = (AA*BA  AA*BB + AB*BC)
% (AD AC) (0  BC)   (AD*BA  AD*BB + AC*BC)
%
mult_mu(V,_,_) :- var(V),!.
mult_mu(1,B,Bc) :- copy_term(B,Bc).
mult_mu(zc21(AA,AD),_1,zc21(AAc,ADc)) :- copy_term(AA,AAc), copy_term(AD,ADc).
mult_mu(zc12(AA,AB),zcu(_1,BB,_Also1),C) :-
  var(BB) -> ( (var(AA),var(AB)) -> true ; copy_term(AA,AAc),
		                           copy_term(AB,ABc),
		                           C = zc12(AAc,ABc))
  ; AA == 1 -> copy_term(AA,AAc), C = zc12(AAc,1)
  ; AB == 1 -> copy_term(AA,AAc), C = zc12(AAc,1)
  ; (var(AA) -> true ; C = zc12(1,_)).
mult_mu(zcm(AA,AB,AD,AC),zcu(BA,BB,BC),C) :-
  mult_mu(AA,BA,CA),
  mult_mm(AA,BB,CB1),
  mult_mu(AB,BC,CB2),
  CB1 = CB2, % sum(CB1,CB2,CB),
  mult_mu(AD,BA,CD),
  mult_mm(AD,BB,CC1),
  mult_mu(AC,BC,CC2),
  CC1 = CC2, % sum(CC1,CC2,CC),
  ( (var(CA),var(CB1),var(CD),var(CC1)) -> true % C = 0
  ; C = zcm(CA,CB1,CD,CC1)
  ).

% calculate C = A+B
% By implementing 0 as variable, we can implement sum as
%  term unification (but then we need to copy structure rather
%  than share variables during multiplication).
%sum(0,B,B) :- !.
%sum(1,_,1) :- !.
%sum(A,B,C) :-
%    B = 0 -> C = A
%  ; sum_nozero(A,B,C).

%sum_nozero(zc12(AA,AB),zc12(BA,BB),zc12(CA,CB)) :-
%  sum(AA,BA,CA),
%  sum(AB,BB,CB).
%sum_nozero(zc21(AA,AD),zc21(BA,BD),zc21(CA,CD)) :-
%  sum(AA,BA,CA),
%  sum(AD,BD,CD).
%sum_nozero(zcm(AA,AB,AD,AC),zcm(BA,BB,BD,BC),zcm(CA,CB,CD,CC)) :-
%  sum(AA,BA,CA),
%  sum(AB,BB,CB),
%  sum(AC,BC,CC),
%  sum(AD,BD,CD).

% ------------------------------------------------------------------------------
% rconvert_stm(+ZCMatrix,-RowMatrix,+Col,+RDim,+CDim)
% ------------------------------------------------------------------------------
% Convert the RDim x CDim submatrix ZCMatrix to row-indexed form.  ZCMatrix
%  is offset by Col columns within its larger matrix.
% ------------------------------------------------------------------------------
% Precondition: RowMatrix is proper
% Postcondition: each row is proper
rconvert_stm(0,RowMatrix,_Col,_NumRows,_NumCols) :-
  !,terminate_rows(RowMatrix).
rconvert_stm(1,[[Col]],Col,_1,_Also1).
rconvert_stm(zc12(A,B),RowMatrix,Col,_1,_2) :-
  A = 0 -> ( B = 0 -> RowMatrix = [[]]
	   ; BCol is Col + 1,
	     RowMatrix = [[BCol]]
	   )
  ; ( B = 0 -> RowMatrix = [[Col]]
    ; BCol is Col + 1,
      RowMatrix = [[Col,BCol]]
    ).
rconvert_stm(zc21(A,D),RowMatrix,Col,_2,_1) :-
  A = 0 -> ( D = 0 -> RowMatrix = [[],[]]
	   ; RowMatrix = [[],[Col]]
	   )
  ; ( D = 0 -> RowMatrix = [[Col],[]]
    ; RowMatrix = [[Col],[Col]]
    ).
rconvert_stm(zcu(A,B,C),RowMatrix,Col,NumRows,NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,CRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm(B,BRowMatrix,BCCol,ABRows,BCCols),
  CRows is NumRows - ABRows,
  rconvert_stm(C,CRowMatrix,BCCol,CRows,BCCols).
rconvert_stm(zcm(A,B,D,C),RowMatrix,Col,NumRows,NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,DRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm(B,BRowMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  rconvert_stm_tail(D,DRowMatrix,CRowMatrix,Col,CDRows,ADCols),
  rconvert_stm(C,CRowMatrix,BCCol,CDRows,BCCols).

% Precondition: RowMatrix is proper
% Postcondition: TailMatrix is proper, same length as RowMatrix,
%  and contains tails of its rows
rconvert_stm_tail(0,RowMatrix,RowMatrix,_Col,_NumRows,_NumCols) :- !.
rconvert_stm_tail(1,[[Col|Tail]],[Tail],Col,_1,_Also1).
rconvert_stm_tail(zc12(A,B),RowMatrix,TailMatrix,Col,_1,_2) :-
  A = 0 -> ( B = 0 -> RowMatrix = [Tail], TailMatrix = RowMatrix
	   ; BCol is Col + 1,
	     RowMatrix = [[BCol|Tail]], TailMatrix = [Tail]
	   )
  ; ( B = 0 -> RowMatrix = [[Col|Tail]], TailMatrix = [Tail]
    ; BCol is Col + 1,
      RowMatrix = [[Col,BCol|Tail]], TailMatrix = [Tail]
    ).
rconvert_stm_tail(zc21(A,D),RowMatrix,TailMatrix,Col,_2,_1) :-
  A = 0 -> ( D = 0 -> RowMatrix = [TailA,TailD], TailMatrix = RowMatrix
	   ; RowMatrix = [TailA,[Col|TailD]], TailMatrix = [TailA,TailD]
	   )
  ; ( D = 0 -> RowMatrix = [[Col|TailA],TailD], TailMatrix = [TailA,TailD]
    ; RowMatrix = [[Col|TailA],[Col|TailD]], TailMatrix = [TailA,TailD]
    ).
rconvert_stm_tail(zcu(A,B,C),RowMatrix,TailMatrix,Col,NumRows,NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,CRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm_opentail(B,BRowMatrix,TailMatrix,CTailMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  rconvert_stm_tail(C,CRowMatrix,CTailMatrix,BCCol,CDRows,BCCols).
rconvert_stm_tail(zcm(A,B,D,C),RowMatrix,TailMatrix,Col,NumRows,NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,DRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm_opentail(B,BRowMatrix,TailMatrix,CTailMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  rconvert_stm_tail(D,DRowMatrix,CRowMatrix,Col,CDRows,ADCols),
  rconvert_stm_tail(C,CRowMatrix,CTailMatrix,BCCol,CDRows,BCCols).

% Precondition: RowMatrix is proper
% PostCondition: TailMatrix is improper and contains tails of rows of RowMatrix,
%  TailRestMatrix is tail of TailMatrix
rconvert_stm_opentail(0,RowMatrix,TailMatrix,TailRestMatrix,_Col,_NumRows,_NumCols) :-
  !,append(RowMatrix,TailRestMatrix,TailMatrix).
rconvert_stm_opentail(1,[[Col|Tail]],[Tail|TailRest],TailRest,Col,_1,_Also1).
rconvert_stm_opentail(zc12(A,B),RowMatrix,TailMatrix,TailRestMatrix,Col,_1,_2) :-
  A = 0 -> ( B = 0 -> RowMatrix = [Tail], TailMatrix = [Tail|TailRestMatrix]
	   ; BCol is Col + 1,
	     RowMatrix = [[BCol|Tail]], TailMatrix = [Tail|TailRestMatrix]
	   )
  ; ( B = 0 -> RowMatrix = [[Col|Tail]], TailMatrix = [Tail|TailRestMatrix]
    ; BCol is Col + 1,
      RowMatrix = [[Col,BCol|Tail]], TailMatrix = [Tail|TailRestMatrix]
    ).
rconvert_stm_opentail(zc21(A,D),RowMatrix,TailMatrix,TailRestMatrix,Col,_2,_1) :-
  A = 0 -> ( D = 0 -> RowMatrix = [TailA,TailD],
	              TailMatrix = [TailA,TailD|TailRestMatrix]
	   ; RowMatrix = [TailA,[Col|TailD]], TailMatrix = [TailA,TailD|TailRestMatrix]
	   )
  ; ( D = 0 -> RowMatrix = [[Col|TailA],TailD],
	       TailMatrix = [TailA,TailD|TailRestMatrix]
    ; RowMatrix = [[Col|TailA],[Col|TailD]], TailMatrix = [TailA,TailD|TailRestMatrix]
    ).
rconvert_stm_opentail(zcu(A,B,C),RowMatrix,TailMatrix,TailRestMatrix,Col,NumRows,
		      NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,CRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm_opentail(B,BRowMatrix,TailMatrix,CTailMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  rconvert_stm_opentail(C,CRowMatrix,CTailMatrix,TailRestMatrix,BCCol,CDRows,BCCols).
rconvert_stm_opentail(zcm(A,B,D,C),RowMatrix,TailMatrix,TailRestMatrix,Col,NumRows,
		      NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,DRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm_opentail(B,BRowMatrix,TailMatrix,CTailMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  rconvert_stm_tail(D,DRowMatrix,CRowMatrix,Col,CDRows,ADCols),
  rconvert_stm_opentail(C,CRowMatrix,CTailMatrix,TailRestMatrix,BCCol,CDRows,BCCols).

% Precondition: RowMatrix is proper
% Postcondition: TailMatrix is proper and contains tails of first NumRows rows
%  of RowMatrix, RestMatrix is remaining rows of RowMatrix.
rconvert_stm_open(0,RowMatrix,RestMatrix,TailMatrix,_Col,NumRows,_NumCols) :-
  !,length(TailMatrix,NumRows),
  append(TailMatrix,RestMatrix,RowMatrix).
rconvert_stm_open(1,[[Col|Tail]|Rest],Rest,[Tail],Col,_1,_Also1).
rconvert_stm_open(zc12(A,B),RowMatrix,RestMatrix,TailMatrix,Col,_1,_2) :-
  A = 0 -> ( B = 0 -> RowMatrix = [Tail|RestMatrix], TailMatrix = [Tail]
	   ; BCol is Col + 1,
	     RowMatrix = [[BCol|Tail]|RestMatrix], TailMatrix = [Tail]
	   )
  ; ( B = 0 -> RowMatrix = [[Col|Tail]|RestMatrix], TailMatrix = [Tail]
    ; BCol is Col + 1,
      RowMatrix = [[Col,BCol|Tail]|RestMatrix], TailMatrix = [Tail]
    ).
rconvert_stm_open(zc21(A,D),RowMatrix,RestMatrix,TailMatrix,Col,_2,_1) :-
  A = 0 -> ( D = 0 -> RowMatrix = [TailA,TailD|RestMatrix], TailMatrix = [TailA,TailD]
	   ; RowMatrix = [TailA,[Col|TailD]|RestMatrix], TailMatrix = [TailA,TailD]
	   )
  ; ( D = 0 -> RowMatrix = [[Col|TailA],TailD|RestMatrix], TailMatrix = [TailA,TailD]
    ; RowMatrix = [[Col|TailA],[Col|TailD]|RestMatrix], TailMatrix = [TailA,TailD]
    ).
rconvert_stm_open(zcu(A,B,C),RowMatrix,RestMatrix,TailMatrix,Col,NumRows,NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,DRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm_opentail(B,BRowMatrix,TailMatrix,CTailMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  length(CRowMatrix,CDRows),
  append(CRowMatrix,RestMatrix,DRowMatrix),
  rconvert_stm_tail(C,CRowMatrix,CTailMatrix,BCCol,CDRows,BCCols).
rconvert_stm_open(zcm(A,B,D,C),RowMatrix,RestMatrix,TailMatrix,Col,NumRows,NumCols) :-
  ABRows is (NumRows+1) >> 1,
  ADCols is (NumCols+1) >> 1,
  rconvert_stm_open(A,RowMatrix,DRowMatrix,BRowMatrix,Col,ABRows,ADCols),
  BCCol is Col + ADCols,
  BCCols is NumCols - ADCols,
  rconvert_stm_opentail(B,BRowMatrix,TailMatrix,CTailMatrix,BCCol,ABRows,BCCols),
  CDRows is NumRows - ABRows,
  rconvert_stm_open(D,DRowMatrix,RestMatrix,CRowMatrix,Col,CDRows,ADCols),
  rconvert_stm_tail(C,CRowMatrix,CTailMatrix,BCCol,CDRows,BCCols).

terminate_rows([]).
terminate_rows([[]|Rest]) :-
  terminate_rows(Rest).

% ==============================================================================

% ------------------------------------------------------------------------------
% hash_stm_rows(RowMatrix,N)
% ------------------------------------------------------------------------------
% Assert the rows of RowMatrix, beginning with index N.
% ------------------------------------------------------------------------------
hash_stm_rows([],_).
hash_stm_rows([Row|STMatrix],N) :-
  assert(stmatrix_num(N,Row)),
  NPlus1 is N + 1,
  hash_stm_rows(STMatrix,NPlus1).

compile_approp(File) :-
  abolish((sub)/2),abolish((intro)/2),
  reconsult(File),
  compile_approp.

compile_approp :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
%  verify_subintro_declarations(SortedSubIntros),
%  verify_intro_declarations(SortedIntros),
%  rebuild_stmatrix(STMatrix),
  compile_approp_act, % (SortedSubIntros,SortedIntros,STMatrix),
  retract(ale_compiling(_)).

verify_subintro_declarations(SortedSubIntros) :-
  ( current_predicate(sub,(_ sub _))
  -> findall(S-FRs,
     ((S sub Ts intro FRs),
     % Error checks invariant to structure of Ss:
      ( var(S) -> raise_exception(ale(sub_lhs_var((S sub Ts intro FRs))))
      ; functor(S,a_,1) -> raise_exception(ale(sub_lhs_abrar))
      ; atom(S) -> true
      ; raise_exception(ale(sub_lhs_other(S)))
      ),
     % Error checks for combined sub/intro declarations:
      ((S = bot,
        FRs \== []) -> raise_exception(ale(bot_feats((S sub Ts intro FRs))))
      ; verify_featrestr_list(FRs,(S sub Ts intro FRs),3)
      )
     ),SubIntros)
  ; SubIntros = []
  ),
  keysort(SubIntros,SortedSubIntros).      % sort, but dups are still there

rebuild_stmatrix(STMatrix) :-
  findall(N-Row,clause(stmatrix_num(N,Row),true),STMatrix),
  ( STMatrix == [] -> raise_exception(ale(no_stmatrix))
  ; true
  ).

compile_approp_act :-
  alec_announce('Compiling appropriateness...'),
  abolish((approp)/3), abolish((approps)/3), retractall(introduce(_,_)),
  ensure_sub_intro,
  ale(bot_feats((bot sub Ss intro [F:R|FRs]))) if_error
        (bot sub Ss intro [F:R|FRs]),
  ale(bot_feats((bot intro [F:R|FRs]))) if_error	
        (bot intro [F:R|FRs]),
  ale(no_features) new_if_warning
        (\+ (_ sub _ intro [_:_|_]),
         \+ (_ intro [_:_|_])),
  ale(duplicate_vr(F,S)) if_error
            ( (S sub _ intro FRs),
              duplicated(F:_,FRs)
            ; (S intro FRs2),
              duplicated(F:_,FRs2)),
  ale(duplicate_intro(S)) if_error
       ((S sub _ intro _),
        (S intro _)
       ;bagof(IType,FRs^(IType intro FRs),ITypes),
        duplicated(S,ITypes)),            % multiple sub/2 taken care of above
  ( ( ( (S sub _ intro FRs)
      ; (S intro FRs)),
      member((_:(a_ X)),FRs),
      cyclic_term(X)
    ) -> error_msg((nl,write_list([atom,'a_',X,is,cyclic,in,declaration,of,S]),nl))
    ; true
  ),
  ale(ground_abar_restriction(F,(a_ X),Clause,ArgNo)) new_if_warning
            ( ( (S sub _ intro FRs), Clause = (S sub _ intro FRs), ArgNo = 3
              ; (S intro FRs), Clause = (S intro FRs), ArgNo = 2),
              member((F:(a_ X)),FRs),
              ground(X)),
  assert(alec(approp)),
  \+ \+ compile('.alec_throw'),
  assert(alec(approps)),
  \+ \+ compile('.alec_throw'),
  retractall(subsume_ready),
  assert(subsume_ready),      % mark as ready for subtest
  ale(approp_cycle(S,Fs)) if_error
     ( type(S), feat_cycle(S,Fs) ),
  ale(nontriv_upward_closure(F,S,T2,T1)) new_if_warning
     ( approp(F,S,T1), restricts(S,F,T2),
       \+ variant(T1,T2)),
  ale(join_nopres(F,S1,S2)) new_if_warning
     non_join_pres(_,F,S1,S2),
  \+ \+ compile_introduce_assert.

ensure_sub_intro :-
 (\+current_predicate(sub,(_ sub _)) -> assertz((_ sub _ :- fail)) ; true),
 (\+current_predicate(intro,(_ intro _)) -> assertz((_ intro _ :- fail)) 
  ; true).

compile_introduce_assert :-
  clause(type_num(T,_),true),  % failure-driven loop through types in topo order
  approps(T,FRs,_),
  member(F:_,FRs),
  ( clause(introduce(F,FIntro),true) -> ( sub_type(FIntro,T) -> true
                                        ; raise_exception(ale(feat_intro(F,[FIntro,T])))
                                        )
  ; assert(introduce(F,T))  % since T is topologically first
  ),
  fail.
compile_introduce_assert.

%compile_approp_act(SortedSubIntros,SortedIntros,STMatrix) :-
%  alec_announce('Compiling appropriateness...'),
%  abolish((approp)/3), abolish((approps)/3),
%  trace, %DEBUG
%  ( no_features new_if_warning_else_fail (SortedSubIntros == [],SortedIntros == [])
%  ; no_duplicates_ksorted(SortedIntros,
%       dup(L1,_,R1,R2,A1,A2,(R1 = A1, R2 = A2),duplicate_decl(intro(L1,R1)),
%           ale(duplicate_intro(L1)))),
%    build_vrqmatrix(SortedSubIntros,SortedIntros,VRQMatrix), % build V

%    qtranspose(VRQMatrix,VRQMatrixTpose),
%    transpose_ugraph(STMatrix,STMatrixTpose),
%    qmultiply(STMatrixTpose,VRQMatrixTpose,RQMatrix),    % build R = ST * V

%    qtranspose(RQMatrix,RQMatrixTpose),
%    verify_upward_closure(VRQMatrixTpose,RQMatrixTpose), % warn on non-trivial up. closures

%    build_stiqmatrixtpose(RQMatrixTpose,STMatrix,VRQMatrix,STIQMatrixTPose),
%    qtranspose(STIQMatrixTPose,STIQMatrix),              % build ST * I

%    convolute(RQMatrix,CMatrix),                         % build C = convolution of R
%    (  top_sort(CMatrix,_)                            % check for appropriateness cycles
%    -> true
%     ; member(T-Neibs,CMatrix),
%       member(S,Neibs),
%       min_path(S,T,CMatrix,Path,_),
%       raise_exception(ale(approp_cycle(T,[T|Path])))
%    ),

%% --- MUST CHANGE approp/3      
%    assert(alec(approp)),
%    \+ \+ compile('.alec_throw'),
%    assert(alec(approps)),
%    \+ \+ compile('.alec_throw'),
%    retractall(subsume_ready),
%    assert(subsume_ready),      % mark as ready for subtest

%    verify_join_preservation(RQMatrix,STIQMatrix)
    
%  ).

build_vrqmatrix([],SIntros,VRQMatrix) :-
  !,build_vrqmatrix_one(SIntros,VRQMatrix).
build_vrqmatrix(SIntros1,SIntros2,VRQMatrix) :-
  SIntros2 = [T2-FRs2|SIntros2Rest]
  -> SIntros1 = [T1-FRs1|SIntros1Rest],
     clause(type_num(T1,N1),true),
     clause(type_num(T2,N2),true),
     compare(Op,N1,N2),
     build_vrqmatrix_act(Op,N1,FRs1,SIntros1Rest,N2,FRs2,SIntros2Rest,
			 VRQMatrix)
   ; build_vrqmatrix_one(SIntros1,VRQMatrix).

build_vrqmatrix_act(<,N1,FRs1,SIntros1,N2,FRs2,SIntros2,
                    [N1-N1Row|VRQMatrix]) :-
  replace_colons(FRs1,KFRs1),
  keysort(KFRs1,SortedFRs1),
  no_duplicates_ksorted(SortedFRs1,dup(F1,_,VR1,VR2,A1,A2,
                        (VR1 = A1, VR2 = A2, clause(num_type(N1,T1),true)),
                        duplicate_feat(F1,VR1,T1),
                        ale(duplicate_vr(F1,T1)))),
  flatten_keys(SortedFRs1,N1Row),
  build_vrqmatrix_rest(SIntros1,N2,FRs2,SIntros2,VRQMatrix).
build_vrqmatrix_act(>,N1,FRs1,SIntros1,N2,FRs2,SIntros2,
                    [N2-N2Row|VRQMatrix]) :-
  replace_colons(FRs2,KFRs2),
  keysort(KFRs2,SortedFRs2),
  no_duplicates_ksorted(SortedFRs2,dup(F1,_,VR1,VR2,A1,A2,
                        (VR1 = A1, VR2 = A2, clause(num_type(N2,T2),true)),
                        duplicate_feat(F1,VR1,T2),
                        ale(duplicate_vr(F1,T2)))),
  flatten_keys(SortedFRs2,N2Row),
  build_vrqmatrix_rest(SIntros2,N1,FRs1,SIntros1,VRQMatrix).
build_vrqmatrix_act(=,N,FRs1,SIntros1,_N,FRs2,SIntros2,[N-NRow|VRQMatrix]) :-
  duplicate_decl(intro(T,FRs1)) if_warning_else_fail 
                  (variant(FRs1,FRs2), clause(num_type(N,T),true))
  -> replace_colons(FRs1,KFRs1),
     keysort(KFRs1,SortedFRs1),
     no_duplicates_ksorted(SortedFRs1,dup(F1,_,VR1,VR2,A1,A2,
                              (VR1 = A1, VR2 = A2, clause(num_type(N,T),true)),
                                          duplicate_feat(F1,VR1,T),
                                          ale(duplicate_vr(F1,T)))),
     flatten_keys(SortedFRs1,NRow),
     build_vrqmatrix(SIntros1,SIntros2,VRQMatrix)
  ; clause(num_type(N,T),true),
    raise_exception(ale(duplicate_intro(T))).

build_vrqmatrix_rest([],N2,FRs2,SIntros2,[N2-N2Row|VRQMatrix]) :-
  replace_colons(FRs2,KFRs2),
  keysort(KFRs2,SortedFRs2),
  no_duplicates_ksorted(SortedFRs2,dup(F1,_,VR1,VR2,A1,A2,
                        (VR1 = A1, VR2 = A2, clause(num_type(N2,T2),true)),
                        duplicate_feat(F1,VR1,T2),
                        ale(duplicate_vr(F1,T2)))),
  flatten_keys(SortedFRs2,N2Row),
  build_vrqmatrix_one(SIntros2,VRQMatrix).
build_vrqmatrix_rest([T1-FRs1|SIntros1],N2,FRs2,SIntros2,VRQMatrix) :-
  clause(type_num(T1,N1),true),
  compare(Op,N1,N2),
  build_vrqmatrix_act(Op,N1,FRs1,SIntros1,N2,FRs2,SIntros2,VRQMatrix).

build_vrqmatrix_one([],[]).
build_vrqmatrix_one([T-FRs|SIntros],[N-NRow|VRQMatrix]) :-
  clause(type_num(T,N),true),
  replace_colons(FRs,KFRs),
  keysort(KFRs,SortedFRs),
  no_duplicates_ksorted(SortedFRs,dup(F1,_,VR1,VR2,A1,A2,
                        (VR1 = A1, VR2 = A2),
                        duplicate_feat(F1,VR1,T),
                        ale(duplicate_vr(F1,T)))),
  flatten_keys(SortedFRs,NRow),
  build_vrqmatrix_one(SIntros,VRQMatrix).

replace_colons([],[]).
replace_colons([F:R|FRs],[F-R|KFRs]) :-
  replace_colons(FRs,KFRs).

flatten_keys([],[]).
flatten_keys([K-V|KVs],[K,V|FlattenedKVs]) :-
  flatten_keys(KVs,FlattenedKVs).

restore_keys([],[]).
restore_keys([K,V|FlattenedKVs],[K-V|KVs]) :-
  restore_keys(FlattenedKVs,KVs).

qtranspose(Graph, Transpose) :-
        qtranspose_edges(Graph, TEdges, []),
        sort(TEdges, TEdges2),
        vertices(Graph, Vertices),
        qgroup_edges(Vertices, TEdges2, Transpose).

qtranspose_edges([]) --> [].
qtranspose_edges([Vertex-Neibs|G]) -->
        qtranspose_edges(Neibs, Vertex),
        qtranspose_edges(G).

qtranspose_edges([], _) --> [].
qtranspose_edges([Neib,Q|Neibs], Vertex) --> [q(Neib,Vertex,Q)],
        qtranspose_edges(Neibs, Vertex).

qgroup_edges([], _, []).
qgroup_edges([Vertex|Vertices], Edges, [Vertex-Neibs|G]) :-
        qgroup_edges(Edges, Vertex, Neibs, RestEdges),
        qgroup_edges(Vertices, RestEdges, G).

qgroup_edges([q(V0,X,Q)|Edges], V, [X,Q|Neibs], RestEdges) :- V0==V, !,
        qgroup_edges(Edges, V, Neibs, RestEdges).
qgroup_edges(Edges, _, [], Edges).

qmultiply([],_,[]).
qmultiply([Row1-Cols1|M1],QM2Tpose,[Row1-QCols3|QM3]) :-
  qmultiply_row(QM2Tpose,Cols1,QCols3,M1,QM2Tpose,QM3,Row1).

qmultiply_row([],_,[],M1,QM2Tpose,QM3,_) :-
  qmultiply(M1,QM2Tpose,QM3).
qmultiply_row([Col2-QRows|QM2TposeRest],Cols1,QCols3,M1,QM2Tpose,QM3,Row1) :-
  ( qintersect(Cols1,QRows,[],Q)          % [] is used to represent sub-bot
  -> ( Q == [] -> QCols3 = QCols3Rest
     ; QCols3 = [Col2,Q|QCols3Rest]
     ),
     qmultiply_row(QM2TposeRest,Cols1,QCols3Rest,M1,QM2Tpose,QM3,Row1)
  ; clause(num_type(Row1,T1),true),       % unify_type/3 failed somewhere
    pretty_vrs(QRows,VRs),
    raise_exception(ale(upward_closure(Col2,T1,VRs)))
  ).

qintersect([],_,Q,Q).
qintersect([C|Cols],[R,QR|QRows],QIn,QOut) :-
  compare(Op,C,R),
  qintersect_act(Op,C,Cols,R,QR,QRows,QIn,QOut).

qintersect_act(<,_,Cols,R,QR,QRows,QIn,QOut) :-
  qintersect_col(Cols,R,QR,QRows,QIn,QOut).
qintersect_act(>,C,Cols,_,_,QRows,QIn,QOut) :-
  qintersect_row(QRows,C,Cols,QIn,QOut).
qintersect_act(=,_C,Cols,_AlsoC,QR,QRows,QIn,QOut) :-
  qunify_type(QIn,QR,QMid),
  qintersect(Cols,QRows,QMid,QOut).

qintersect_col([],_,_,_,Q,Q).
qintersect_col([C|Cols],R,QR,QRows,QIn,QOut) :-
  compare(Op,C,R),
  qintersect_act(Op,C,Cols,R,QR,QRows,QIn,QOut).

qintersect_row([],_,_,Q,Q).
qintersect_row([R,QR|QRows],C,Cols,QIn,QOut) :-
  compare(Op,C,R),
  qintersect_act(Op,C,Cols,R,QR,QRows,QIn,QOut).

qunify_type([],T,T) :- !.   % sub-bot unification
qunify_type(T1,T2,T3) :- unify_type(T1,T2,T3).

pretty_types([],[]).
pretty_types([N|Ns],[T|Ts]) :-
  clause(num_type(N,T),true),
  pretty_types(Ns,Ts).

pretty_vrs([],[]).
pretty_vrs([N,QR|QRows],[T:QR|QRs]) :-
  clause(num_type(N,T),true),
  pretty_vrs(QRows,QRs).

verify_upward_closure([],[]).
verify_upward_closure([Feat-VRQRows|VRQMatrixTpose],[_Feat-RQRows|RQMatrixTpose]) :-
  verify_upward_closure_feat(VRQRows,RQRows,VRQMatrixTpose,RQMatrixTpose,Feat).

verify_upward_closure_feat([],_,VRQMatrixTPose,RQMatrixTPose,_) :-
  verify_upward_closure(VRQMatrixTPose,RQMatrixTPose).
verify_upward_closure_feat([VN,VQ|VRQRows],[RN,RQ|RQRows],VRQMatrixTpose,RQMatrixTPose,
                           Feat) :-
  compare(Op,VN,RN),
  verify_ucf_act(Op,VN,VQ,VRQRows,RN,RQ,RQRows,VRQMatrixTpose,RQMatrixTPose,Feat).

% verify_ucf_act(<,...): R contains all the rows that V does
verify_ucf_act(>,VN,VQ,VRQRows,_,_,[RN,RQ|RQRows],VRQMatrixTpose,RQMatrixTpose,Feat) :-
  compare(Op,VN,RN),
  verify_ucf_act(Op,VN,VQ,VRQRows,RN,RQ,RQRows,VRQMatrixTpose,RQMatrixTpose,Feat).
verify_ucf_act(=,VN,VQ,VRQRows,_VN,RQ,RQRows,VRQMatrixTpose,RQMatrixTpose,Feat) :-
  ( variant(VQ,RQ) -> true
  ; clause(num_type(VN,T),true),
    (nontriv_upward_closure(Feat,T,VQ,RQ) warning)
  ),
  verify_upward_closure_feat(VRQRows,RQRows,VRQMatrixTpose,RQMatrixTpose,Feat).

build_stiqmatrixtpose([],_,_,[]).
build_stiqmatrixtpose([VCol-RQRows|RQMatrixTpose],STMatrix,VRQMatrix,
                      [VCol-SQRows|STIQMatrixTpose]) :-
  qdelta(RQRows,RRows),
  ( memberchk(VRow-RRows,STMatrix)
  -> memberchk(VRow-VRQCols,VRQMatrix),
     append(_,[VCol,V|_],VRQCols),
     qproject(RRows,V,SQRows),
     build_stiqmatrixtpose(RQMatrixTpose,STMatrix,VRQMatrix,STIQMatrixTpose)
  ; map_minimal(RRows,RMins),
    raise_exception(ale(feat_intro(VCol,RMins)))
  ).

qdelta([],[]).
qdelta([Col,_|QCols],[Col|Cols]) :-
  qdelta(QCols,Cols).

qproject([],_,[]).
qproject([Col|Cols],V,[Col,V|QCols]) :-
  qproject(Cols,V,QCols).

convolute([],[]).
convolute([N-QCols|QMatrix],[T-Cols|Matrix]) :-
  clause(num_type(N,T),true),
  convolute_cols(QCols,Cols,QMatrix,Matrix).

convolute_cols([],[],QMatrix,Matrix) :-
  convolute(QMatrix,Matrix).
convolute_cols([_,Q|QCols],Cols,QMatrix,Matrix) :-
  ( functor(Q,a_,1) -> Cols = ColsRest  % a_/1 atoms have no features
  ; Q == bot -> Cols = ColsRest         % neither does bot
  % MAYBE WE SHOULD ALLOW FOR 0 TOO?
  ; Cols = [Q|ColsRest]
  ),
  convolute_cols(QCols,ColsRest,QMatrix,Matrix).

verify_join_preservation(RQMatrix,STIQMatrix) :-
  unify_type(A,B,C), A @< B, B \== C,  A \== C, % no repetition, no subtypes
  atom(C),                                      % no a_/1 atoms
  clause(type_num(A,NA),true),
  clause(type_num(B,NB),true),
  clause(type_num(C,NC),true),
  memberchk(NA-RA,RQMatrix),
  memberchk(NB-RB,RQMatrix),
  memberchk(NC-RC,RQMatrix),
  memberchk(NC-STIC,STIQMatrix),
  unify_vector(RA,RB,RAB),
  unify_vector(RAB,STIC,JP),
  vjp_act(JP,RC,A,B,C),
  fail.
verify_join_preservation(_,_).

vjp_act([],[],_,_,_).
vjp_act([F,QJ|JP],[_F,QC|RC],A,B,C) :-
  ( variant(QJ,QC) -> true
  ; join_nopres(F,A,B) warning,
    ( clause(standard_non_jp(A,B,C),true) -> true
    ; assert(standard_non_jp(A,B,C))
    )
  ),
  vjp_act(JP,RC,A,B,C).

unify_qvector([],V,V).
unify_qvector([F1,Q1|V1],[F2,Q2|V2],[FRes,QRes|VRes]) :-
  compare(Op,F1,F2),
  uqv_act(Op,F1,Q1,V1,F2,Q2,V2,FRes,QRes,VRes).

uqv_act(<,F1,Q1,V1,F2,Q2,V2,F1,Q1,VRes) :-
  uqv_act2(V1,F2,Q2,V2,VRes).
uqv_act(>,F1,Q1,V1,F2,Q2,V2,F2,Q2,VRes) :-
  uqv_act2(V2,F1,Q1,V1,VRes).
uqv_act(=,F,Q1,V1,_F,Q2,V2,F,QRes,VRes) :-
  unify_type(Q1,Q2,QRes),
  unify_qvector(V1,V2,VRes).

uqv_act2([],F,Q,V,[F,Q|V]).
uqv_act2([F1,Q1|V1],F2,Q2,V2,[FRes,QRes|VRes]) :-
  compare(Op,F1,F2),
  uqv_act(Op,F1,Q1,V1,F2,Q2,V2,FRes,QRes,VRes).


compile_extensional(File) :-
  abolish((ext)/1),
  reconsult(File),
  compile_extensional.

compile_extensional :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
%  verify_ext_declaration(SortedExts),
  compile_extensional_act, % (SortedExts),
  retract(ale_compiling(_)).

compile_extensional_act :- % (SortedExts) :-
  alec_announce('Compiling extensionality declarations...'),
  retractall(extensional(_)),
%  retractall(ext_sub_type(_)),retractall(ext_sub_structs(_,_,_,_,_,_)),
%  abolish((iso_sub_seq)/5), % abolish((check_sub_seq)/5),
%  abolish((check_pre_traverse)/6),abolish((check_post_traverse)/6),
%  assert(alec(ext)),
%  \+ \+ compile('.alec_throw'),
  \+ \+ compile_ext_assert. % (SortedExts),
%  assert(alec(iso)),
%  \+ \+ compile('.alec_throw'),
%  assert(alec(check)),
%  \+ \+ compile('.alec_throw').

compile_ext_assert :- % (Es) :-
  current_predicate(ext,ext(_)),
  ext(Es),			% should be passed as arg
  member(T,Es),
  ( maximal(T) -> assert(extensional(T))
  ; raise_exception(ext_nomax(T))
  ),
  fail.
compile_ext_assert :-
  assert(extensional(a_ _)).
  
%compile_ext_sub_assert :-
%  esetof(ValueType-MotherType,F^(approp(F,MotherType,ValueType)),
%         TposeApprops),
%  vertices_edges_to_ugraph([],TposeApprops,TposeAppropGraph),
%  top_sort(TposeAppropGraph,AppropTypes),
%  compile_ext_sub_assert_act(AppropTypes).

%compile_ext_sub_assert_act([]).
%compile_ext_sub_assert_act([T|Ts]) :-
%  approps(T,FRs,A), Arity is A + 2, functor(TFS,tfs,Arity),
%  compile_ext_sub_assert_type(FRs,2,TFS,FS,NewFSs,FSs,FeatGoals,FeatGoalsRest,Goals,GoalsRest),
%  ( Goals == GoalsRest -> compile_ext_sub_assert_act(Ts)
%  ; assert(ext_sub_structs(T,TFS,FS,NewFSs,FSs,FeatGoals,FeatGoalsRest,Goals,GoalsRest)),
%    compile_ext_sub_assert_act(Ts)
%  ).

%compile_ext_sub_assert_type([],_,_,_,FSs,FSs,FeatGoals,FeatGoals,Goals,Goals).
%compile_ext_sub_assert_type([F:R|FRs],N,TFS,FS,NewFSs,FSs,FeatGoals,FeatGoalsRest,Goals,GoalsRest) :-
%  arg(N,TFS,V), NewN is N + 1,
%  (ext_sub_type(R) -> NewFSs = fs(V,VType,VTFS,FSsMid),
%                      cat_atoms('featval_',F,Rel), FeatGoal =.. [Rel,FS,V],
%                      FeatGoals = [FeatGoal|FeatGoalsMid],
%                      Goals = ['$get_attributes'(V,VTFS,VType)|GoalsMid],
%                      compile_ext_sub_assert_type(FRs,NewN,TFS,FSsMid,FSs,FeatGoalsMid,FeatGoalsRest,
%						  GoalsMid,GoalsRest)
%  ; clause(ext_sub_structs(R,_,NewFSs,FSsMid,Goals,GoalsMid,GoalsMid,GoalsMid2),true) ->
%   % this is available if needed because we topologically sorted the types
%                      compile_ext_sub_assert_type(FRs,NewN,TFS,FSsMid,FSs,FeatGoals,FeatGoalsRest,
%						  GoalsMid2,GoalsRest)
%  ; compile_ext_sub_assert_type(FRs,NewN,TFS,NewFSs,FSs,FeatGoals,FeatGoalsRest,Goals,GoalsRest)
%  ).

compile_modules :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_modules_act,
  retract(ale_compiling(_)).

compile_modules_act :-
  alec_announce('Computing signature modules...'),
  retractall(basis(_)), retractall(mbasis(_,_)), retractall(marity(_,_)),
  retractall(tmodule(_,_)), retractall(fcolour(_,_,_)), abolish((deref)/4),
  \+ \+ compile_modules_assert.

:- dynamic basis/1, mbasis/2, marity/2, tmodule/2, fcolour/3.
compile_modules_assert :-
  findall(S-T,(sub_type(S,T),\+ S==T),SubEdges),
  vertices_edges_to_ugraph([],SubEdges,SubGraph),
  top_sort(SubGraph,TopoTypes),

  map_basis(TopoTypes),
  assert(basis(a_ _)),

  map_module(TopoTypes),
  colour_features.  

map_basis([]).
map_basis([T|Ts]) :-
  approps(T,FRs,_),
  map_basis_act(FRs,T,Ts).

map_basis_act([_|_],T,Ts) :-
  \+ (clause(basis(S),true), sub_type(S,T)),
  !,assert(basis(T)),
  map_basis(Ts).
map_basis_act([],T,Ts) :-
  maximal(T),
  !,assert(basis(T)),
  map_basis(Ts).
map_basis_act(_,_,Ts) :-
  map_basis(Ts).

map_module(Ts) :-
  map_module_union_find(Ts),
  map_module_backtrace(Ts).

map_module_union_find([]).
map_module_union_find([T|Ts]) :-
  (clause(basis(T),true) -> map_module_ufbasis(T) ; true),
  map_module_union_find(Ts).

map_module_backtrace([]).
map_module_backtrace([T|Ts]) :-
  ( clause(basis(T),true) -> map_module_btbasis(T)
  ; clause(basis(B),true),
    ( sub_type(T,B) -> true  % since bases are pairwise incomparable, T belongs to no module.
    ; sub_type(B,T) -> clause(tmodule(B,Key),true),  % tmodule/2 already defined for B because we
	               assert(tmodule(T,Key))        % consider types in topological order.
  % ; otherwise fail - this basis element is no help
    ),!
  ; true  % otherwise succeed - T belongs to no module
  ),
  map_module_backtrace(Ts).
  
map_module_btbasis(T) :-  % HACK: actually, this needs no argument - just consider the types
	% as they come, iterating through mbasis/2.
  clause(mbasis(Key,MTypes),true),
  member(T,MTypes),
  assert(tmodule(T,Key)).

map_module_ufbasis(T) :-
  findall(Key-MTypes,(clause(mbasis(Key,MTypes),true),
		      member(U,MTypes), unify_type(T,U,_),
		      retract(mbasis(Key,_))),NewBasis),
  ( NewBasis == [] -> assert(mbasis(T,[T]))
  ; NewBasis = [NewKey-_|_],
    append_keyed_lists(NewBasis,NewMTypes),
    assert(mbasis(NewKey,[T|NewMTypes]))
  ).

min_colouring(G,K,C) :-
  min_colouring_act(0,G,K,C).
min_colouring_act(N,G,K,Colouring) :-
  colouring(G,N,Colouring) -> K = N
  ; NewN is N + 1,
    min_colouring_act(NewN,G,K,Colouring).

colour_features :-
  clause(mbasis(Key,M),true),
  \+ functor(Key,'a_',1),
  findall(F1-F2,(maximal(T), member(B,M), sub_type(B,T), approp(F1,T,_), approp(F2,T,_),
                 F1 \== F2),FEdges),
  findall(F,(maximal(T), approps(T,[F:_],_), member(B,M), sub_type(B,T)),FSingletons),
  vertices_edges_to_ugraph(FSingletons,FEdges,FGraph),
  min_colouring(FGraph,K,Colouring),
  Arity is K + 2,             % could optimise this when 1) all max types in module are extensional, and
                              %   2) no constraints at joins within module.
  assert(marity(Key,Arity)),  
  tabulate_colours(Colouring,Key),
  fail.
colour_features.

tabulate_colours([],_).
tabulate_colours([F-K|Cs],Module) :-
  KPlus1 is K + 1,
  assert(fcolour(F,KPlus1,Module)),
  tabulate_colours(Cs,Module).

compile_cons(File) :-
  abolish((cons)/2),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(cons)) ; true),
  reconsult(File),
  compile_cons.

compile_cons :-
  clear_index,
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_cons_act,
  retract(ale_compiling(_)).

compile_cons_act :-
  alec_announce('Compiling type constraints...'),
  abolish((ct)/3), retractall(constrained(_)), abolish_wpreds,
%  retract_fs_palettes(ct),
  (current_predicate(cons,(_ cons _)) ->
            [bot,has,constraints] if_error
                 ( bot cons _ ),
            [multiple,constraint,declarations,for,CType] if_error
                 (bagof(CT,Cons^(CT cons Cons),CTypes),
                  duplicated(CType,CTypes)),
            [constraint,declaration,given,for,atom] if_error
                 ( (a_ _) cons _ ),
%      ['=@',accessible,by,procedural,attachment,calls,from,constraint,for,Type]
%            if_warning (current_predicate(if,(_ if _)),
%                        find_xeqs([],EGs),
%                        (Type cons _ goal Gs),
%                        find_xeq_act(Gs,EGs)),
      assert(alec(ct)),
      \+ \+ compile('.alec_throw')
  ; ([no,constraints,found] if_warning true)
  ),
  ( current_predicate(compile_cons_hook,compile_cons_hook) -> call_all(compile_cons_hook) ; true).

generate_wpreds(Code,CodeRest) :-
  findall((Head :- Body),(retract(wpred(Head,Body)),assert(wpred_compiled(Head))),Code,CodeRest).

abolish_wpreds :-
  retract(wpred_compiled(Pred)),
  functor(Pred,Rel,Arity),
  static_abolish((Rel)/Arity),
  fail.
abolish_wpreds.

find_xeqs(Accum,EGs) :-
  findall(EG,find_xeq(Accum,EG),NewAccum,Accum),
  find_xeqs_act(NewAccum,Accum,EGs).

find_xeqs_act(EGs,EGs,EGs) :- !.
find_xeqs_act(NewAccum,_,EGs) :-
  find_xeqs(NewAccum,EGs).

find_xeq(Accum,G/N) :-
  (Head if Body),
  functor(Head,G,N),
  \+member(G/N,Accum),
  find_xeq_act(Body,Accum).

find_xeq_act(=@(_,_),_) :- !.
find_xeq_act((G1,_),Accum) :-
  find_xeq_act(G1,Accum),
  !.
find_xeq_act((_,G2),Accum) :-
  find_xeq_act(G2,Accum),
  !.
find_xeq_act((G1 -> G2),Accum) :-
  ( find_xeq_act(G1,Accum)
  ; find_xeq_act(G2,Accum)
  ),
  !.
find_xeq_act((G1;_),Accum) :-
  find_xeq_act(G1,Accum),
  !.
find_xeq_act((_;G2),Accum) :-
  find_xeq_act(G2,Accum),
  !.
find_xeq_act((\+ G),Accum) :-
  find_xeq_act(G,Accum),
  !.
find_xeq_act(At,Accum) :-
  functor(At,AG,AN),
  member(AG/AN,Accum).

compile_logic :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_logic_act,
  retract(ale_compiling(_)).

compile_logic_act :-
  compile_mgsc_act,
  compile_add_to_type_act,
%  compile_featval_act,
  compile_u_act.

compute_mgsat :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_mgsc_act,
  retract(ale_compiling(_)).

compile_mgsc_act :-
  alec_announce('Computing most general satisfiers...'),
  abolish((mgsc)/5), abolish((bind_mgsat)/3),
  \+ \+ compile_mgsc_assert,
  assert(alec(deref)),
  \+ \+ compile('.alec_throw'),
  assert(alec(mgsc)),
  \+ \+ consult('.alec_throw').  % bind_mgsat/3 has attributes - can't compile/1.

compile_mgsc_assert:-
  esetof(ValueType-MotherType,F^(approp(F,MotherType,ValueType),
                                 \+ ValueType = (a_ _),
				 \+ ValueType == bot),TposeApprops),
  setof(T,non_a_bot_type(T),Types),
  vertices_edges_to_ugraph(Types,TposeApprops,TposeAppropGraph),
  top_sort(TposeAppropGraph,AppropTypes),  % build t'pose graph since top_sort
  assert(mgsc((a_ X),(a_ X),max,CGs,CGs)),  % returns reverse ordering
  assert(mgsc(bot,_,_,BGs,BGs)),
  map_mgsat(AppropTypes).

map_mgsat([]).
map_mgsat([T|AppropTypes]) :-
  ( maximal(T) -> clause(tmodule(T,Module),true), clause(marity(Module,Arity),true),
                  functor(FS,Module,Arity), arg(1,FS,TypePos), arg(Arity,FS,DelayPos),
                  DelayPos = max,
                  ( clause(extensional(T),true) -> functor(TypePos,T,0)
		  ; functor(TypePos,T,1), arg(1,TypePos,_Intensional)
		  ),
                  approps(T,FRs,_),
                  map_mgsat_act(FRs,FS,Goals,GoalsMid),
                  Int = max
  ; clause(tmodule(T,Module),true) -> clause(marity(Module,Arity),true),
                                      functor(FS,Module,Arity), arg(1,FS,TypePos), arg(Arity,FS,DelayPos),
                                      TFS = tfs(T,FS,DelayPos,Int),
                                      sp_put_attributes(TypePos,TFS,Goals,Goals0),
                                      approps(T,FRs,_),
                                      map_mgsat_act(FRs,FS,Goals0,GoalsMid)
  ; functor(TFS,tfs,2), arg(1,TFS,T), arg(2,TFS,Int),
    sp_put_attributes(FS,TFS,Goals,GoalsMid)
  ),
  mgsat_cons(T,ConsTypes),
  ( ConsTypes == [] -> GoalsMid = GoalsMid2
  ; GoalsMid = [enforce_constraints(ConsTypes,FS)|GoalsMid2]
  ),
  ( ale_flag(subtypecover,on)
  -> ( clause(deranged_maps(T,_),true) -> GoalsMid2 = [stc_maps_init(T,FS)|GoalsRest]
    ; GoalsMid2 = GoalsRest
    )
  ; GoalsMid2 = GoalsRest
  ),
  assert(mgsc(T,FS,Int,Goals,GoalsRest)),
  map_mgsat(AppropTypes).
  
map_mgsat_act([],_,ConsGoals,ConsGoals).
map_mgsat_act([F:TypeRestr|FRs],FS,ConsGoals,ConsGoalsRest) :-
  clause(introduce(F,FIntro),true), approp(F,FIntro,FIntroRestr),
  ( sub_type(TypeRestr,FIntroRestr) -> map_mgsat_act(FRs,FS,ConsGoals,ConsGoalsRest)
  ; clause(fcolour(F,K,_),true),
    arg(K,FS,V),
    clause(mgsc(TypeRestr,V,_,ConsGoals,ConsGoalsMid),true),
    map_mgsat_act(FRs,FS,ConsGoalsMid,ConsGoalsRest)
  ).

mgsat_cons(Type,ConsTypes) :-
  findall(T,(clause(constrained(T),true),
             sub_type(T,Type)),ConsTypes).
%  map_cons(ConsTypes,FS,ConsGoals,ConsGoalsRest).

compile_mgsat :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_mgsat_act,
  retract(ale_compiling(_)).
	
compile_mgsat_act :-
  ( ale_flag(mgsat,offline) -> alec_announce('Compiling most general satisfiers...'),
                               assert(alec(mgsat)),
                               \+ \+ consult('.alec_throw')  % would like to compile, but mgsats
  ; true                                                     % typically have attributes
  ).

compile_add_to_type :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_add_to_type_act,
  retract(ale_compiling(_)).

compile_add_to_type_act :-
  alec_announce('Compiling type promotion...'),
  abolish((add_to_type)/4),
%  statistics(walltime,_), % DEBUG
  assert(alec(addtype)),
  \+ \+ compile('.alec_throw'),
  
%  statistics(walltime,W), write(user_error,'addtype post-compile: '), % DEBUG
%  write(user_error,W),nl(user_error),
  
  assert(alec(atd)),
  \+ \+ compile('.alec_throw').

%  statistics(walltime,W3), write(user_error,'atd post-compile: '), % DEBUG
%  write(user_error,W3),nl(user_error).

compile_add_to_typed3(Code,CodeRest) :-
  findall((Goal :-
	     deref(FS,TFS,FSType,PosOrFS),
	     BodyGoal),
          (non_a_type(Type),   % types other than a_/1 atoms
           cat_atoms('add_to_typed_',Type,DRel),
	   cat_atoms('add_to_type_',Type,Rel),   
           Goal =.. [DRel,FS],
           BodyGoal =.. [Rel,FSType,TFS,PosOrFS]),
          Code,
          [('add_to_typed_a_'((a_ X),X) :- true)|CodeRest]).
%compile_add_to_typed4(Code,CodeRest) :-
%  findall((Goal :-
%             deref(Tag,SVs,TagOut,SVsOut),
%             Goal2),
%          (non_a_type(Type),   % types other than a_/1 atoms
%           cat_atoms('add_to_typed_',Type,DRel),
%	   cat_atoms('add_to_type_',Type,Rel),   
%           Goal =.. [DRel,SVs,Tag],
%           Goal2 =.. [Rel,SVsOut,TagOut]),
%          Code,
%          [('add_to_typed_a_'(SVs,Tag,X) :-
%              deref(Tag,SVs,TagOut,SVsOut),
%              'add_to_type_a_'(SVsOut,TagOut,X))|CodeRest]).


%compile_featval :-
%  touch('.alec_throw'),
%  absolute_file_name('.alec_throw',AbsFileName),
%  retractall(ale_compiling(_)),
%  assert(ale_compiling(AbsFileName)),
%  compile_featval_act,
%  retract(ale_compiling(_)).
           
%compile_featval_act :-
%  alec_announce('Compiling feature selection...'),
%  abolish((featval)/5),
%  ( ((_ sub _ intro _)
%    ; (_ intro _))
%    -> (assert(alec(featval)),
%        \+ \+ compile('.alec_throw'),
%        assert(alec(fvd)),
%        \+ \+ compile('.alec_throw'))
%  ; true).

%compile_featvald3(Code,CodeRest) :-
%  findall((Goal :-
%             deref(FS,TFS,Type,PosOrFS),
%             BodyGoal),
%          (feature(Feat),
%           cat_atoms('featvald_',Feat,DRel),
%	   cat_atoms('featval_',Feat,Rel),
%           Goal =.. [DRel,FS,FSOut],
%           BodyGoal =.. [Rel,Type,TFS,PosOrFS,FSOut]),
%        Code,CodeRest).

:- dynamic utype_module_pair_visited/2.
compile_u :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_u_act,
  retract(ale_compiling(_)).

compile_u_act :-
  alec_announce('Compiling unification...'),
  abolish((u)/6), retractall(utype_module_pair_visited(_,_)),
  assert(alec(u)),
  \+ \+ compile('.alec_throw').

compile_subsume :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_subsume_act,
  retract(ale_compiling(_)).

compile_subsume_act :-
  ale_flag(subtest,off)
  -> true
   ; (retract(subsume_ready),parsing)
     -> alec_announce('Compiling subsumption checking...'),
        abolish((subsume_type)/13),
        assert(alec(subsume)),
        \+ \+ compile('.alec_throw')
      ; true.

compile_grammar(File):-
  abolish((empty)/1),abolish((rule)/2),
  abolish((lex_rule)/2),
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish(('--->')/2),
  abolish((semantics)/1), abolish((forall)/2),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(grammar)) ; true),
  reconsult(File),
  compile_grammar.

compile_grammar :-
  clear_index,
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_grammar_act,
  retract(ale_compiling(_)).

compile_grammar_act :-
  compile_list_access_act,
  compile_lex_rules_act,
  compile_lex_act,
  compile_rules_act,
% 5/1/96 - Octav -- added call for compilation of generation predicate
  compile_generate_act,
  ( current_predicate(compile_grammar_hook,compile_grammar_hook) -> call_all(compile_grammar_hook)
  ; true).

compile_list_access :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_list_access_act,
  retract(ale_compiling(_)).

compile_list_access_act :-
  static_abolish((add_to_store)/3),static_abolish((add_to_store)/2),
  static_abolish((terminate_store)/1),
  assert(alec(addstore)),
  \+ \+ consult('.alec_throw').  

compile_lex_rules(File):-
  abolish((lex_rule)/2),
  reconsult(File),
  compile_lex_rules.

compile_lex_rules :-
  clear_index,
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_lex_rules_act,
  retract(ale_compiling(_)).

compile_lex_rules_act :-
  abolish((lex_rule)/8), % retract_fs_palettes(lex_rule),
  abolish((forall_lex_rule)/6),abolish((apply_forall_lex_rule)/5),
 (parsing ->
    alec_announce('Compiling lexical rules...'),
  ( [no,lexical,rules,found] if_warning_else_fail
        (\+ current_predicate(lex_rule,lex_rule(_,_)))
    -> true
% 5/1/96 - Octav -- added test to signal lack of 'morphs' specification
     ; ([lexical,rule,RuleName,lacks,morphs,specification] if_error
          ((RuleName lex_rule _ **> _ if _)
          ;(RuleName lex_rule _ **> _)),
        assert(alec(forall_lex_rule)),
        \+ \+ compile('.alec_throw'),
        assert(alec(lexrules)),
        \+ \+ consult('.alec_throw'))  % would compile but routinely exceeds 256-var limit
  )
 ; true).

compile_lex(File):-
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish(('--->')/2),abolish((lex_rule)/2),abolish((semantics)/1),
  abolish((forall)/2),
  reconsult(File),
  compile_lex.

compile_lex :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_lex_act,
  retract(ale_compiling(_)).

compile_lex_act :-
  abolish((lex)/2), retract_fs_palettes(lex),
  abolish((forall_lex)/3), abolish((apply_forall_lex)/2),
  secret_noadderrs(Mode),
  (parsing ->
    alec_announce('Compiling lexicon...'),
    [no,lexicon,found] if_warning
      (\+ current_predicate('--->',(_ ---> _))),
    assert(alec(forall_lex)),
    \+ \+ compile('.alec_throw'),
    assert(alec(lex)),
    (ale_flag(lexicon,consult) -> \+ \+ consult('.alec_throw')
                      ; \+ \+ compile('.alec_throw'))
  ; true
  ),
  secret_adderrs(Mode).

% update_lex(+File)
% -----------------
% add the lexical entries in File to the lexicon, closing under lexical rules.
update_lex(File) :-
  ale_flag(lexicon,consult),
  assert(lexicon_updating),
  reconsult(File),
  retract(lexicon_updating).

% retract_lex(+LexSpec)
% ---------------------
% retract the lexical entries specified by LexSpec, not closing under lexical
%  rules.  LexSpec is either a word, or a list of words.
retract_lex(LexSpec) :-
  ( current_predicate(lex,lex(_,_,_))
  -> ( predicate_property(lex(_,_,_),dynamic) -> (LexSpec = [_|_]
                                                 -> retract_lex_list(LexSpec)
                                                 ; retract_lex_one(LexSpec)
                                                 )
     ; error_msg((nl,write('retract_lex/1: lexicon is currently static'),nl))
     )
  ; error_msg((nl,write('retract_lex/1: no compiled lexicon in memory'),nl))
  ).

retract_lex_list([]).
retract_lex_list([Lex|LexRest]) :-
  retract_lex_one(Lex),
  retract_lex_list(LexRest).

retract_lex_one(Word) :-
  call_residue((clause(lex(Word,FS),Body,Ref), call(Body)),FS,Residue),
  ((current_predicate(portray_lex,portray_lex(_,_,_)),
    portray_lex(Word,FS,Residue)) -> true
  ; nl, write('WORD: '), write(Word),
    nl, write('ENTRY: '), nl,
    pp_fs_res(FS,Residue),nl
  ),
  write('RETRACT? '),flush_output,read(y),
  erase(Ref),
  fail.                       
retract_lex_one(_).

retractall_lex(LexSpec) :-
  LexSpec = [_|_]
   -> retractall_lex_list(LexSpec)
    ; retractall(lex(LexSpec,_,_,_)).
retractall_lex_list([]).
retractall_lex_list([Lex|LexRest]) :-
  retractall(lex(Lex,_,_,_)),
  retract_lex_list(LexRest).

% export_words(+Stream,+Delimiter)
% --------------------------------
% Write the words in the current lexicon in a Delimiter-separated list to
%  Stream
export_words(Stream,Delimiter) :-
  setof(Word,FS^lex(Word,FS),Words),
  export_words_act(Words,Stream,Delimiter).
export_words_act([],_,_).
export_words_act([W|Ws],Stream,Delimiter) :-
  write(Stream,W),write(Stream,Delimiter),
  export_words_act(Ws,Stream,Delimiter).

:- dynamic emptynum/1.
:- dynamic alec_rule/9, rule_compiled/1.
:- dynamic fspal_ref/2.

%compile_empty(File):-
%  abolish((empty)/1),
%  reconsult(File),
%  compile_empty.

%compile_empty :-
%  touch('.alec_throw'),
%  absolute_file_name('.alec_throw',AbsFileName),
%  retractall(ale_compiling(_)),
%  assert(ale_compiling(AbsFileName)),
%  compile_empty_act,
%  retract(ale_compiling(_)).

%compile_empty_act :-
%  abolish((empty_cat)/4),
%  retractall(emptynum(_)),
%  assert(emptynum(-1)),
%  secret_noadderrs,
%  (parsing
%  -> alec_announce('Compiling empty categories...'),
%     (assert(alec(empty)),
%                    (ale_flag(lexicon,consult) -> consult('.alec_throw')
%                                      ; compile('.alec_throw')))
%   ; true),
%  secret_adderrs.

%retract_empty :-
%  empty_cat(N,Tag,SVs,IqsIn),
%  extensionalise(Tag,SVs,IqsIn),
%  check_inequal(IqsIn,IqsOut),
%  nl, write('EMPTY CATEGORY: '), 
%  pp_fs_col(Tag,SVs,IqsOut,4),
%  nl, write('RETRACT? '),flush_output,read(y),
%  retract(empty_cat(N,Tag,SVs,IqsIn)),
%  fail.
%retract_empty.

%retractall_empty :-
%  retractall(empty_cat(_,_,_,_)).

compile_rules(File):-
% 5/1/96 - Octav -- added abolish/2 calls for generation predicates
  abolish((rule)/2),abolish((empty)/1),abolish((forall)/2),
  reconsult(File),
  compile_rules.

compile_rules :-
  clear_index,
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_rules_act,
  retract(ale_compiling(_)).

retract_fs_palettes(Source) :-
  retract(fspal_ref(Source,Ref)),
  erase(Ref),
  fail
 ; true.

compile_rules_act :-
  alec_announce('Compiling empty categories and phrase structure rules...'),
  abolish((empty_cat)/5), retractall(emptynum(_)), assert(emptynum(-1)),
  abolish((rule)/6), abolish((chain_rule)/8), abolish((try_rule)/6),
  abolish((non_chain_rule)/4),abolish((chained)/4),
  abolish((forall_rule)/4),abolish((apply_forall_rule)/3),
  retractall(alec_rule(_,_,_,_,_,_,_,_,_)), retractall(rule_compiled(_)),
%  retract_fs_palettes(chained),  retract_fs_palettes(chain_rule),
  retract_fs_palettes(non_chain_rule), retract_fs_palettes(rule),
  ( [no,phrase,structure,rules,found] if_warning_else_fail
         (\+ current_predicate(rule,rule(_,_)))
    -> true
% 5/1/96 - Octav -- added 'sem_head>' in the list of labels tested for
  ; [rule,RuleName,has,no,'cat>','cats>',or,'sem_head>',specification]
      if_error ((RuleName rule _ ===> Body),
                \+ cat_member(Body),
                \+ cats_member(Body),
	        \+ sem_head_member(Body)),
% 5/1/96 - Octav -- added check for multiple occurences of 'sem_head>' label
    [rule,RuleName,has,multiple,'sem_head>',specifications]
      if_error ((RuleName rule _ ===> Body),
	        multiple_heads(Body)),
% 6/10/97 - Octav -- added check for bad 'sem_goal>' labels
    [rule,RuleName,has,wrongly,placed,'sem_goal>',specifications]
      if_error ((RuleName rule _ ===> Body),
                bad_sem_goal(Body))),
  (parsing -> (secret_noadderrs(Mode),
	       assert(alec(forall_rule)),
	       \+ \+ compile('.alec_throw'),
               assert(alec(empty)),
               \+ \+ consult('.alec_throw'),
               secret_adderrs(Mode),
               assert(alec(rules)),
	       ( ale_flag(psrules,consult) -> \+ \+ consult('.alec_throw')
	       ; \+ \+ compile('.alec_throw')
	       ))
            ; true),
% 5/1/96 - Octav -- added secret_noadderrs/0 to prevent printing 'unification
%   failure' messages during chaining compilation
% 7/1/98 - Gerald -- changed secret_noadderrs/0 calls to have scope only
%   over relevant (non-chain) lexical compilation
  (generating ->
% 5/1/96 - Octav -- added compilation of chain rules for generation
    ( [no,chain,rules,found] if_warning_else_fail
         (\+ (current_predicate(rule,(_ rule _)),
	      (_ rule _ ===> Body), split_dtrs(Body,_,_,_,_,_)))
    -> true
     ; assert(alec(chain)),
       \+ \+ compile('.alec_throw'),
       assert(alec(chained)),
       \+ \+ compile('.alec_throw')),
% 5/1/96 - Octav - added compilation of non_chain rules for generation
    ( [no,non_chain,rules,found] if_warning_else_fail
         (\+ (current_predicate(rule,(_ rule _)),
              (_ rule _ ===> Body), \+ split_dtrs(Body,_,_,_,_,_)),
          \+ current_predicate(empty,empty(_)),
          \+ current_predicate('--->',(_ ---> _)))
    -> true
     ; (assert(alec(nochain)),
        \+ \+ compile('.alec_throw')))
  ; true).

% 5/1/96 - Octav -- added rules to compile the generation predicate
compile_generate(File) :-
  abolish((semantics)/1),
  reconsult(File),
  compile_generate.

compile_generate :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_generate_act,
  retract(ale_compiling(_)).

compile_generate_act :-
  abolish((generate)/3),
  (generating ->
    alec_announce('Compiling semantics directive...'),
  (  [no,semantics,directive,found] if_warning_else_fail
      (\+ current_predicate(semantics,semantics(_)))
  -> true
  ; semantics(Pred), functor(Goal,Pred,2),
    ([no,Pred,definite,clause,found] if_warning_else_fail
      (\+ (current_predicate(if,(_ if _)), (Goal if _)))
    -> true
     ; (assert(alec(generate)),
        \+ \+ compile('.alec_throw'))))
  ; true).

compile_dcs(File):-
  abolish((if)/2),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(dcs)) ; true),
  reconsult(File),
  compile_dcs.

compile_dcs :-
  clear_index,
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_dcs_act,
  retract(ale_compiling(_)).

compile_dcs_act :-
  alec_announce('Compiling definite clauses...'),
  retractall(fun_exp(_,_)), abolish((when_approp)/2),
%  retract_fs_palettes(dcs),
  [no,definite,clauses,found] if_warning
    (\+ current_predicate(if,if(_,_))),
  assert(alec(dcs)),
  \+ \+ compile('.alec_throw'),
  ( current_predicate(compile_dcs_hook,compile_dcs_hook) -> call_all(compile_dcs_hook) ; true).

:- dynamic fun_exp/2.
compile_dcs(Code,CodeRest) :-
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(MFSIn),
  empty_avl(NVs),
  empty_avl(EMode),
  findall((CompiledHead :- CompiledBody),
	  ( ( current_predicate('+++>',(_ +++> _)),
	      (FunDesc +++> Result),
	      functor(FunDesc,Rel,FunArity),
  	      RelArity is FunArity + 1,
              fun_expand_act(0,FunArity,FunDesc,ArgDescs,Result),
              ( clause(fun_exp(Rel,RelArity),true) -> true
	      ; assert(fun_exp(Rel,RelArity))),
	      Body = true
            ; current_predicate(if,if(_,_)),
	      (Head if Body),
	      functor(Head,Rel,RelArity),
	      Head =.. [_|ArgDescs]
	    ),
	    initialise_rel_mode(RelArity,ArgPaths,EMode,ModeIn,MFSIn,MFSMid),
	    assert_input_modes(RelArity,Rel,ArgPaths,ModeIn,ModeMid,MFSMid,MFSMid2),
            ( compile_descs(ArgDescs,Args,ArgPaths,CompiledBodyList,CompiledBodyRest,
                            serial,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeMid,ModeOut,MFSMid2,MFSMid3,NVs),
%             append(Args,[IqsIn,IqsOut],CompiledArgs),
              cat_atoms('fs_',Rel,CompiledRel),
              CompiledHead =.. [CompiledRel|Args],
              term_variables(ArgDescs,PriorVs),
              compile_body(Body,CompiledBodyRest,[],serial,VarsMid,_VarsOut,FSPal,FSsMid,FSsOut,MFSMid3,
			   MFSOut,NVs,PriorVs,[]),
 	      verify_output_modes(RelArity,Rel,ArgPaths,ModeOut,MFSOut),
	      assert_empty_avl(FSsOut)
%             build_fs_palette(FSsOut,FSPal,CompiledBodyList,CompiledBodyMid,dcs)
	    -> goal_list_to_seq(CompiledBodyList,CompiledBody)
	    ; print_message(warning,ale(dcs_failure((Head if Body)))),
	      fail
	    )),
          Code,CodeRest),
  esetof((Rel/RelArity),(current_predicate(if,if(_,_)),
	                 (Head if _Body),
			 functor(Head,Rel,RelArity),
			 clause(fun_exp(Rel,RelArity),true)),FunRedefines),
  ( member(Spec,FunRedefines),
    [Spec,already,implicitly,defined,by,'+++>',declaration] if_warning true,
    fail
  ; true
  ).
% KNOWN BUG - should register these predicates so that we can abolish them on
%  recompiles.  Unclear what's happening at present.

%     , \+ (CodeRest =[], member(C,Code), write(user_error,C), nl(user_error), fail)
%   ; CodeRest = Code.

fun_expand_act(A,A,_,[Result],Result) :- !.
fun_expand_act(I,A,FunDesc,[ArgDesc|ArgDescs],Result) :-
  NewI is I + 1,
  arg(NewI,FunDesc,ArgDesc),
  fun_expand_act(NewI,A,FunDesc,ArgDescs,Result).

% ==============================================================================
% Functional Description Resolution/Compilation
% ==============================================================================

compile_fun(File):-
  abolish(('+++>')/2), abolish((fun)/1),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(fun)) ; true),
  reconsult(File),
  compile_fun_act.

compile_fun :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_fun_act,
  retract(ale_compiling(_)).

compile_fun_act :-
  alec_announce('Compiling functional descriptions...'),
  retractall(fun_spec(_,_,_)),
  compile_fun_assert,
  ( current_predicate(compile_fun_hook,compile_fun_hook) -> call_all(compile_fun_hook) ; true).

:- dynamic fun_spec/3.
compile_fun_assert :-
  current_predicate(fun,fun(_)),
  (fun FunSpec),
  functor(FunSpec,Functor,RelArity),
  FunArity is RelArity - 1,
  [nullary,relation,FunSpec,specified,as,function] if_error (FunArity < 0),
  [nullary,function,FunSpec,identical,to,type] if_error ( FunArity == 0, non_a_type(Functor) ),
  [unary,function,FunSpec,identical,to,'a_',atom] if_error ( FunArity == 1,
	   					             Functor == 'a_' ),
  ( compile_fun_act(0,RelArity,FunSpec,ResArg) -> assert(fun_spec(Functor,FunArity,ResArg)),
                                                  fail
  ; error_msg((nl,write('  **ERROR: no result argument specified in '),write(FunSpec),nl))
  ).
compile_fun_assert :-
  current_predicate('+++>',(_ +++> _)),
  (FunDesc +++> _Result),
  functor(FunDesc,Functor,FunArity),
  ResArg is FunArity + 1,
  [nullary,function,FunSpec,identical,to,type] if_error ( FunArity == 0, non_a_type(Functor) ),
  [unary,function,FunSpec,identical,to,'a_',atom] if_error ( FunArity == 1,
    	   				                     Functor == 'a_' ),
  assert(fun_spec(Functor,FunArity,ResArg)),
  fail.
compile_fun_assert :-
  [conflicting,argument,positions,ResArg1,and,ResArg2,for,function,Functor,'/',FunArity]
    if_warning (clause(fun_spec(Functor,FunArity,ResArg1),true),
                clause(fun_spec(Functor,FunArity,ResArg2),true),
                ResArg1 \== ResArg2).

compile_fun_act(I,N,FunSpec,ResArg) :-
  I < N,
  NewI is I + 1,
  arg(NewI,FunSpec,A),
  ( A == '-' -> ResArg = NewI, compile_fun_flush(NewI,N,FunSpec)
  ; compile_fun_act(NewI,N,FunSpec,ResArg)
  ).

compile_fun_flush(N,N,_) :- !.
compile_fun_flush(I,N,FunSpec) :-
%  I < N,
  NewI is I + 1,
  arg(NewI,FunSpec,A),
  [multiple,result,arguments,specified,in,FunSpec] if_error (A == '-'),
  compile_fun_flush(NewI,N,FunSpec).

compile_macro(File) :-
  abolish((macro)/2),
  ( current_predicate(abolish_user_preds,abolish_user_preds(_)) -> call_all(abolish_user_preds(macro)) ; true),
  reconsult(File),
  compile_macro_act.

compile_macro :-
  touch('.alec_throw'),
  absolute_file_name('.alec_throw',AbsFileName),
  retractall(ale_compiling(_)),
  assert(ale_compiling(AbsFileName)),
  compile_macro_act,
  retract(ale_compiling(_)).

compile_macro_act :-
  alec_announce('Verifying macros...'),
  ( current_predicate(compile_macro_hook,compile_macro_hook) -> call_all(compile_macro_hook) ; true),
  verify_macro_declarations.

verify_macro_declarations :-
  current_predicate(macro,(_ macro _)) -> findall((MacroName/Arity)-macroclause(N,Head,Body),
                                                  ((Head macro Body),
                                                   genindex(N),
                                                   functor(Head,MacroName,Arity)),
                                                  NABs),
                                          keysort(NABs,KSortedNABs),
                                          verify_macro_declarations_act(KSortedNABs)
  ; true.

verify_macro_declarations_act([]) :- print_message(warning,ale(no_succ_macros)).
verify_macro_declarations_act([(MacroName/Arity)-macroclause(N,Head,Body)|KNABs]) :-
  verify_macro_declarations_act(KNABs,MacroName,Arity,N,Head,Body,_,_).

verify_macro_declarations_act([],MacroName,Arity,_,_,_,DiscFlag,MultFlag) :-
  report_macro_flags(DiscFlag,MultFlag,MacroName,Arity).
verify_macro_declarations_act([(MacroName2/Arity2)-macroclause(N2,Head2,Body2)|KNABs],
                              MacroName1,Arity1,N1,Head1,Body1,DiscFlag,MultFlag) :-
  (MacroName1 == MacroName2, Arity1 == Arity2)
  -> ( (variant(Head1,Head2), variant(Body1,Body2)) 
     -> print_message(warning,ale(identical_macro_clauses(MacroName1,Arity1,Head1,Body1)))
     ; true
     ),
     ( (N2 =\= N1 + 1) -> DiscFlag = discontiguous ; MultFlag = multiple),
     verify_macro_declarations_act(KNABs,MacroName1,Arity1,N2,Head2,Body2,DiscFlag,MultFlag)
   ; report_macro_flags(DiscFlag,MultFlag,MacroName1,Arity1),
     verify_macro_declarations_act(KNABs,MacroName2,Arity2,N2,Head2,Body2,_NewDiscFlag,_NewMultFlag).

report_macro_flags(DiscFlag,MultFlag,MacroName,Arity) :-
   nonvar(DiscFlag) -> print_message(warning,ale(discontiguous_macro_clauses(MacroName,Arity)))
 ; nonvar(MultFlag) -> print_message(warning,ale(multiple_macro_clauses(MacroName,Arity)))
 ; true.


% ------------------------------------------------------------------------------
% cat_member(Dtrs)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one category member
% ------------------------------------------------------------------------------
cat_member((cat> _)).
cat_member((cat> _, _)):-!.
cat_member((_,Body)):-
  cat_member(Body).

% ------------------------------------------------------------------------------
% sem_head_member(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one sem_head> member
% ------------------------------------------------------------------------------
sem_head_member((sem_head> _)).
sem_head_member((sem_head> _,_)):-!.
sem_head_member((_,Body)):-
  sem_head_member(Body).

% ------------------------------------------------------------------------------
% sem_goal_member(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one sem_goal> member
% ------------------------------------------------------------------------------
sem_goal_member((sem_goal> _)).
sem_goal_member((sem_goal> _,_)):-!.
sem_goal_member((_,Body)):-
  sem_goal_member(Body).

% ------------------------------------------------------------------------------
% cats_member(Dtrs)
% ------------------------------------------------------------------------------
% true if Dtrs has at least one cats member
% ------------------------------------------------------------------------------
cats_member((cats> _)).
cats_member((cats> _, _)):- !.  % doesn't check for cats> [] or elist!
cats_member((_,Body)):-
  cats_member(Body).

% ------------------------------------------------------------------------------
% multiple_heads(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% checks whether Dtrs has multiple sem_head> members
% ------------------------------------------------------------------------------
multiple_heads((sem_head> _,Dtrs)) :- !,
  sem_head_member(Dtrs).
multiple_heads((_,Dtrs)) :-
  multiple_heads(Dtrs).

% ------------------------------------------------------------------------------
% bad_sem_goal(+Dtrs:<desc>s)
% ------------------------------------------------------------------------------
% checks whether Dtrs has wrongly placed sem_goal> members
% ------------------------------------------------------------------------------
bad_sem_goal(Dtrs) :-       % there's a sem_head
  split_dtrs(Dtrs,_,_,_,DtrsBefore,DtrsAfter),
  !,(sem_goal_member(DtrsBefore)
    -> true
     ; sem_goal_member(DtrsAfter)).
bad_sem_goal(Dtrs) :-       % there's no sem_head
  sem_goal_member(Dtrs).

% ------------------------------------------------------------------------------
% if_h(Goal:<goal>, SubGoals:<goal>s)                                      +user
% ------------------------------------------------------------------------------
% accounts for multi-hash goals with no subgoals given
% ------------------------------------------------------------------------------
Goal if_h [] :-
  Goal if_h.

% ------------------------------------------------------------------------------
% multi_hash(N:<int>, Fun/Arity:<fun_sym>/<int>,Code:<goals>,CodeRest:<goals>)
% ------------------------------------------------------------------------------
% for each solution T1,...,TK of ?- G(T1,...,TK) if_h SubGoals. 
%   G(f1(X11,...,X1J1),V2,...,VK):-
%       G_f1(V2,...,VK,X11,...,X1J1).
%   ...
%   G_f1_f2_..._fN(TN+1,...,TK,X11,...,X1J1,X21,..,X2J2,...,XN1,..,XNJN):-
%     SubGoals.
% order matters for clauses listed with if_b, but not with if_h
% clauses with if_b must have subgoals listed, even if empty (for order)
% Will not behave properly with if_b on discontiguous user declarations for N>0
% ------------------------------------------------------------------------------

multi_hash(N,(Fun)/Arity,Code,CodeRest):-
  length(Args,Arity),
  Goal =.. [Fun|Args],
% DEBUG
%  statistics(walltime,B),write(user_error,'pre-setof: '),
%  write(user_error,B),nl(user_error),
  
  ( setof(sol(Args,SubGoals), if_h(Goal,SubGoals), Sols)
    -> true
     ; bagof(sol(Args,SubGoals), if_b(Goal,SubGoals), Sols)
  ),

%  statistics(walltime,E),write(user_error,'pre-hash: '),
%  write(user_error,E),nl(user_error),

  mh(N,Sols,Fun,Code,CodeRest).

%  statistics(walltime,H),write(user_error,'post-hash: '),
%  write(user_error,H),nl(user_error).
  

my_multi_hash(N,(Fun)/Arity,Code,CodeRest):-  % DEBUG
  length(Args,Arity),
  Goal =.. [Fun|Args],
  statistics(walltime,_),
  ( setof(sol(Args,SubGoals), if_h(Goal,SubGoals), Sols)
    -> true
     ; bagof(sol(Args,SubGoals), if_b(Goal,SubGoals), Sols)
  ),
  statistics(walltime,[_,SolS]),
  write(user_error,'DEBUG: solutions '),write(user_error,SolS),nl(user_error),flush_output(user_error),
  mh(N,Sols,Fun,Code,CodeRest),
  statistics(walltime,[_,HashS]),
  write(user_error,'DEBUG: hash '),write(user_error,HashS),nl(user_error),flush_output(user_error).

mh(0,Sols,Fun,Code,CodeRest):-
  !, mh_zero(Sols,Fun,Code,CodeRest).
mh(N,Sols,Fun,Code,CodeRest):-
  mh_nonzero(Sols,Fun,N,Code,CodeRest).

mh_zero([],_,Code,Code).
mh_zero([sol(Args,SubGoals)|Sols],Fun,[Clause|CodeMid],CodeRest) :-
  Goal =.. [Fun|Args],
  (SubGoals = []
    -> (Clause = Goal)
     ; (goal_list_to_seq(SubGoals,SubGoalSeq),
        Clause = (Goal :- SubGoalSeq))),
  mh_zero(Sols,Fun,CodeMid,CodeRest).

mh_nonzero([],_,_,Code,Code).
mh_nonzero([sol(Args,SubGoals)],Fun,_,[Clause|CodeRest],CodeRest):-
  !, Goal =.. [Fun|Args],
  (SubGoals = []
   -> (Clause = Goal)
    ; (goal_list_to_seq(SubGoals,SubGoalSeq),
       Clause = (Goal :- SubGoalSeq))).
  
mh_nonzero([sol([Arg|Args],SubGoals)|Sols],Fun,N,Code,CodeRest):-
  nonvar(Arg), 
  functor(Arg,FunArg,Arity),
  Arg =.. [_|ArgsArg],
  ( (Sols = [sol([Arg2|_],_)|_],
     nonvar(Arg2), functor(Arg2,FunArg,Arity))
    -> (cat_atoms('_',FunArg,FunTail),
        cat_atoms(Fun,FunTail,FunNew),
        same_length(Args,OtherArgs),
        Goal =.. [Fun,Arg|OtherArgs],
        append(OtherArgs,ArgsArg,ArgsNew), 
        SubGoal =.. [FunNew|ArgsNew],
        append(Args,ArgsArg,ArgsOld),
        (Code = [(Goal :-
                    SubGoal)|CodeMid]),
        SolsSub = [sol(ArgsOld,SubGoals)|SolsSubRest],
        mh_arg(FunArg,Arity,Sols,SolsSub,SolsSubRest,Fun,FunNew,N,
               CodeMid,CodeRest))
  ; Goal =.. [Fun,Arg|Args],
    (Code = [Clause|CodeMid]),
    (SubGoals = []
     -> (Clause = Goal)
      ; (goal_list_to_seq(SubGoals,SubGoalSeq),
         Clause = (Goal :- SubGoalSeq))),
    mh_nonzero(Sols,Fun,N,CodeMid,CodeRest)
  ).

mh_arg(FunMatch,Arity,[sol([Arg|Args],SubGoals)|Sols],SolsSub,SolsSubMid,
       Fun,FunNew,N,Code,CodeRest):-
  nonvar(Arg),
  Arg =.. [FunMatch|ArgsSub],  % formerly cut here - standard order ensures
  length(ArgsSub,Arity),       %  correctness for if_h in both cases
  !,append(Args,ArgsSub,ArgsNew),
  SolsSubMid = [sol(ArgsNew,SubGoals)|SolsSubRest],
  mh_arg(FunMatch,Arity,Sols,SolsSub,SolsSubRest,Fun,FunNew,N,
         Code,CodeRest).
mh_arg(_,_,Sols,SolsSub,[],Fun,FunNew,N,Code,CodeRest):-
  NMinusOne is N-1,
  mh(NMinusOne,SolsSub,FunNew,Code,CodeMid),
  mh_nonzero(Sols,Fun,N,CodeMid,CodeRest).



% ==============================================================================
% Debugger / Top Level I/O
% ==============================================================================

% ------------------------------------------------------------------------------
% show_type(Type:<type>)
% ------------------------------------------------------------------------------
% Displays information about Type, including appropriate features, immediate
% subtypes, supertypes, and constraints.  Continues by allowing to browse 
% super or subtypes
% ------------------------------------------------------------------------------
show_type(Type):-
  type(Type),
  immed_subtypes(Type,SubTypes),
  ( setof(T,T2^(sub_type(T,Type),
                T \== Type,
                \+ (sub_type(T2,Type),
                    T2 \== Type, T2 \== T,
                    sub_type(T,T2))),SuperTypes)
    -> true
  ; SuperTypes = []
  ),
  (current_predicate(cons,(_ cons _))
   -> ((Type cons Cons goal Goal)
       -> true
        ; (Type cons Cons)
          -> Goal = none
           ; Cons = none, Goal = none)
    ; Cons = none, Goal = none
  ),
  ( join_reducible(Type) -> JoinReducible = 1  ; JoinReducible = 0),
  esetof(F,non_join_pres(Type,F),Fs),
  esetof(T,unary_branch(T,Type),Ts),  % HACK: this is slow
  ((current_predicate(portray_type_info,portray_type_info(_,_,_,_,_,_,_,_)),
    portray_type_info(Type,SubTypes,SuperTypes,JoinReducible,Fs,Ts,Cons,Goal)) -> true
  ; nl,  write('TYPE: '), write(Type),
    nl, write('SUBTYPES: '), write_list(SubTypes),
    nl, write('SUPERTYPES: '), write_list(SuperTypes),
    ( JoinReducible == 1 -> nl,write(Type),write(' is JOIN-REDUCIBLE') ; true),
    ( Fs == [] -> true ; nl,write('HOMOMORPHISM CONDITION fails at: '),
                         write_list(Fs)),
    ( Ts == [] -> true ; nl,write('UNARY BRANCHES from: '), write_list(Ts)),
    empty_avl(EAssoc),
    nl, write('IMMEDIATE CONSTRAINT: '), pp_desc(Cons,EAssoc,_,EAssoc,_,22,EAssoc,_),
    (Goal == none -> true
    ; nl, write('           WITH GOAL: '), pp_goal(Goal,EAssoc,_,EAssoc,_,22,EAssoc,_)
    )
  ),
  call_residue(add_to(Type,FS),FS,Residue),
  ((current_predicate(portray_mgsat,portray_mgsat(_,_,_,_)),
    portray_mgsat(Type,FS,Residue,Type)) -> true
  ; nl, write('MOST GENERAL SATISFIER: '),
    pp_fs_res_col(FS,Residue,5),nl
  ),
  query_proceed.

% ------------------------------------------------------------------------------
% show_cons(Type:<type>)
%-------------------------------------------------------------------------------
show_cons(Type):-
  immed_cons(Type,Cons,Goal),
  nl, write('Immediate Constraint for type: '),write(Type),
  nl, write(Cons),
  (Goal = true -> true
  ; nl, write('with goal: '), write(Goal)).

% ------------------------------------------------------------------------------
% mgsat(Desc:<desc>)
% ------------------------------------------------------------------------------
% prints out most general satisfiers of Desc
% ------------------------------------------------------------------------------
mgsat(Desc):-
   infer_mgsat_type(Desc,bot,MGType),
   \+ \+ (call_residue(add_to(Desc,FS),FS,Residue),
	  ((current_predicate(portray_mgsat,portray_mgsat(_,_,_,_)),
	    portray_mgsat(Desc,FS,Residue,MGType)) -> true
	  ; nl, write('MOST GENERAL SATISFIER OF: '), write(Desc), nl,
            pp_fs_res(FS,Residue,MGType), nl
	  ),
          query_proceed).

infer_mgsat_type(Var,Trigger,Trigger) :-
  var(Var),
  !.
infer_mgsat_type(Feat:_,TrigIn,TrigOut) :-
  clause(introduce(Feat,Intro),true),
  !,unify_type(Intro,TrigIn,TrigOut).
infer_mgsat_type([],TrigIn,TrigOut) :-
  !,unify_type(e_list,TrigIn,TrigOut).
infer_mgsat_type([_|_],TrigIn,TrigOut) :-
  !,unify_type(ne_list,TrigIn,TrigOut).
infer_mgsat_type(@ MacroName,TrigIn,TrigOut) :-
  !,
  ( (current_predicate(macro,(_ macro _)), (MacroName macro Desc))
  -> infer_mgsat_type(Desc,TrigIn,TrigOut)
   ; raise_exception(undef_macro(MacroName))
  ).
infer_mgsat_type(FS,TrigIn,TrigOut) :-
  functor(FS,Module,Arity),
  clause(marity(Module,Arity),true),
  !, deref(FS,_,FSType,_),
  unify_type(FSType,TrigIn,TrigOut).
infer_mgsat_type((D1,D2),TrigIn,TrigOut) :-
  !,infer_mgsat_type(D1,TrigIn,TrigMid),
  infer_mgsat_type(D2,TrigMid,TrigOut).
infer_mgsat_type((D1;D2),TrigIn,TrigOut) :-
  !,infer_mgsat_type(D1,TrigIn,TrigOut1),
  infer_mgsat_type(D2,TrigIn,TrigOut2),
  generalise(TrigOut1,TrigOut2,TrigOut).
infer_mgsat_type(Type,TrigIn,TrigOut) :-
  type(Type),
  !,unify_type(Type,TrigIn,TrigOut).
infer_mgsat_type(FunDesc,Trigger,Trigger) :- % should add output mode from ResArg 
  functor(FunDesc,Functor,FunArity),         % when those become available
  clause(fun_spec(Functor,FunArity,_ResArg),true),
  !.
infer_mgsat_type((=\= _),Trigger,Trigger) :-
  !.
infer_mgsat_type(D,_,_) :-
  raise_exception(ill_desc(D)).

% ------------------------------------------------------------------------------
% iso_desc(Desc1:<desc>, Desc2:<desc>)
% ------------------------------------------------------------------------------
% checks if Desc1 and Desc2 create extensionally identical structures
% ------------------------------------------------------------------------------
%iso_desc(D1,D2):-  % we can use =@ now that we have the new term encoding.
%  add_to(D1,FS1),
%  add_to(D2,FS2),
%  iso_seq(iso(FS1,FS2,done)).

% ------------------------------------------------------------------------------
% rec(Words:<word>s)
% ------------------------------------------------------------------------------
% basic predicate to parse Words;  prints out recognized categories
% one at a time
% ------------------------------------------------------------------------------
rec(Words):-  
  rec(Words,bot).

%  nl, write('STRING: '),
%  nl, number_display(Words,0),
%  nl, 
%  \+ \+ on_exception(ale(Exception),
%		     (rec(Words,FS,Residue),
%                      ((current_predicate(portray_cat,portray_cat(_,_,_,_,_)),  
%                        portray_cat(Words,bot,FS,Residue)) -> true         
%                      ; nl, write('CATEGORY: '),nl, flush_output,
%                        pp_fs_res(FS,Residue), nl
%                      ),
%                      query_proceed),
%		     alex(Exception)).

% ------------------------------------------------------------------------------
% rec(Words:<word>s,Desc:<desc>)
% ------------------------------------------------------------------------------
% Like rec/1, but solution FSs must satisfy Desc
% ------------------------------------------------------------------------------
rec(Words,Desc):-  % must add code to print residues
  nl, write('STRING: '),
  nl, number_display(Words,0),
  nl, % SP4: ttynl replaced with nl/1.
  \+ \+ on_exception(ale(Exception),
		     (rec(Words,FS,Desc,Residue,Index),
                      ((current_predicate(portray_cat,portray_cat(_,_,_,_,_)),
                        portray_cat(Words,Desc,FS,Residue,Index)) -> true
                      % see also gen/1 - portray_cat/5 can be called with var 1st arg.
                      ; nl, write('CATEGORY: '),nl, flush_output, % SP4: no more ttyflush/0
                        pp_fs_res(FS,Residue),nl
                      ),
                      query_proceed),
		     alex(Exception)).

% ------------------------------------------------------------------------------
% rec_best(+WordsList:list(<word>s),Desc)
% ------------------------------------------------------------------------------
% Parses every list of words in WordsList until one succeeds, satisfying Desc,
%  or there are no more lists.  If one succeeds, then rec_best/2 will backtrack
%  through all of its solutions that satisfy Desc, but not through the
%  subsequent lists of words in WordsList.
% ------------------------------------------------------------------------------
rec_best([],_) :-
  fail.
rec_best([Ws|WordsList],Desc) :-
 \+ \+ on_exception(ale(Exception),
		    (if(rec(Ws,FS,Desc,Residue,Index),
                        (((current_predicate(portray_cat,portray_cat(_,_,_,_,_)),
        	           portray_cat(Ws,Desc,FS,Residue,Index)) -> true
                         ; nl,write('STRING: '),
                          nl,number_display(Ws,0),
                          nl, write('CATEGORY: '),nl, flush_output,
                          pp_fs_res(FS,Residue),nl
                         ),
                        query_proceed),
                        rec_best(WordsList,Desc))),
		    alex(Exception)).

% ------------------------------------------------------------------------------
% rec_list(+WordsList:list(<word>s),Desc)
% ------------------------------------------------------------------------------
% Parses every list of words in WordsList until one succeeds, satisfying Desc,
%  or there are no more lists.  Unlike rec_best/2, rec_list/2 will backtrack
%  through all of the solutions of a list that succeeds, and then continue
%  parsing the subsequent lists of words in WordsList.
% ------------------------------------------------------------------------------
rec_list([],_) :-
  fail.
rec_list([Ws|WordsList],Desc) :-
  \+ \+ on_exception(ale(Exception),
	             ((rec(Ws,FS,Desc,Residue,Index),
  	               ((current_predcicate(portray_cat,portray_cat(_,_,_,_,_)),
   	                 portray_cat(Ws,Desc,FS,Residue,Index)) -> true
	               ; nl,write('STRING: '),
                         nl,number_display(Ws,0),
    	                 nl, write('CATEGORY: '),nl, flush_output,
                         pp_fs_res(FS,Residue),nl
	               ),
                       query_proceed)
                     ; rec_list(WordsList,Desc)
		     ),
		     alex(Exception)).

% ------------------------------------------------------------------------------
% rec_list(+WordsList:list(<word>s),Desc,SolnsList:list(<fs(FS,Iqs)>s))
% ------------------------------------------------------------------------------
% Like rec_list/2, but collects the solutions in a list of lists, one for each
%  list of words in WordsList.
% ------------------------------------------------------------------------------
rec_list([],_,[]).
rec_list([Ws|WordsList],Desc,[Solns|SolnsList]) :-
  bagof(soln(FS,Residue),  % collect indices too?
	on_exception(ale(Exception),rec(Ws,FS,Desc,Residue),alex(Exception)),
        Solns),
  rec_list(WordsList,Desc,SolnsList).

% ------------------------------------------------------------------------------
% lex(Word:<word>)
% ------------------------------------------------------------------------------
% prints out all categories for Word, querying user in between
% ------------------------------------------------------------------------------
lex(Word):-
  \+ \+ on_exception(ale(Exception),
	             (current_predicate(lex,lex(_,_))
                     -> if(call_residue(lex(Word,FS),FS,Residue),
   		           true,
             		   raise_exception(ale(unk_words([Word])))),
                        ((current_predicate(portray_lex,portray_lex(_,_,_)),
                          portray_lex(Word,FS,Residue)) -> true
                        ; nl, write('WORD: '), write(Word),
                          nl, write('ENTRY: '), nl,
                          pp_fs_res(FS,Residue), nl
                        ),
                        query_proceed
                     ; raise_exception(ale(no_lex))),
	             alex(Exception)).

% ------------------------------------------------------------------------------
% query(GoalDesc:<goal_desc>)
% ------------------------------------------------------------------------------
% given a goal description GoalDesc, finds most general satisfier of it
% and then calls it as a goal
% ------------------------------------------------------------------------------
query(GoalDesc):-  % must add code to print residues
 \+ \+
 (nl, empty_avl(AssocIn),  % KNOWN BUG: we should be checking relation mode somewhere inside query_goal/5
  call_residue((query_goal(GoalDesc,Args,[],Goal,Zip),
		Zip = []),Goal,Residue),	 % Args isn't well-formed until we instantiate this.
		
  \+ \+ (((current_predicate(portray_ale_goal,portray_ale_goal(_,_)),
	   portray_ale_goal(Goal,Residue)) -> true
	 ; filter_iqs(Residue,Iqs,FSResidue),
	   (ale_flag(residue,show) -> residue_args(FSResidue,ResArgs,Args) ; ResArgs = Args),
	   duplicates_list(ResArgs,AssocIn,DupsMid,AssocIn,VisMid,0,NumMid),
	   duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,Inf,NumMid,_),
           pp_goal(Goal,DupsOut,Inf,AssocIn,VisMid2,0,AssocIn,HDMid),
	   nl,nl,
	   pp_iqs(Iqs,DupsOut,Inf,VisMid2,VisOut,0,HDMid,HDOut),
	   ((ale_flag(residue,show),FSResidue \== [])
  	   -> nl,nl, write('Residue:'), pp_residue(FSResidue,DupsOut,Inf,VisOut,_,HDOut,_)
	    ; true), nl
	 ),
         query_proceed)
 ).

ale(GD) :-     		% nicer interface, analogous to prolog/1 in ALE.
  secret_noadderrs_toggle(Mode),
  query_goal(GD),
  secret_adderrs_toggle(Mode).

query_goal(GD) :-
  query_goal(GD,_,_,_,[]).
  % instantiating Zip now guarantees no Arg suspensions.

query_goal(GD,DtrCats,DtrCatsRest,G,Zip) :-
  empty_avl(NVs),
  on_exception(cut,query_goal0(GD,DtrCats,DtrCatsRest,G,NVs,Zip),fail).
% KNOWN BUG: IS THIS EXCEPTION HANDLER PROPERLY PLACED?  WHAT DO WE DO WITH RULE
% ATTACHMENTS WITH EXPOSED CUTS?

query_goal0((GD1,GD2),DtrCats,DtrCatsRest,(G1,G2),NVs,Zip):-
  !, query_goal0(GD1,DtrCats,DtrCatsMid,G1,NVs,Zip),
  query_goal0(GD2,DtrCatsMid,DtrCatsRest,G2,NVs,Zip).
query_goal0((GD1 -> GD2 ; GD3),DtrCats,DtrCatsRest,(G1 -> G2 ; G3),NVs,Zip) :-
  !,( query_goal0(GD1,DtrCats,DtrCatsMid,G1,NVs,Zip)
    -> query_goal0(GD2,DtrCatsMid,DtrCatsRest,G2,NVs,Zip)
%       nv_replace_body(GD3,G3,DtrCatsMid2,DtrCatsRest,NVs) % see query_goal_args/5 comment below
    ; query_goal0(GD3,DtrCats,DtrCatsRest,G3,NVs,Zip)
%      nv_replace_body(GD1,G1,DtrCats,DtrCatsMid,NVs),     % see query_goal_args/5 comment below
%      nv_replace_body(GD2,G2,DtrCatsMid,DtrCatsMid2,NVs)
    ).
query_goal0((GD1;GD2),DtrCats,DtrCatsRest,(G1;G2),NVs,Zip):-
  !,( query_goal0(GD1,DtrCats,DtrCatsRest,G1,NVs,Zip)
%      nv_replace_body(GD2,G2,DtrCatsMid,DtrCatsRest,NVs) % see query_goal_args/5 comment below
    ; query_goal0(GD2,DtrCats,DtrCatsRest,G2,NVs,Zip)
%      nv_replace_body(GD1,G1,DtrCats,DtrCatsMid,NVs)     % see query_goal_args/5 comment below
    ).
query_goal0((\+ GD1),DtrCats,DtrCatsRest,(\+ G1),NVs,_) :-
  !, \+ query_goal0(GD1,_,_,_,NVs,_),
  nv_replace_body(GD1,G1,DtrCats,DtrCatsRest,NVs).
query_goal0(prolog(Hook),DtrCats,DtrCats,prolog(Hook),_NVs,_) :-
  !,
  call(Hook).  % could at least attempt to look for duplicated desc vars here
query_goal0(prolog(NVs,Hook),DtrCats,DtrCats,prolog(NVs,Hook),NVs,_) :-
  !,
  call(Hook).  % could at least attempt to look for duplicated desc vars here
query_goal0(when(Cond,Body),DtrCats,DtrCatsRest,when(NCond,Goal),NVs,Zip) :-
  !, query_cond(Cond,NCond,Body,DtrCats,DtrCatsRest,Goal,NVs,Zip,_).
query_goal0(true,DtrCats,DtrCats,true,_,_) :-
  !.
query_goal0(fail,_,_,_,_,_) :-
  !, fail.
query_goal0(!,DtrCats,DtrCats,!,_,_) :-
  !, ( true
     ; raise_exception(cut)
     ).
query_goal0((GD1 -> GD2),DtrCats,DtrCatsRest,(G1 -> G2),NVs,Zip) :-
  !,(  query_goal0(GD1,DtrCats,DtrCatsMid,G1,NVs,Zip)
    -> query_goal0(GD2,DtrCatsMid,DtrCatsRest,G2,NVs,Zip)
    ).
query_goal0((Desc1 =@ Desc2),[FS1,FS2|DtrCatsRest],DtrCatsRest,
	   (FS1 =@ FS2),NVs,_) :-
  !, % nv_replace_desc(Desc1,NDesc1,DtrCatsMid,DtrCatsMid2,NVs), % see query_goal_args/5 comment below
  nv_replace_desc(Desc1,NDesc1,_DescVars,DescVarsMid,NVs),
  add_to(NDesc1,FS1,bot,tfs(bot,_),FS1,bot),
  nv_replace_desc(Desc2,NDesc2,DescVarsMid,_DescVarsRest,NVs),
  add_to(NDesc2,FS2,bot,tfs(bot,_),FS2,bot),
  (FS1 == FS2).
query_goal0((Desc1 = Desc2),[FS,FS|DtrCatsRest],DtrCatsRest,
	    (FS = FS),NVs,_) :-
  !, % nv_replace_desc(Desc1,NDesc1,DtrCatsMid,DtrCatsMid2,NVs),  % see query_goal_args/5 comment below
  nv_replace_desc(Desc1,NDesc1,_DescVars,DescVarsMid,NVs),
  add_to(NDesc1,FS,bot,tfs(bot,_),FS,bot),
  nv_replace_desc(Desc2,NDesc2,DescVarsMid,_DescVarsRest,NVs),
  deref(FS,TFS2,Type2,AttPos),
  add_to(NDesc2,FS,Type2,TFS2,AttPos,bot).
query_goal0(AtGD,DtrCats,DtrCatsRest,Goal,NVs,_):-
  AtGD =.. [Rel|ArgDescs],  % KNOWN BUG: need to check relation mode
  query_goal_args(ArgDescs,DtrCats,DtrCatsRest,GoalArgs,NVs),
  cat_atoms('fs_',Rel,CompiledRel),
  AtG =.. [CompiledRel|GoalArgs],
  Goal =.. [Rel|GoalArgs],
  call(AtG).

query_goal_args([],DtrCats,DtrCats,[],_).
query_goal_args([D|Ds],[FS|DtrCats],DtrCatsRest,[FS|GArgs],NVs):-
  nv_replace_desc(D,ND,_DescVars,_DescVarsRest,NVs),
  add_to(ND,FS,bot,tfs(bot,_),FS,bot),
  query_goal_args(Ds,DtrCats,DtrCatsRest,GArgs,NVs).

%query_goal_args([],DtrCats,DtrCats,[],_).
%query_goal_args([D|Ds],[FS|DtrCats],DtrCatsRest,[FS|GArgs],NVs):-
%  nv_replace_desc(D,ND,DtrCats,DtrCatsMid,NVs), - KNOWN BUG: this is close to what we should do, but ALE
%                                                   does not portray descriptions in successul queries,
%                                                   but rather FSs; descriptions would be better
%  add_to(ND,FS,bot,tfs(bot,_),FS,bot),
%  query_goal_args(Ds,DtrCatsMid,DtrCatsRest,GArgs,NVs).

query_cond(X^(Cond),Fresh^(NCond),Body,DtrCats,DtrCatsRest,NBody,NVs,Zip,FreshNVs) :-
  !, % ['non-variable',X,used,in,quantifier] if_error nonvar(X), - do we need this?
  % References might make it difficult to index instantiated narrow vars,
  % and we can't tell one from another Tag-SVs in prolog hooks.
  (var(Zip) -> when(nonvar(FreshNVs),avl_fetch(X,FreshNVs,seen(Fresh))) ; true), % nonvar(Zip) means don't care about Fresh
  avl_store(X,NVs,unseen,NVsMid),
  query_cond(Cond,NCond,Body,DtrCats,DtrCatsRest,NBody,NVsMid,Zip,FreshNVs).
query_cond(Cond,NCond,Body,DtrCats,DtrCatsRest,NBody,NVs,Zip,FreshNVs) :-
  var(Zip),
  !, when(nonvar(FreshNVs),nv_replace_cond0(Cond,NCond,DtrCats,DtrCatsMid,FreshNVs)),
  when(nonvar(Zip),(var(FreshNVs) -> avl_map(nv_fresh,NVs,NVsSeen),
                                     nv_replace_body(Body,NBody,DtrCatsMid,DtrCatsRest,
						     NVsSeen),
		                     FreshNVs = NVsSeen
                           		    % FreshNVs must be well-formed when bound
		                   ; true)),
  transform_cond(Cond,CUFCond),
  query_cond0(CUFCond,(avl_map(nv_fresh,NVsOut,NVsSeen),
		       FreshNVs = NVsSeen,  % FreshNVs must be well-formed when bound
                       query_goal0(Body,DtrCatsMid,DtrCatsRest,NBody,FreshNVs,Zip)),
	      NVs,NVsOut).
query_cond(Cond,_,Body,_,_,_,NVs,Zip,_) :-
  % nonvar(Zip) - so forget about NCond, NBody, FreshNVs, and DtrCats-Rest
  transform_cond(Cond,CUFCond),
  query_cond0(CUFCond,(avl_map(nv_fresh,NVsOut,NVsSeen),
                       query_goal0(Body,_,_,_,NVsSeen,Zip)),
	      NVs,NVsOut).
	      
query_cond0([Cond1|Cond2],WBody,NVs,FreshNVs) :-
  query_cond0_act(Cond2,Cond1,WBody,NVs,FreshNVs).

query_cond0_act([],(C1;C2),WBody,NVs,NVsOut) :-
  !, when(nonvar(Trigger),(Trigger == 0 -> NVsOut = NVsOut0 ; NVsOut = NVsOut1)),
  query_cond0(C1,(Trigger = 0 -> WBody ; true),NVs,NVsOut0),
  query_cond0(C2,(Trigger = 1 -> WBody ; true),NVs,NVsOut1).
query_cond0_act([],FS=Desc,WBody,NVs,NVsOut) :-
  [narrowly,quantified,variable,used,on,'LHS',of,delay,FS=Desc]
    if_error avl_fetch(FS,NVs,unseen),
  query_cond_desc(Desc,FS,WBody,NVs,NVsOut).
query_cond0_act([Cond|CondRest],FS=Desc,WBody,NVs,NVsOut) :-
  [narrowly,quantified,variable,used,on,'LHS',of,delay,FS=Desc]
    if_error avl_fetch(FS,NVs,unseen),
  query_cond_desc(Desc,FS,query_cond0_act(CondRest,Cond,WBody,NVsMid,NVsOut),NVs,NVsMid).

query_cond_desc(Var,FS,Body,NVs,NVsOut) :-
  var(Var),
  !, '$get_attributes'(Var,TFS,_),
  ( var(TFS) -> ( avl_change(Var,NVs,unseen,NVsOut,seen(FS))
	        -> call(Body)
	        ; NVsOut = NVs, when_eq(FS,Var,Body)
	        )
  ; ( avl_fetch(Var,NVs,SeenFlag)
    -> ( SeenFlag = seen(FVar) -> NVsOut = NVs, when_eq(FS,FVar,Body)
       ; % SeenFlag = unseen,
	 avl_store(Var,NVs,seen(FS),NVsOut),
         call(Body)
       )
    ; NVsOut = NVs, when_eq(FS,Var,Body)
    )
  ).
query_cond_desc(F:Desc,FS,Body,NVs,NVsOut) :-
 clause(introduce(F,FIntro),true),
  !, clause(fcolour(F,K,_),true),
  when_type(FIntro,FS,(arg(K,FS,FSatF),
		       query_cond_desc(Desc,FSatF,Body,NVs,NVsOut))).
query_cond_desc((Path1 == Path2),FS,Body,NVs,NVsOut) :-
  !, expand_path(Path1,PathVar,ExpPath1),
  expand_path(Path2,PathVar,ExpPath2),
  avl_store(PathVar,NVs,unseen,PathNVs),
  query_cond_desc((ExpPath1,ExpPath2),FS,Body,PathNVs,NVsOut).
query_cond_desc((Desc1,Desc2),FS,Body,NVs,NVsOut) :-
  !, query_cond_desc(Desc1,FS,query_cond_desc(Desc2,FS,Body,NVsMid,NVsOut),NVs,NVsMid).
query_cond_desc((a_ X),FS,Body,NVs,NVs) :-
  !, when_a_(X,FS,Body).
query_cond_desc(Var,FS,Body,NVs,NVsOut) :-
  functor(Var,Module,Arity),
  clause(marity(Module,Arity),true),
  !,
  ( avl_fetch(Var,NVs,SeenFlag)
  -> ( SeenFlag = seen(FVar) -> NVsOut = NVs, when_eq(FS,FVar,Body)
     ; % SeenFlag = unseen,
       avl_store(Var,NVs,seen(FS),NVsOut),
       call(Body)
     )
  ; NVsOut = NVs, when_eq(FS,Var,Body)
  ).
query_cond_desc(Type,FS,Body,NVs,NVs) :-
  non_a_type(Type),
  !, (Type == bot -> call(Body)
     ; when_type(Type,FS,Body)
     ).
query_cond_desc(X,_,_,_,_) :-
  error_msg((nl,write('unrecognised conditional: '),write(X))).

pp_goal(\+ Goal,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  !, write('\\+ '), write('( '), 
  NewCol is Col+5, pp_goal(Goal,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut),
  nl, tab(Col), tab(3), write(')').
pp_goal((G1 -> G2 ; G3),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('(  '), NewCol is Col + 3,
  pp_goal(G1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  nl, tab(Col), write('-> '),
  pp_goal(G2,Dups,Inf,VisMid,VisMid2,NewCol,HDMid,HDMid2),
  nl, tab(Col), write(';  '),
  pp_goal(G3,Dups,Inf,VisMid2,VisOut,NewCol,HDMid2,HDOut),
  nl, tab(Col), write(')').
pp_goal((Goal1;Goal2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  !, write('( '), NewCol is Col + 2,
  pp_goal(Goal1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  nl, tab(Col), write('; '),
  pp_goal(Goal2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  nl, tab(Col), write(')').
pp_goal((Goal1,Goal2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  !, pp_goal(Goal1,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid), write(','),
  nl, tab(Col), pp_goal(Goal2,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).
pp_goal(prolog(Hook),_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write(prolog(Hook)).
pp_goal(prolog(NVs,Hook),_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write(prolog(NVs,Hook)).
pp_goal(when(Cond,Goal),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('when('), NewCol is Col + 5,
  pp_cond(Cond,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  write(','), nl, tab(NewCol),
  pp_goal(Goal,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  write(')').
pp_goal(Desc1 =@ Desc2,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('('),
  NewCol is Col+3,
  pp_desc(Desc1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid), nl, tab(Col),
  write('=@'), nl, tab(NewCol),
  pp_desc(Desc2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut), nl, tab(Col),
  write(')').
pp_goal(true,_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write(true).
pp_goal(!,_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write(!).
pp_goal((G1 -> G2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('(  '), NewCol is Col + 3,
  pp_goal(G1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  nl, tab(Col), write('-> '),
  pp_goal(G2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  nl, tab(Col), write(')').
pp_goal(fail,_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write(fail).
pp_goal((Desc1 = Desc2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('('),
  NewCol is Col+3,
  pp_desc(Desc1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid), nl, tab(Col),
  write('='), nl, tab(NewCol),
  pp_desc(Desc2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut), nl, tab(Col),
  write(')').
pp_goal(Goal,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  Goal =.. [Rel|Args],
  write(Rel),
  ( Args = []  % inequation threading occupies the last two positions
    -> VisOut = VisIn, HDOut = HDIn
  ; write('('),
    name(Rel,Name),
    length(Name,N),
    NewCol is Col+N+1,
    pp_goal_args(Args,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut)
  ).

pp_goal_args([Arg],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-  % one left
  !, pp_desc(Arg,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut), write(')').
pp_goal_args([Arg|Args],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  pp_desc(Arg,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid), write(','), nl, tab(Col),
  pp_goal_args(Args,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).

pp_cond(X^(Cond),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  pp_desc(X,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid), 
  nl, tab(Col), write('^ '), NewCol is Col + 2,
  pp_cond(Cond,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut).
pp_cond((C1,C2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  write('('), NewCol is Col + 1,
  pp_cond(C1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid), write(','),
  nl, tab(NewCol), pp_cond(C2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  write(')').
pp_cond((C1;C2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  write('( '), NewCol is Col + 2,
  pp_cond(C1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  nl, tab(Col), write('; '),
  pp_cond(C2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  nl, tab(Col), write(')').
pp_cond(FS=Desc,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  pp_desc(FS,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
  nl, tab(Col), write('='),
  nl, tab(Col), pp_desc(Desc,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).

pp_desc(X,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  var(X),
  !, pp_fs(X,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut).
pp_desc(FS,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  functor(FS,Module,Arity),
  clause(marity(Module,Arity),true),
  !,
  pp_fs(FS,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut).
pp_desc([],_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !,write([]).
pp_desc([H|T],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !,write('['),
  pp_desc(H,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
  pp_tail(T,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).
pp_desc(F:Desc,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write_feature(F,LengthF),
  NewCol is Col + LengthF +1,
  pp_desc(Desc,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut).
pp_desc(@ Macro,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  write('@ '), NewCol is Col + 2,
  pp_desc(Macro,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut).
				% will fall through to function clause
pp_desc((D1,D2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('('), NewCol is Col + 1,
  pp_desc(D1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid), write(','),
  nl, tab(NewCol), pp_desc(D2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  write(')').
pp_desc((D1;D2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  !, write('( '), NewCol is Col + 2,
  pp_desc(D1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  nl, tab(Col), write('; '),
  pp_desc(D2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),
  nl, tab(Col), write(')').
pp_desc((=\= Desc),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('=\\= '), NewCol is Col+4,
  pp_desc(Desc,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut).
pp_desc(Path1 == Path2,_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write(Path1),write(' == '),write(Path2).
pp_desc(a_ X,_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !, write('a_ '),write(X).
pp_desc(Other,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
				% handles types, functions and macros
  Other =.. [Head|Args],
  write(Head),
  ( Args = [] -> VisOut = VisIn, HDOut = HDIn
  ; write('('),
    name(Head,Name), length(Name,N), NewCol is Col + N + 1,
    pp_descs(Args,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut)
  ).

pp_descs([Desc],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, pp_desc(Desc,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut), write(')').
pp_descs([D|Ds],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  pp_desc(D,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid), write(','), nl, tab(Col),
  pp_descs(Ds,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).

pp_tail([],_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  !,write(']').
pp_tail([H|T],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !,write(','),pp_desc(H,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
  pp_tail(T,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).
pp_tail(NonList,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  write('|'),pp_desc(NonList,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut),
  write(']').

% ------------------------------------------------------------------------------
% mg_sat_fun(FunDesc,Fun,IqsIn,IqsOut)                                   eval
% ------------------------------------------------------------------------------
% Fun is most general satisfier of FunDesc
% (also used for functional descriptions)
% ------------------------------------------------------------------------------
%mg_sat_fun(GoalDesc,Goal,IqsIn,IqsOut):-
%  GoalDesc =.. [Rel|ArgDescs],
%  mg_sat_list(ArgDescs,Args,IqsIn,IqsOut),
%  Goal =.. [Rel|Args].

% ------------------------------------------------------------------------------
% mg_sat_list(GoalDescs,Goals,IqsIn,IqsOut)
% ------------------------------------------------------------------------------
% maps mg_sat_fun on GoalDescs
% ------------------------------------------------------------------------------
mg_sat_list([],[]).
mg_sat_list([ArgDesc|ArgDescs],[FS|Args]) :-
  add_to(ArgDesc,FS,bot,tfs(bot,_),FS,bot),
  mg_sat_list(ArgDescs,Args).

dpp_fs(FS) :-
  dpp_fs(FS,0).

dpp_fs(FS,Col) :-
  deref(FS,_,ZType,_),
  write(ZType), nl,
  zero_trans(ZType,Type),
  approps(Type,FRs,_),
  dpp_fs_act(FRs,FS,Col).

dpp_fs_act([],_,_).
dpp_fs_act([Feat:_|FRs],FS,Col) :-
  tab(Col), write(Feat), write(' '),
  clause(fcolour(Feat,K,_),true),
  arg(K,FS,V),
  name(Feat,FeatName),length(FeatName,L),
  NewCol is Col + L + 2,
  dpp_fs(V,NewCol),
  dpp_fs_act(FRs,FS,Col).

% ------------------------------------------------------------------------------
% macro(MacroName:<name>)
% ------------------------------------------------------------------------------
% prints out possible instantiations of macro named MacroName
% ------------------------------------------------------------------------------
macro(MacroName) :-
%  MacroName = VarName,
%  \+ \+
  empty_avl(AssocIn),
  (MacroName macro Desc),
  call_residue((add_to(Desc,FS),
                MacroName =.. [Name|MacroArgDescs],
                mg_sat_list(MacroArgDescs,MacroArgs),
                MacroSat =.. [Name|MacroArgs],
                ArgsOut = [FS|MacroArgs]),[MacroSat|FS],Residue),
  \+ \+ (((current_predicate(portray_ale_macro,portray_ale_macro(_,_,_,_)),
	   portray_ale_macro(MacroName,Desc,FS,Residue)) -> true
	 ; filter_iqs(Residue,Iqs,FSResidue),
	   (ale_flag(residue,show) -> residue_args(FSResidue,ResArgs,ArgsOut) ; ResArgs = ArgsOut),
           duplicates_list(ResArgs,AssocIn,DupsMid,AssocIn,VisMid,0,NumMid),
           duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,Inf,NumMid,_),
           nl, write('MACRO: '),
           nl, tab(4), pp_goal(MacroSat,DupsOut,Inf,AssocIn,VisMid2,4,AssocIn,HDMid),
           nl, write('ABBREVIATES:'),
           nl, tab(4), pp_fs(FS,DupsOut,Inf,VisMid2,VisMid3,4,HDMid,HDMid2),
           nl, nl, tab(4), pp_iqs(Iqs,DupsOut,Inf,VisMid3,VisOut,4,HDMid2,HDOut),
           ((ale_flag(residue,show),FSResidue \== [])
           -> nl, nl, write('Residue:'), pp_residue(FSResidue,DupsOut,Inf,VisOut,_,HDOut,_)
           ; true),nl
	 ),
         query_proceed).

%insert_vars(MacroName,VarName):-
%  MacroName =.. [Rel|Args],
%  insert_vars_list(Args,ArgsVars),
%  VarName =.. [Rel|ArgsVars].

%insert_vars_list([],[]).
%insert_vars_list([X|Xs],[(_,X)|XsVar]):-
%  insert_vars_list(Xs,XsVar).

% ------------------------------------------------------------------------------
% empty
% ------------------------------------------------------------------------------
% displays empty categories
% ------------------------------------------------------------------------------
empty:-
  \+ \+ (call_residue(empty_cat(I,-1,FS,Dtrs,RuleName),FS,Residue),
         length(Dtrs,ND),
         print_empty(I,FS,Dtrs,RuleName,ND,Residue)).

print_empty(I,FS,Dtrs,RuleName,ND,Residue) :-
  ((current_predicate(portray_empty,portray_empty(_,_,_,_,_,_)),
    portray_empty(I,FS,Dtrs,RuleName,ND,Residue)) -> true
  ; nl, write('EMPTY CATEGORY: '), 
    pp_fs_res_col(FS,Residue,4),
    (ale_flag(interp,off) 
    -> true
     ; nl, write('     index: '),(functor(I,empty,2)
                                 -> arg(1,I,E),
                                    write(E)
                                  ; write(I)),
       nl, write('      rule: '),write(RuleName),
       nl, write(' # of dtrs: '),write(ND)
    ),
    nl
  ),
  (ale_flag(interp,off) -> query_proceed
  ; query_empty(I,FS,Dtrs,RuleName,ND,Residue)
  ).

query_empty(I,FS,Dtrs,RuleName,ND,Res) :-
  write('Action(dtr-#,continue,abort)? '),
  nl,read(Response),
  query_empty_act(Response,I,FS,Dtrs,RuleName,ND,Res).

query_empty_act(continue,_,_,_,_,_,_) :-
  !,fail.
query_empty_act(abort,_,_,_,_,_,_) :-
  !,abort.
query_empty_act(dtr-D,I,FS,Dtrs,RuleName,ND,Res) :-
  nth_index(Dtrs,D,empty(DI,-1),-1,-1,DFS,DDtrs,DRule,DResidue),
  !,length(DDtrs,DND),
  ( print_empty(DI,DFS,DDtrs,DRule,DND,DResidue)
  ; print_empty(I,FS,Dtrs,RuleName,ND,Res)
  ).
query_empty_act(_,I,FS,Dtrs,RuleName,ND,Res) :-
  !,query_empty(I,FS,Dtrs,RuleName,ND,Res).


% ------------------------------------------------------------------------------
% edge(N:<int>, M:<int>)
% ------------------------------------------------------------------------------
% prints out edges from N to M, querying user in between
% ------------------------------------------------------------------------------
num(N) :-			% for backwards compatibility
  print_message(informational,ale_deprec(num/1,edgenum/1)),
  edgenum(N).  

edgenum(N) :-
    var(N) -> clause(edgenum(N,_),true)
  ; integer(N), N>=0 -> clause(edgenum(N,_),true)
  ; raise_exception(domain_error(edgenum(N),1,int>=0,N)).

edge(I) :-
  \+ \+ (edge_by_index(I,M,N,FS,Residue,Dtrs,RuleName),
         print_asserted_edge(I,M,N,FS,Dtrs,RuleName,Residue)).
edge(M,N) :-
  \+ \+ (edge_by_subspan(M,N,I,FS,Residue,Dtrs,RuleName),
         print_asserted_edge(I,M,N,FS,Dtrs,RuleName,Residue)).
edge(M,N,FS) :-
  edge(M,N,FS,_).
edge(M,N,FS,Residue) :-
  edge_by_subspan(M,N,_,FS,Residue,_,_).
edge(I,M,N,FS,Residue) :-
  edge_by_index(I,M,N,FS,Residue,_,_).
% edge(I,M,N,FS,Residue,Dtrs,RuleName): these are asserted during the build/3 loop
edge(I,M,N,FS,Dtrs,RuleName,Residue) :-
  edge_by_index(I,M,N,FS,Residue,Dtrs,RuleName).

edge_by_index(I,M,N,FS,Residue,Dtrs,RuleName) :-
    var(I) -> edge_by_subspan(M,N,I,FS,Residue,Dtrs,RuleName)
  ; integer(I) -> ( I < 0 -> call_residue((empty_cat(I,N,FS,Dtrs,RuleName), M=N),FS,Residue)
		  ; call_with_residue(clause(edge(I,M,N,FS,EResidue,Dtrs,RuleName),true),EResidue,Residue)
		  )
  ; raise_exception(type_error(edge(I),1,integer,I)).

edge_by_subspan(M,N,I,FS,Residue,Dtrs,RuleName):-
  ( var(M) -> ( var(N) -> edge_by_subspan_var(M,N,I,FS,Residue,Dtrs,RuleName)
	      ; ( integer(N) -> ( N>=0 -> edge_by_subspan_var(M,N,I,FS,Residue,Dtrs,RuleName)
                ; raise_exception(domain_error(edge(M,N),2,int>=0,N)))
	        ; raise_exception(type_error(edge(M,N),2,integer,N)))
	      )
  ; var(N) -> ( integer(M) -> (M>=0 -> edge_by_subspan_var(M,N,I,FS,Residue,Dtrs,RuleName)
	      ; raise_exception(domain_error(edge(M,N),1,int>=0,M)))
	      ; raise_exception(type_error(edge(M,N),1,integer,M))
	      )
  ; ( integer(M) -> ( M>=0 ->
    ( integer(N) -> ( N>=0 ->
       ( M > N -> raise_exception(consistency_error(edge(M,N),M,N,'{ALE: M <= N in edge(M,N)}'))
       ; M == N -> call_residue(empty_cat(I,N,FS,Dtrs,RuleName),FS,Residue)
       ; call_with_residue(clause(edge(I,M,N,FS,EResidue,Dtrs,RuleName),true),EResidue,Residue) % not indexed
       )
    ; raise_exception(domain_error(edge(M,N),2,int>=0,N)))
    ; raise_exception(type_error(edge(M,N),2,integer,N)))
    ; raise_exception(domain_error(edge(M,N),1,int>=0,M)))
    ; raise_exception(type_error(edge(M,N),1,integer,M)))
  ).

edge_by_subspan_var(M,N,I,FS,Residue,Dtrs,RuleName) :-
   M = N, call_residue(empty_cat(I,N,FS,Dtrs,RuleName),FS,Residue)
 ; call_with_residue(clause(edge(I,M,N,FS,EResidue,Dtrs,RuleName),true),EResidue,Residue). % not indexed

print_asserted_edge(I,M,N,FS,Dtrs,RuleName,Residue) :-		 
  nl, write('COMPLETED CATEGORY SPANNING: '),
  write_parsing_substring(M,N),
  nl, print_asserted_edge_act(I,M,N,FS,Dtrs,RuleName,Residue).

print_asserted_edge_act(I,M,N,FS,Dtrs,RuleName,Residue) :-
  length(Dtrs,ND),
  print_asserted_edge_act(I,M,N,FS,Dtrs,RuleName,ND,Residue).

print_asserted_edge_act(I,M,N,FS,Dtrs,RuleName,ND,Residue) :-
  ((current_predicate(portray_edge,portray_edge(_,_,_,_,_,_,_)),
    portray_edge(I,M,N,FS,RuleName,ND,Residue)) -> true
  ; nl,pp_fs_res(FS,Residue),
    (ale_flag(interp,off)
    -> true
     ; nl,write('Edge created for category above: '),
       nl,write('     index: '),(functor(I,empty,2)
                                -> arg(1,I,E),
                                   write(E)
                                 ; write(I)),
       nl,write('      from: '),write(M),write(' to: '),write(N),
       nl,write('    string: '),write_parsing_substring(M,N),
       nl,write('      rule:  '),write(RuleName),
       nl,write(' # of dtrs: '),write(ND)
    ),
    nl
  ),
  (ale_flag(interp,off) -> query_proceed
  ; query_asserted_edge(I,M,N,FS,Dtrs,RuleName,ND,Residue)
  ).

query_asserted_edge(I,M,N,FS,Dtrs,RuleName,ND,Res) :-
  nl,
  ( M == N -> write('Action(dtr-#,continue,abort)? ') % can't retract empty cats
  ; write('Action(retract,dtr-#,continue,abort)? ')
  ),
  nl,read(Response),
  query_asserted_edge_act(Response,I,M,N,FS,Dtrs,RuleName,ND,Res).

query_asserted_edge_act(retract,I,M,N,_,_,_,_,_) :-
  N \== M,
  retract(edge(I,M,_,_,_,_,_)), % can't retract empty cats
  !,fail.
query_asserted_edge_act(dtr-D,I,M,N,FS,Dtrs,RuleName,ND,Res) :-
  nth_index(Dtrs,D,DI,DLeft,DRight,DFS,DDtrs,DRule,DResidue),
  !,length(DDtrs,DND),
  print_dtr_edge(D,DI,DLeft,DRight,DFS,DDtrs,DRule,DND,DResidue),
  print_asserted_edge_act(I,M,N,FS,Dtrs,RuleName,ND,Res).
query_asserted_edge_act(continue,_,_,_,_,_,_,_,_) :-
  !,fail.
query_asserted_edge_act(abort,_,_,_,_,_,_,_,_) :-
  !,abort.
query_asserted_edge_act(_,I,M,N,FS,Dtrs,RuleName,ND,Res) :-
  query_asserted_edge(I,M,N,FS,Dtrs,RuleName,ND,Res).

write_parsing_substring(M,N):-
  parsing(Ws),
  all_but_first(M,Ws,WsRest),
  K is N-M,
  write_first(K,WsRest).

all_but_first(0,Ws,Ws):-!.
all_but_first(M,[_|Ws],WsOut):-
  K is M-1,
  all_but_first(K,Ws,WsOut).

write_first(0,_):-!.
write_first(N,[W|Ws]):-
  write(W), write(' '),
  K is N-1,
  write_first(K,Ws).

% ------------------------------------------------------------------------------
% lex_rule(RuleName:<name>)
% ------------------------------------------------------------------------------
% Displays lexical rule with name RuleName
% ------------------------------------------------------------------------------
lex_rule(RuleName):-
%  \+ \+
%  lexrule2(RuleName).
%lexrule2(RuleName):-
   ( (RuleName lex_rule Desc1 **> Desc2 if Cond morphs Morphs)
   ; (RuleName lex_rule Desc1 **> Desc2 morphs Morphs),
     Cond = true
   ),
   empty_avl(AssocIn),
   call_residue((add_to(Desc1,FS1),
                 add_to(Desc2,FS2),
                 nv_replace_body(Cond,Goal,Args,[],AssocIn),
                 ArgsOut = [FS1,FS2|Args]),ArgsOut,Residue),
   \+ \+ (((current_predicate(portray_lex_rule,portray_lex_rule(_,_,_,_,_,_,_,_,_,_)),
	    portray_lex_rule(RuleName,Desc1,Desc2,FS1,FS2,Residue,Goal,Morphs,Args,Cond)) -> true
	  ; filter_iqs(Residue,Iqs,FSResidue),
	    nl, write('LEX RULE: '), write(RuleName), 
            (ale_flag(residue,show) -> residue_args(FSResidue,ResArgs,ArgsOut) ; ResArgs = ArgsOut),
            duplicates_list(ResArgs,AssocIn,DupsMid,AssocIn,VisMid,0,NumMid),
	    duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,Inf,NumMid,_),
            nl, write('INPUT CATEGORY: '), 
            nl, tab(4), pp_fs(FS1,DupsOut,Inf,AssocIn,VisMid2,4,AssocIn,HDMid),
            nl, write('OUTPUT CATEGORY: '),
            nl, tab(4), pp_fs(FS2,DupsOut,Inf,VisMid2,VisMid3,4,HDMid,HDMid2),
            ( Cond = true
            -> VisMid4 = VisMid3, HDMid3 = HDMid2
            ; nl, write('CONDITION: '), 
              nl, tab(4), pp_goal(Goal,DupsOut,Inf,VisMid3,VisMid4,4,HDMid2,HDMid3)
  	    ),
            nl, write('MORPHS: '),
            numbervars(Morphs,0,_),
            pp_morphs(Morphs),
	    nl, nl, tab(4), pp_iqs(Iqs,DupsOut,Inf,VisMid4,VisOut,4,HDMid3,HDOut),
            ((ale_flag(residue,show),FSResidue \== [])
	    -> nl,nl, write('Residue:'), pp_residue(FSResidue,DupsOut,Inf,VisOut,_,HDOut,_)
	    ; true
  	    ),nl
	  ),
          query_proceed).

pp_morphs((Morph,Morphs)):-
  !, nl, tab(4), pp_morph(Morph),
  pp_morphs(Morphs).
pp_morphs(Morph):-
  nl, tab(4), pp_morph(Morph).

pp_morph((P1 becomes P2)):-
  pp_patt(P1), write(' becomes '), pp_patt(P2).
pp_morph((P1 becomes P2 when Cond)):-
  pp_patt(P1), write(' becomes '), pp_patt(P2),
  nl, tab(8), write('when '), write(Cond).
  
pp_patt((X,Xs)):-
  !, pp_at_patt(X), write(','),
  pp_patt(Xs).
pp_patt(X):-
  pp_at_patt(X).

pp_at_patt(Atom):-
 atom(Atom),
  !, name(Atom,Codes),
  make_char_list(Codes,Chars),
  write(Chars).
pp_at_patt(List):-
  write(List).

% ------------------------------------------------------------------------------
% show_clause(PredSpec:<predspec>)
% ------------------------------------------------------------------------------
% Displays ALE definite clause source code
% ------------------------------------------------------------------------------
show_clause(Spec):-
  ( (nonvar(Spec),Spec = Name/Arity) -> true
  ; Spec = Name
  ),
  empty_avl(EAssoc),
  (Head if Body),
  functor(Head,Name,Arity),
  ((current_predicate(portray_ale_clause,portray_ale_clause(_,_)),
    portray_ale_clause(Head,Body)) -> true
  ; nl, write('HEAD: '), pp_goal(Head,EAssoc,_,EAssoc,_,6,EAssoc,_),
    nl, write('BODY: '), pp_goal(Body,EAssoc,_,EAssoc,_,6,EAssoc,_),nl
  ),
  query_proceed.

% ------------------------------------------------------------------------------
% rule(RuleName:<name>)
% ------------------------------------------------------------------------------
% Displays rule with name RuleName
% ------------------------------------------------------------------------------
rule(BaseRuleName):-
%  (RuleName rule Moth ===> DtrsDesc),
  \+ \+ (( nonvar(BaseRuleName) -> name(BaseRuleName,BaseRuleNameString) ; true ),
         call_with_residue(clause(alec_rule(RuleName,DtrsDesc,_,Moth,EResidue,_,_,_,_),true),EResidue,Residue),
         % HACK: prob shouldn't just suppress DtrStore
         ( BaseRuleName = RuleName   % although it is clear that they can't simply be printed like Dtrs
         -> true
         ; name(RuleName,RuleNameString),
           append(BaseRuleNameString,[47,47|_],RuleNameString) % strip off EFD suffix "//N"
         ),
         nl, write('RULE: '), write(RuleName), 
         empty_avl(AssocIn),  
         call_residue((satisfy_dtrs(DtrsDesc,DtrCats,[],Dtrs,gdone),
		       add_to(Moth,FSMoth),
                       CatsOut = [FSMoth|DtrCats]),CatsOut,Residue),
         ((current_predicate(portray_rule,portray_rule(_,_,_,_,_)),
	   portray_rule(RuleName,FSMoth,DtrsDesc,Dtrs,Residue)) -> true
	 ; filter_iqs(Residue,Iqs,FSResidue),
	   (ale_flag(residue,show) -> residue_args(FSResidue,ResArgs,CatsOut) ; ResArgs = CatsOut),
           duplicates_list(ResArgs,AssocIn,DupsMid,AssocIn,VisMid,0,NumMid),
  	   duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,Inf,NumMid,_),
           nl, nl, write('MOTHER: '), nl,
           nl, tab(2), pp_fs(FSMoth,DupsOut,Inf,AssocIn,VisMid2,2,AssocIn,HDMid),
           nl, nl, write('DAUGHTERS/GOALS: '),   
           show_rule_dtrs(Dtrs,DupsOut,Inf,VisMid2,VisMid3,HDMid,HDMid2),
	   nl,nl, tab(2), pp_iqs(Iqs,DupsOut,Inf,VisMid3,VisOut,2,HDMid2,HDOut),
  	   ((ale_flag(residue,show),FSResidue \== [])
  	   -> nl, nl, write('Residue:'), pp_residue(FSResidue,DupsOut,Inf,VisOut,_,HDOut,_)
           ; true), nl
	 ),
         query_proceed).

show_rule_dtrs([],_Dups,_Inf,Vis,Vis,HD,HD).
show_rule_dtrs([(cat> C)|Dtrs],Dups,Inf,VisIn,VisOut,HDIn,HDOut):-
  !,nl, nl, write('CAT  '), pp_fs(C,Dups,Inf,VisIn,VisMid,5,HDIn,HDMid),
  show_rule_dtrs(Dtrs,Dups,Inf,VisMid,VisOut,HDMid,HDOut).
% 5/1/96 - Octav -- added clause for sem_head> label
show_rule_dtrs([(sem_head> C)|Dtrs],Dups,Inf,VisIn,VisOut,HDIn,HDOut):-
  !,nl, nl, write('SEM_HEAD  '), pp_fs(C,Dups,Inf,VisIn,VisMid,10,HDIn,HDMid),
  show_rule_dtrs(Dtrs,Dups,Inf,VisMid,VisOut,HDMid,HDOut).
show_rule_dtrs([(cats> Cs)|Dtrs],Dups,Inf,VisIn,VisOut,HDIn,HDOut):-
  !,nl, nl, write('CATs '), pp_fs(Cs,Dups,Inf,VisIn,VisMid,5,HDIn,HDMid),
  show_rule_dtrs(Dtrs,Dups,Inf,VisMid,VisOut,HDMid,HDOut).
show_rule_dtrs([(goal> G)|Dtrs],Dups,Inf,VisIn,VisOut,HDIn,HDOut):-
  !,nl, nl, write('GOAL  '), pp_goal(G,Dups,Inf,VisIn,VisMid,6,HDIn,HDMid),
  show_rule_dtrs(Dtrs,Dups,Inf,VisMid,VisOut,HDMid,HDOut).
% 6/1/97 - Octav -- added clause for sem_goal> label
show_rule_dtrs([(sem_goal> G)|Dtrs],Dups,Inf,VisIn,VisOut,HDIn,HDOut):-
  nl, nl, write('SEM_GOAL  '), pp_goal(G,Dups,Inf,VisIn,VisMid,10,HDIn,HDMid),
  show_rule_dtrs(Dtrs,Dups,Inf,VisMid,VisOut,HDMid,HDOut).

satisfy_dtrs((cat> Desc),[FS|DtrCatsRest],DtrCatsRest,
             [(cat> FS)],Goals):-
  !, add_to(Desc,FS),
  nv_replace_goals(Goals).  % must postpone to make sure all variables that
                            %  will be instantiated are instantiated.
% 5/1/96 - Octav -- added clause for sem_head> label
satisfy_dtrs((sem_head> Desc),[FS|DtrCatsRest],DtrCatsRest,
             [(sem_head> FS)],Goals):-
  !, add_to(Desc,FS),
  nv_replace_goals(Goals).
satisfy_dtrs((cats> Descs),[FS|DtrCatsRest],DtrCatsRest,
             [(cats> FS)],Goals) :-
  !, add_to(Descs,FS),
  nv_replace_goals(Goals).
satisfy_dtrs(remainder(RFS),[RFS|DtrCatsRest],DtrCatsRest,
	     [(cats> RFS)],Goals) :-
  !, nv_replace_goals(Goals).
satisfy_dtrs((goal> GoalDesc),DtrCats,DtrCatsRest,
             [(goal> Goal)],Goals):-
  !, nv_replace_goals(goal(GoalDesc,Goal,DtrCats,DtrCatsRest,Goals)).
  % satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsRest,Goal,IqsIn,IqsOut).
% 6/1/97 - Octav -- added clause for sem_goal> label
satisfy_dtrs((sem_goal> GoalDesc),DtrCats,DtrCatsRest,
             [(sem_goal> Goal)],Goals):-
  !, nv_replace_goals(goal(GoalDesc,Goal,DtrCats,DtrCatsRest,Goals)).
  % satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsRest,Goal,IqsIn,IqsOut).
satisfy_dtrs(((cat> Desc),Dtrs),[FS|DtrCatsMid],DtrCatsRest,
             [(cat> FS)|DtrsSats],Goals):-
  !, add_to(Desc,FS),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,Goals).
% 5/1/96 - Octav -- added clause for sem_head> label
satisfy_dtrs(((sem_head> Desc),Dtrs),[FS|DtrCatsMid],DtrCatsRest,
             [(sem_head> FS)|DtrsSats],Goals):-
  !, add_to(Desc,FS),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,Goals).
satisfy_dtrs(((cats> Descs),Dtrs),[FS|DtrCatsMid],DtrCatsRest,
             [(cats> FS)|DtrsSats],Goals):-
  !, add_to(Descs,FS),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,Goals).
satisfy_dtrs((remainder(RFS),Dtrs),[RFS|DtrCatsMid],DtrCatsRest,
	     [(cats> RFS)|DtrsSats],Goals) :-
  !, satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,Goals).
satisfy_dtrs(((goal> GoalDesc),Dtrs),DtrCats,DtrCatsRest,
              [goal> Goal|DtrsSats],Goals):-
%  satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsMid,Goal,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,
               goal(GoalDesc,Goal,DtrCats,DtrCatsMid,Goals)).
% 6/1/97 - Octav -- added clause for sem_goal> label
satisfy_dtrs(((sem_goal> GoalDesc),Dtrs),DtrCats,DtrCatsRest,
              [sem_goal> Goal|DtrsSats],Goals):-
%  satisfy_dtrs_goal(GoalDesc,DtrCats,DtrCatsMid,Goal,IqsIn,IqsMid),
  satisfy_dtrs(Dtrs,DtrCatsMid,DtrCatsRest,DtrsSats,
	       goal(GoalDesc,Goal,DtrCats,DtrCatsMid,Goals)).

%satisfy_dtrs_goal((GD1,GD2),DtrCats,DtrCatsRest,
%                  (G1,G2),IqsIn,IqsOut,NVs):-
%  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid,NVs),
%  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut,NVs).
%satisfy_dtrs_goal((GD1 -> GD2 ; GD3),DtrCats,DtrCatsRest,
%                  (G1 -> G2 ; G3),IqsIn,IqsOut,NVs) :-
%  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid,NVs),
%  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsMid2,G2,IqsMid,IqsMid2,NVs),
%  satisfy_dtrs_goal(GD3,DtrCatsMid2,DtrCatsRest,G3,IqsMid2,IqsOut,NVs).
%satisfy_dtrs_goal((GD1;GD2),DtrCats,DtrCatsRest,(G1;G2),IqsIn,IqsOut,NVs):-
%  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid,NVs),
%  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut,NVs).
%satisfy_dtrs_goal((\+ GD1),DtrCats,DtrCatsRest,(\+ G1),IqsIn,IqsOut,NVs):-
%  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsRest,G1,IqsIn,IqsOut,NVs).
%satisfy_dtrs_goal(prolog(Hook),DtrCats,DtrCats,prolog(Hook),Iqs,Iqs,_) :-
%  !.
%satisfy_dtrs_goal(when(Cond,Body),DtrCats,DtrCatsRest,when(NCond,NBody),Iqs,Iqs,NVs) :-
%  !, satisfy_dtrs_cond(Cond,NCond,Body,NBody,DtrCats,DtrCatsRest,NVs).
%satisfy_dtrs_goal((GD1 -> GD2),DtrCats,DtrCatsRest,(G1 -> G2),IqsIn,IqsOut,NVs) :-
%  !, satisfy_dtrs_goal(GD1,DtrCats,DtrCatsMid,G1,IqsIn,IqsMid,NVs),
%  satisfy_dtrs_goal(GD2,DtrCatsMid,DtrCatsRest,G2,IqsMid,IqsOut,NVs).
%satisfy_dtrs_goal(AtGD,DtrCats,DtrCatsRest,AtG,IqsIn,IqsOut,NVs):-
%  AtGD =.. [Rel|ArgDescs],
%  same_length(ArgDescs,Args),
%  AtG =.. [Rel|Args],
%  satisfy_dtrs_goal_args(ArgDescs,DtrCats,DtrCatsRest,Args,IqsIn,IqsOut,NVs).

%satisfy_dtrs_goal_args([],DtrCats,DtrCats,[],Iqs,Iqs,_).
%satisfy_dtrs_goal_args([D|Ds],[Tag-bot|DtrCats],DtrCatsRest,[Tag-bot|Args],
%                       IqsIn,IqsOut):-
%  add_to(D,Tag,bot,IqsIn,IqsMid),
%  satisfy_dtrs_goal_args(Ds,DtrCats,DtrCatsRest,Args,IqsMid,IqsOut).
  

% ==============================================================================
% Pretty Printing
% ==============================================================================

% ------------------------------------------------------------------------------
% pp_fs(FS:<fs>,Iqs:<ineq>s)
% ------------------------------------------------------------------------------
% pretty prints FS with inequations Iqs
% ------------------------------------------------------------------------------
pp_fs(FS):-
  pp_fs_col(FS,0,0).
%pp_fs(Ref,SVs) :-
%  pp_fs_col(Ref,SVs,0).

pp_fs(FS,MGType) :-
  pp_fs_col(FS,0,MGType).
	
pp_fs_col(FS,N,MGType):-
  \+ \+ ( empty_assoc(AssocIn),
          duplicates(FS,MGType,AssocIn,Dups,AssocIn,Inf,0,_,_),
          nl, 
          tab(N), pp_fs(FS,MGType,Dups,Inf,AssocIn,_,N,AssocIn,_)).
%pp_fs_col(Ref,SVs,N):-
%  \+ \+ ( empty_avl(AssocIn),
%          duplicates(Ref,SVs,AssocIn,DupsMid,AssocIn,_,0,_),
%          nl, 
%          tab(N), pp_fs(Ref,SVs,DupsMid,_,AssocIn,_,N,AssocIn,_)).

pp_fs_res(FS,Residue) :-
  pp_fs_res_col(FS,Residue,0,0).

pp_fs_res(FS,Residue,MGType) :-
  pp_fs_res_col(FS,Residue,0,MGType).

pp_fs_res_col(FS,Residue,Col) :-
  pp_fs_res_col(FS,Residue,Col,0).

pp_fs_res_col(FS,Residue,Col,MGType) :-
  empty_avl(AssocIn),
  filter_iqs(Residue,Iqs,FSResidue),
  (ale_flag(residue,show) -> residue_args(FSResidue,ResArgs,[FS]) ; ResArgs = [FS]),
  duplicates_list(ResArgs,AssocIn,DupsMid,AssocIn,VisMid,0,NumMid),
  duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,Inf,NumMid,_),
  pp_fs(FS,MGType,DupsOut,Inf,AssocIn,VisMid2,Col,AssocIn,HDMid),
  nl,nl,
  tab(Col), pp_iqs(Iqs,DupsOut,Inf,VisMid2,VisOut,0,HDMid,HDOut),
  ((ale_flag(residue,show),FSResidue\==[])
  -> nl,nl, write('Residue:'), pp_residue(FSResidue,DupsOut,Inf,VisOut,_,HDOut,_)
  ; true
  ).

% ------------------------------------------------------------------------------
% duplicates(FS:<fs>, Iqs:<ineq>s, 
%            VisIn:<ref>s, VisOut:<ref>s, NumIn:<int>, NumOut:<int>)
% ------------------------------------------------------------------------------
% DupsOut is the result of adding the duplicate references
% in FS and Iqs to those in DupsIn.  VisIn are those nodes already
% visited and VisOut are those visited in FS.  NumIn is
% the current number for variables and NumOut is the
% next available after numbering only the shared refs in FS.
% ------------------------------------------------------------------------------
%duplicates(FS,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut) :-
%  duplicates_fs(FS,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid).
%  duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).
%duplicates(Ref,SVs,Iqs,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut) :-
%  duplicates_fs(Ref,SVs,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid),
%  duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).

%duplicates(FS,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut):-
%  ( avl_fetch(FS,DupsIn,_) -> VisOut = VisIn, NumOut = NumIn, DupsOut = DupsIn
%  ; avl_fetch(FS,VisIn,_) -> avl_store(FS,DupsIn,NumIn,DupsOut), NumOut is NumIn + 1, VisOut = VisIn
%  ; get_type(FS,Type), approps(Type,FRs,_),
%    avl_store(FS,VisIn,_,VisMid),
%    get_vals(FRs,FS,Vs),
%    duplicates_list(Vs,DupsIn,DupsOut,VisMid,VisOut,NumIn,NumOut)).  % HACK: should compile get_vals/3
%                                                       % plus this into a series of duplicates/7 calls.

duplicates(FS,R,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut,MotherInfFlag):-
  ( avl_fetch(FS,DupsIn,_) -> VisOut = VisIn, NumOut = NumIn, DupsOut = DupsIn, MotherInfFlag = inform
  ; avl_fetch(FS,VisIn,InfFlag) -> avl_store(FS,DupsIn,NumIn,DupsOut), NumOut is NumIn + 1, VisOut = VisIn,
                                   InfFlag = inform, MotherInfFlag = inform
  ; get_type(FS,Type),
    ( Type == 0 -> true
    ; sub_type(Type,R) -> true 
    ; InfFlag = inform
    ),
    approps(Type,FRs,_),
    avl_store(FS,VisIn,InfFlag,VisMid),
    when(nonvar(InfFlag),MotherInfFlag = inform),
    duplicates_vals(FRs,FS,DupsIn,DupsOut,VisMid,VisOut,NumIn,NumOut,InfFlag)
  ).

duplicates_vals([],_,Dups,Dups,Vis,Vis,Num,Num,_).
duplicates_vals([F:R|FRs],FS,DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut,MotherInfFlag):-
  clause(fcolour(F,K,_),true), arg(K,FS,V),
  duplicates(V,R,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid,MotherInfFlag),
  duplicates_vals(FRs,FS,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut,MotherInfFlag).

duplicates_list([],Dups,Dups,Vis,Vis,Num,Num).
duplicates_list([V|Vs],DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut):-
  duplicates(V,bot,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid,_),
  duplicates_list(Vs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).

duplicates_iqs([],Dups,Dups,Vis,Vis,Num,Num).
duplicates_iqs([Iq|Iqs],DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut) :-
  duplicates_ineq(Iq,DupsIn,DupsMid,VisIn,VisMid,NumIn,NumMid),
  duplicates_iqs(Iqs,DupsMid,DupsOut,VisMid,VisOut,NumMid,NumOut).

duplicates_ineq(ineq(FS1,FS2),DupsIn,DupsOut,VisIn,VisOut,NumIn,NumOut):-
  duplicates(FS1,bot,DupsIn,DupsMid1,VisIn,VisMid1,NumIn,NumMid1,_),
  duplicates(FS2,bot,DupsMid1,DupsOut,VisMid1,VisOut,NumMid1,NumOut,_).

% ------------------------------------------------------------------------------
% pp_iqs(Iqs:<ineq>s, VisIn:<var>s, VisOut:<var>s,Col:<int>)
% ------------------------------------------------------------------------------
% pretty-prints a list of inequations, indented Col columns
%-------------------------------------------------------------------------------
pp_iqs([],_Dups,_Inf,Vis,Vis,_,HD,HD).
pp_iqs([Iq|Iqs],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  write('('),
  pp_ineq(Iq,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
  write(')'),
  (Iqs = []
   -> nl
   ; write(','),
     nl,
     pp_iqs(Iqs,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut)).

% ineq(Tag1,SVs1,Tag2,SVs2,Ineqs)
pp_ineq(ineq(FS1,FS2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  tab(Col),pp_fs(FS1,Dups,Inf,VisIn,VisMid1,Col,HDIn,HDMid1),
  write('  =\\=  '),
  NewCol is Col+7,
  pp_fs(FS2,Dups,Inf,VisMid1,VisOut,NewCol,HDMid1,HDOut),
  nl.
%  pp_ineq(Ineqs,DupsMid2,DupsOut,VisMid2,VisOut,Col,HDMid2,HDOut).

% ------------------------------------------------------------------------------
% frozen_term(+Term,-Goals)
% ------------------------------------------------------------------------------
% Extended version of built-in frozen/2, which finds frozen Goals for all
%  variables in any Prolog Term.
% ------------------------------------------------------------------------------
frozen_term(Var,Frozen) :-
  var(Var),
  !,frozen(Var,Goal),
  filter_goals(Goal,UnsortedRes,[],Var),
  sort(UnsortedRes,Frozen).
frozen_term(Term,Frozen) :-
  term_variables(Term,Vars),
  frozen_term_act(Vars,UnsortedRes),
  sort(UnsortedRes,Frozen).

frozen_term_act([],[]).
frozen_term_act([Var|Vars],Frozen) :-
  frozen(Var,Goal),
  filter_goals(Goal,Frozen,Rest,Var),
  frozen_term_act(Vars,Rest).

filter_goals(true,Rest,Rest,_) :- !.
filter_goals((G1,G2),Frozen,Rest,Var) :-
  !,filter_goals(G1,Frozen,Mid,Var),
  filter_goals(G2,Mid,Rest,Var).
filter_goals(prolog:trig_nondif(A,B,C,Trig),[[Var]-prolog:trig_nondif(A,B,C,Trig)|Frozen],
	     Rest,Var) :-
  !,frozen(Trig,Goal),
  filter_goals(Goal,Frozen,Rest,Trig).
filter_goals(prolog:trig_and(A,B,C,D,Trig),[[Var]-prolog:trig_and(A,B,C,D,Trig)|Frozen],
	     Rest,Var) :-
  !,frozen(Trig,Goal),
  filter_goals(Goal,Frozen,Rest,Trig).
filter_goals(prolog:trig_or(A,B,Trig),[[Var]-prolog:trig_or(A,B,Trig)|Frozen],Rest,Var) :-
  !,frozen(Trig,Goal),
  filter_goals(Goal,Frozen,Rest,Trig).
filter_goals(G,[[Var]-G|Rest],Rest,Var).

residue_args([],Args,Args).
residue_args([_-Goal|Residue],Args,ArgsRest) :-
  resgoal_args(Goal,Args,ArgsMid),
  residue_args(Residue,ArgsMid,ArgsRest).

%resgoal_args(prolog:when(_,_,user:when_eq0(FS1,Tag2,SVs2,WGoal)),
%	     [FS1,Tag2-SVs2|Args],ArgsRest) :-
%  !,resgoal_args_wgoal(WGoal,Args,ArgsRest).
%resgoal_args(prolog:when(_,_,user:when_eq0(Tag1,SVs1,Tag2,SVs2,WGoal)),
%	     [Tag1-SVs1,Tag2-SVs2|Args],ArgsRest) :-
%  !,resgoal_args_wgoal(WGoal,Args,ArgsRest).
%resgoal_args(prolog:when(_,_,user:when_eq_a2(X1,X2,Tag1,Tag2,WGoal)),  
%	     [Tag1-(a_ X1),Tag2-(a_ X2)|Args],ArgsRest) :-
%  !,resgoal_args_wgoal(WGoal,Args,ArgsRest).
%resgoal_args(prolog:when(_,_,user:when_type0(_,FS,WGoal)),Args,Rest) :-
%  !,(var(FS) -> ArgsMid = Args ; Args = [FS|ArgsMid]),
%  resgoal_args_wgoal(WGoal,ArgsMid,Rest).
resgoal_args(prolog:when(_,_,user:when_type_delayed0(_,FS,_,WGoal)),[FS|Args],ArgsRest) :-
  !,resgoal_args_wgoal(WGoal,Args,ArgsRest).   % Must look in WGoal too
resgoal_args(_,Args,Args).

resgoal_args_wgoal(Var,Args,ArgsRest) :-
  var(Var),
  !,Args = [Var|ArgsRest].  % if unattributed, we'll interpret these as FSs of type bot.
resgoal_args_wgoal((G1 -> G2 ; G3),Args,ArgsRest) :-
  !,resgoal_args_wgoal(G1,Args,ArgsMid),
  resgoal_args_wgoal(G2,ArgsMid,ArgsMid2),
  resgoal_args_wgoal(G3,ArgsMid2,ArgsRest).
resgoal_args_wgoal((G1 -> G2),Args,ArgsRest) :-
  !,resgoal_args_wgoal(G1,Args,ArgsMid),
  resgoal_args_wgoal(G2,ArgsMid,ArgsRest).
resgoal_args_wgoal((G1,G2),Args,ArgsRest) :-
  !,resgoal_args_wgoal(G1,Args,ArgsMid),
  resgoal_args_wgoal(G2,ArgsMid,ArgsRest).
resgoal_args_wgoal((G1;G2),Args,ArgsRest) :-
  !,resgoal_args_wgoal(G1,Args,ArgsMid),
  resgoal_args_wgoal(G2,ArgsMid,ArgsRest).
resgoal_args_wgoal(\+ G1,Args,ArgsRest) :-
  !,resgoal_args_wgoal(G1,Args,ArgsRest).
resgoal_args_wgoal(when_type(_,FS,WGoal),Args,ArgsRest) :-
  !,Args = [FS|ArgsMid],
  resgoal_args_wgoal(WGoal,ArgsMid,ArgsRest).
resgoal_args_wgoal(when_a_(_,FS,WGoal),Args,ArgsRest) :-
  !,Args = [FS|ArgsMid],
  resgoal_args_wgoal(WGoal,ArgsMid,ArgsRest).
resgoal_args_wgoal(when_eq(FS,Var,WGoal),Args,ArgsRest) :-
  !,Args = [FS,Var|ArgsMid2],
  resgoal_args_wgoal(WGoal,ArgsMid2,ArgsRest).
resgoal_args_wgoal((Arg1=Arg2),Args,ArgsRest) :-
  !, ( integer(Arg2) -> Args = ArgsRest  % This is a disjunctive switch for when/2
     ; Args = [Arg1,Arg2|ArgsRest] % Otherwise, user did it: treat as FSs
     ).
resgoal_args_wgoal(arg(_N,FS1,FS2),Args,ArgsRest) :-
  !, Args = [FS1,FS2|ArgsRest].
resgoal_args_wgoal(deref(FS,_,_,_),Args,ArgsRest) :-
  !,Args = [FS|ArgsRest].
%resgoal_args_wgoal(FGoal,Args,ArgsRest) :-  % prob. need an arg/3 clause in place of this.
%  FGoal =.. [FRel|FGoalArgs],
%  name(FRel,FRelName),
%  append("featval_",_,FRelName),
%  !, FGoalArgs = [SVs,Tag,ValatF],
%  ( var(SVs) -> Args = ArgsMid ; Args = [Tag-SVs|ArgsMid]),
%  ( var(ValatF) -> ArgsMid = ArgsRest ; ArgsMid = [ValatF|ArgsRest]).
resgoal_args_wgoal(Goal,Args,ArgsRest) :-
  Goal =.. [_|GoalArgs],
  resgoal_args_wargs(GoalArgs,Args,ArgsRest).

resgoal_args_wargs([],Args,Args).
resgoal_args_wargs([GA|GArgs],Args,ArgsRest) :-
  Args = [GA|ArgsMid],
  resgoal_args_wargs(GArgs,ArgsMid,ArgsRest).

pp_residue([],_Dups,_Inf,Vis,Vis,HD,HD).
pp_residue([_-Goal|Residue],Dups,Inf,VisIn,VisOut,HDIn,HDOut) :-
  ( (current_predicate(portray_resgoal,portray_resgoal(_,_,_,_,_,_,_)),
     portray_resgoal(Goal,Dups,Inf,VisIn,VisMid,HDIn,HDMid))
  -> true
  ; pp_resgoal(Goal,Dups,Inf,VisIn,VisMid,HDIn,HDMid)
  ),
  pp_residue(Residue,Dups,Inf,VisMid,VisOut,HDMid,HDOut).

% pp_resgoal(prolog:trig_nondif(_,_,_,_),Dups,Dups,Vis,Vis,HD,HD) :- !.
% pp_resgoal(prolog:trig_or(_,_,_),Dups,Dups,Vis,Vis,HD,HD) :- !.
%pp_resgoal(prolog:when(_,_,user:when_eq0(Tag1,SVs1,Tag2,SVs2,WGoal)),DupsIn,DupsOut,
%         VisIn,VisOut,HDIn,HDOut) :-
%  !,nl, write('when_eq('),pp_fs(Tag1,SVs1,DupsIn,DupsMid,VisIn,VisMid,8,HDIn,HDMid),
%  write(','), nl, write('        '),
%  pp_fs(Tag2,SVs2,DupsMid,DupsMid2,VisMid,VisMid2,8,HDMid,HDMid2),
%  write(','), nl, write('        '),
%  pp_res_wgoal(WGoal,DupsMid2,DupsOut,VisMid2,VisOut,8,HDMid2,HDOut),
%%    DupsOut = DupsMid2, VisOut = VisMid2, HDOut = HDMid2,
%%    write(WGoal),
%  write(')').
%pp_resgoal(prolog:when(_,_,user:when_eq_a2(X1,X2,Tag1,Tag2,WGoal)),DupsIn,DupsOut,
%         VisIn,VisOut,HDIn,HDOut) :-
%  !,nl, write('when_eq('),pp_fs(Tag1,(a_ X1),DupsIn,DupsMid,VisIn,VisMid,8,HDIn,HDMid),
%  write(','), nl, write('        '),
%  pp_fs(Tag2,(a_ X2),DupsMid,DupsMid2,VisMid,VisMid2,8,HDMid,HDMid2),
%  write(','), nl, write('        '),
%  pp_res_wgoal(WGoal,DupsMid2,DupsOut,VisMid2,VisOut,8,HDMid2,HDOut),
%%    DupsOut = DupsMid2, VisOut = VisMid2, HDOut = HDMid2,
%%    write(WGoal),
%  write(')').
%pp_resgoal(prolog:when(_,_,user:when_type0(Type,FS,WGoal)),DupsIn,DupsOut,
%         VisIn,VisOut,HDIn,HDOut) :-
%  !,nl,write('when_type('),write(Type),write(','),
%  name(Type,TName), length(TName,TLen),
%  Col is 10+TLen,
%  (var(FS) -> write(FS)
%  ; pp_fs(FS,DupsIn,DupsMid,VisIn,VisMid,Col,HDIn,HDMid)
%  ),
%  write(','),
%  nl, write('          '),
%  pp_res_wgoal(WGoal,DupsMid,DupsOut,VisMid,VisOut,10,HDMid,HDOut),
%%    DupsOut = DupsMid, VisOut = VisMid, HDOut = HDMid,
%%    write(WGoal),
%  write(')').
pp_resgoal(prolog:when(_,_,user:when_type_delayed0(Type,FS,_,WGoal)),Dups,Inf,
           VisIn,VisOut,HDIn,HDOut) :-
  !,nl,write('when_type('),write(Type),write(','),
  name(Type,TName), length(TName,TLen),
  Col is 10+TLen,
  pp_fs(FS,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid), write(','),
  nl, write('          '),
  pp_res_wgoal(WGoal,Dups,Inf,VisMid,VisOut,10,HDMid,HDOut),
%    DupsOut = DupsMid, VisOut = VisMid, HDOut = HDMid,
%    write(WGoal),
  write(')').
pp_resgoal(Goal,_Dups,_Inf,Vis,Vis,HD,HD) :-
  nl,write(Goal).

% query_cond/9 prefixes
pp_res_wgoal((avl_map(nv_fresh,_,_),(_=_),query_goal0(_,_,_,NBody,_,_)),Dups,Inf,
	     VisIn,VisOut,Col,HDIn,HDOut) :-
  !,pp_goal(NBody,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut).
pp_res_wgoal((avl_map(nv_fresh,_,_),query_goal0(_,_,_,NBody,_,_)),Dups,Inf,
	     VisIn,VisOut,Col,HDIn,HDOut) :-
  !,pp_goal(NBody,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut).

pp_res_wgoal((G1 -> G2 ; G3),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !,pp_res_wgoal(G1,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
  nl, tab(Col), write(' -> '), NewCol is Col + 4,
  pp_res_wgoal(G2,Dups,Inf,VisMid,VisMid2,NewCol,HDMid,HDMid2),
  nl, tab(Col), write(' ; '), NewCol2 is Col + 3,
  pp_res_wgoal(G3,Dups,Inf,VisMid2,VisOut,NewCol2,HDMid2,HDOut).
pp_res_wgoal((G1,G2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !,pp_res_wgoal(G1,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
  write(','), nl, tab(Col),
  pp_res_wgoal(G2,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).
pp_res_wgoal(\+ G,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !,write('\\+ ( '), NewCol is Col + 5,
  pp_res_wgoal(G,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut),
  nl, tab(Col), tab(3), write(')').
pp_res_wgoal((Arg1=Arg2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, ( integer(Arg2) -> VisOut = VisIn, HDOut = HDIn,
	                write((Arg1=Arg2))
     ; NewCol is Col + 4,
       pp_fs(Arg1,Dups,Inf,VisIn,VisMid,Col,HDIn,HDMid),
       nl, tab(Col), write('  = '), 
       pp_fs(Arg2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut)
     ).
pp_res_wgoal(arg(N,FS1,FS2),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('arg('), NewCol is Col + 4,
  write(N),write(','),nl,tab(NewCol),
  pp_fs(FS1,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  write(','),nl,tab(NewCol),
  pp_fs(FS2,Dups,Inf,VisMid,VisOut,NewCol,HDMid,HDOut),write(')').
pp_res_wgoal(deref(FS,TFS,Type,AttPos),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !, write('deref('), NewCol is Col + 6,
  pp_fs(FS,Dups,Inf,VisIn,VisOut,NewCol,HDIn,HDOut),
  write(','),nl,tab(NewCol),write(TFS),
  write(','),nl,tab(NewCol),write(Type),
  write(','),nl,tab(NewCol),write(AttPos),
  write(')').

pp_res_wgoal(when_type(Type,FS,WGoal),Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  !,write('when_type('),write(Type),write(','),
  name(Type,TName), length(TName,TLen),
  NewCol is Col+10+TLen,
  pp_fs(FS,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid),
  write(','), nl, tab(Col), write('          '),
  NewCol2 is Col+10,
  pp_res_wgoal(WGoal,Dups,Inf,VisMid,VisOut,NewCol2,HDMid,HDOut), write(')').

pp_res_wgoal(CompGoal,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  nonvar(CompGoal), CompGoal =.. [CompRel|Args],
  name(CompRel,CompRelName),
  append("fs_",RelName,CompRelName),
  !,name(Rel,RelName), Goal =.. [Rel|Args],
  pp_goal(Goal,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut).

% everything else
pp_res_wgoal(WGoal,_Dups,_Inf,Vis,Vis,_,HD,HD) :-
  write(WGoal).

% ------------------------------------------------------------------------------
% pp_fs(FS:<fs>,VisIn:<var>s, VisOut:<var>s, Col:<int>)
% ------------------------------------------------------------------------------
% prints FS where VisOut is the result of adding all of the
% referents of substructures in FS to VisIn
% Col is where printing begins for FS
% ------------------------------------------------------------------------------
pp_fs(FS,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  pp_fs(FS,0,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut).

pp_fs(FS,MGType,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  deref(FS,_,Type,_),
  approps(Type,FRs,_),
  build_keyed_feats(FRs,FS,KeyedFeats),
  ( (current_predicate(portray_fs,portray_fs(_,_,_,_,_,_,_,_,_,_,_)),
     portray_fs(Type,FS,MGType,KeyedFeats,VisIn,VisOut,Dups,Inf,Col,HDIn,HDOut))
  -> true
   ; pp_fs_default(Type,FS,MGType,KeyedFeats,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut)
  ).

build_keyed_feats([],_,[]).
build_keyed_feats([F:Restr|FRs],FS,[fval(F,V,Restr)|KFs]) :-
  clause(fcolour(F,K,_),true),
  arg(K,FS,V),
  build_keyed_feats(FRs,FS,KFs).

pp_fs_default(Type,FS,MGType,KeyedFeats,Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  ( avl_fetch(FS,Dups,TagNum)            % print ref if shared (nonvar)
  -> write('['), write(TagNum), write('] ')
   ; true
  ),
  ( avl_fetch(FS,VisIn,_) -> VisOut = VisIn, HDOut = HDIn
  ; Type == 0 -> avl_store(FS,VisIn,_,VisOut), HDOut = HDIn,
                 ( no_write_type_flag(MGType) -> true
		 ; MGType == 0 -> write(mgsat)
		 ; approps(MGType,_,0) -> write(MGType) % MGType had no features anyway
		 ; write('mgsat('), write(MGType), write(')')
		 )
  ; avl_store(FS,VisIn,_,VisMid),     % print FS if not already visited
    ( no_write_type_flag(Type)
    -> pp_vs_unwritten(KeyedFeats,Dups,Inf,VisMid,VisOut,Col,HDIn,HDOut)
     ; write(Type),
       pp_vs(KeyedFeats,Dups,Inf,VisMid,VisOut,Col,HDIn,HDOut)
     )
  ).

% recursive callback for portray_fs
print_fs(_VarType,FS,MGType,VisIn,VisOut,Tags,Inf,Col,HDIn,HDOut) :-
  pp_fs(FS,MGType,Tags,Inf,VisIn,VisOut,Col,HDIn,HDOut).


:- dynamic no_write_type_flag/1.
:- dynamic no_write_feat_flag/1.

write_types:-
  write_type(_).

write_feats:-
  write_feat(_).

write_type(Type):-
  retractall(no_write_type_flag(Type)).

write_feat(Feat):-
  retractall(no_write_feat_flag(Feat)).

no_write_type(Type):-
  retractall(no_write_type_flag(Type)),
  assert(no_write_type_flag(Type)).

no_write_feat(Feat):-
  retractall(no_write_feat_flag(Feat)),
  assert(no_write_feat_flag(Feat)).

% ------------------------------------------------------------------------------
% pp_vs(FRs:<fs>, Vs:<vs>, Dups:<var>s, 
%        VisIn:<var>s, VisOut:<var>s, Col:<int>)
% ------------------------------------------------------------------------------
% prints Vs at Col 
% ------------------------------------------------------------------------------
pp_vs([],_,_,Vis,Vis,_,HD,HD).
pp_vs([fval(F,V,R)|KFs],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut) :-
  ( no_write_feat_flag(F) -> VisMid = VisIn, HDMid = HDIn
  ; (ale_flag(sparseoutput,on),
     avl_fetch(V,Inf,Inform),
     var(Inform)) -> VisMid = VisIn, HDMid = HDIn
  ; nl, tab(Col),
    write_feature(F,LengthF), 
    NewCol is Col + LengthF +1,
    pp_fs(V,R,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid)
  ),
  pp_vs(KFs,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).

pp_vs_unwritten([],_,_,Vis,Vis,_,HD,HD).
pp_vs_unwritten([fval(F,V,R)|KFs],Dups,Inf,VisIn,VisOut,Col,HDIn,HDOut):-
  ( no_write_feat_flag(F) -> VisMid = VisIn, HDMid = HDIn
  ; (ale_flag(sparseoutput,on),
     avl_fetch(V,Inf,Inform),
     var(Inform)) -> VisMid = VisIn, HDMid = HDIn
  ; write_feature(F,LengthF), 
    NewCol is Col + LengthF +1,
    pp_fs(V,R,Dups,Inf,VisIn,VisMid,NewCol,HDIn,HDMid)
  ),
  pp_vs(KFs,Dups,Inf,VisMid,VisOut,Col,HDMid,HDOut).

write_feature(F,LengthF):-
  name(F,NameF),
  count_and_capitalize(NameF,0,LengthF),
  write(' ').

write_desc_feature(F,LengthF) :-
  name(F,NameF), length(NameF,LengthF),
  write(F),
  write(':').
		   
count_and_capitalize([],Length,Length).
count_and_capitalize([L|Ls],LengthIn,Length):-
  capitalize(L,LCap),
  write(LCap),
  LengthInPlus1 is LengthIn + 1,
  count_and_capitalize(Ls,LengthInPlus1,Length).

capitalize(X,XCap):-
  ("a" =< X, X =< "z")
  -> NameXCap is X + "A" - "a",
     char_code(XCap,NameXCap)
  ; char_code(XCap,X).


% ==============================================================================
% Utilities
% ==============================================================================

% ------------------------------------------------------------------------------
% cat_atoms/3
% ------------------------------------------------------------------------------
cat_atoms(A1,A2,A3):-
  name(A1,L1),
  name(A2,L2),
  append(L1,L2,L3),
  name(A3,L3).

% ------------------------------------------------------------------------------
% esetof(X:Alpha, Goal:<goal>, Xs:<list(Alpha)>)
% ------------------------------------------------------------------------------
% setof returning empty list if no solutions
% ------------------------------------------------------------------------------
:- meta_predicate esetof/3.
esetof(X,Goal,Xs) :-
  if(setof(X,Goal,Xs),
     true,
     (Xs = [])).

% ------------------------------------------------------------------------------
% ebagof(X:Alpha, Goal:<goal>, Xs:<list(Alpha)>)
% ------------------------------------------------------------------------------
% bagof returning empty list if no solutions
% ------------------------------------------------------------------------------
:- meta_predicate ebagof/3.
ebagof(X,Goal,Xs) :-
  if(bagof(X,Goal,Xs),
     true,
     (Xs = [])).

% ------------------------------------------------------------------------------
% member_eq(X:<term>, Xs:<term>s)
% ------------------------------------------------------------------------------
% X is strictly == equal to a member of list Xs
% ------------------------------------------------------------------------------
member_eq(X,[Y|Ys]):-
    X==Y
  ; member_eq(X,Ys).

% ------------------------------------------------------------------------------
% member_rest(Elt,List,Rest)
% ------------------------------------------------------------------------------
% like member/2 but also returns remainder of list after Elt
% ------------------------------------------------------------------------------
member_rest(Element, [Head|Tail], Rest) :-
        member_rest_act(Tail, Head, Element, Rest).
        % auxiliary to avoid choicepoint for last element
member_rest_act(Rest, Element, Element, Rest).
member_rest_act([Head|Tail], _, Element, Rest) :-
        member_rest_act(Tail, Head, Element, Rest).

% ------------------------------------------------------------------------------
% select_eq(X:<term>, Xs:<term>s, XsLeft:<term>s)
% ------------------------------------------------------------------------------
% X is strictly == equal to a member of list Xs with XsLeft left over
% ------------------------------------------------------------------------------
select_eq(X,[Y|Ys],Zs):-
    X==Y,
    Zs = Ys
  ; Zs = [Y|Zs2],
    select_eq(X,Ys,Zs2).

% ------------------------------------------------------------------------------
% transitive_closure(Graph:<graph>, Closure:<graph>)
% ------------------------------------------------------------------------------
% Warshall's Algorithm (O'Keefe, Craft of Prolog, p. 172)
% Input: Graph = [V1-Vs1,...,VN-VsN]
%   describes the graph G = <Vertices, Edges> where
%      * Vertices = {V1,..,VN} and
%      * VsI = {VJ | VI -> VJ in Edges}
% Output: Closure is transitive closure of Graph in same form
% SICStus Prolog's transitive_closure/2 will not add loops in case of
%  subsumption cycles, so we cannot use it.
% ------------------------------------------------------------------------------
%transitive_closure(Graph,Closure):-
%  warshall(Graph,Graph,Closure).

%warshall([],Closure,Closure).
%warshall([V-_|G],E,Closure):-
%  memberchk(V-Y,E),
%  warshall(E,V,Y,NewE),
%  warshall(G,NewE,Closure).

%warshall([],_,_,[]).
%warshall([X-Neibs|G],V,Y,[X-NewNeibs|NewG]):-
%  memberchk(V,Neibs),
%  !, ord_union(Neibs,Y,NewNeibs),
%  warshall(G,V,Y,NewG).
%warshall([X-Neibs|G],V,Y,[X-Neibs|NewG]):-
%  warshall(G,V,Y,NewG).

% ------------------------------------------------------------------------------
% reverse_count_lex_check(ListIn:<list>,Acc:<list>,ListOut:<list>,
%                         CountIn:<int>,CountOut:<int>)
% ------------------------------------------------------------------------------
% using accumulators, reverses ListIn into ListOut, with initial segment
% Acc;  CountIn is current count (of Acc) and CountOut is result;  call
% by: reverse_count_lex_check(ListIn,[],ListOut,0,Count).  Also verify that each
% word/member of the list has an entry in the lexicon.
% ------------------------------------------------------------------------------
reverse_count_lex_check([],Xs,Xs,Count,Count,Unknowns) :-
  Unknowns == [] -> true
  ; raise_exception(ale(unk_words(Unknowns))).
reverse_count_lex_check([X|Xs],Ys,Zs,CountIn,Count,UnknownsIn):-
  CountInPlus1 is CountIn+1,
  ( \+ lex(X,_) -> UnknownsOut = [X|UnknownsIn] ; UnknownsOut = UnknownsIn ),
  reverse_count_lex_check(Xs,[X|Ys],Zs,CountInPlus1,Count,UnknownsOut).

% ------------------------------------------------------------------------------
% query_proceed
% ------------------------------------------------------------------------------
% prompts user for n. response, otherwise proceeds
% ------------------------------------------------------------------------------
query_proceed :- ale_flag(another,autoconfirm), !, fail.
query_proceed:-
  nl(user_error), write(user_error,'ANOTHER?  '), flush_output(user_error),
  get_char(C), query_proceed_act(C).

query_proceed_act(n) :- !,skip_line.
query_proceed_act('\n') :- !.
query_proceed_act(_) :- skip_line,fail.

% ------------------------------------------------------------------------------
% call_all(:Pred)
% ------------------------------------------------------------------------------
% Calls every clause of Pred in a failure-driven loop.
% ------------------------------------------------------------------------------
:- meta_predicate call_all(:).
call_all(Pred) :-
  call(Pred),
  fail.
call_all(_).

% ------------------------------------------------------------------------------
% number_display/2
% ------------------------------------------------------------------------------
number_display([],M):-
  !,write(M).  % need cut for variable 1st arguments
number_display([W|Ws],N):-
  write(N), write(' '), write(W), write(' '),
  SN is N + 1,
  number_display(Ws,SN).

% ------------------------------------------------------------------------------
% error_msg(Goal:<goal>)
% ------------------------------------------------------------------------------
% tells user, solves Goal, then goes back to old file being told
% ------------------------------------------------------------------------------
error_msg(Goal):-
  write(user_error,'{ALE: ERROR: '),
  telling(S),
  ( tell(user_error),
    call(Goal)
  ; tell(S)
  ),
  fail.  

% ------------------------------------------------------------------------------
% tell_user_error(Goal:<goal>)
% ------------------------------------------------------------------------------
% execute Goal telling user_error stream.
% ------------------------------------------------------------------------------
tell_user_error(Goal) :-
  telling(UserOutputStream),
  tell(user_error),
  if(call(Goal),
     tell(UserOutputStream),
     (tell(UserOutputStream),fail)
    ).

% ------------------------------------------------------------------------------
% if_error(Msg,Cond)
% ------------------------------------------------------------------------------
% if condition Cond holds, provides Msg as error message;  always succeeds
% ------------------------------------------------------------------------------
if_error(Msg,Cond):-
  ( call(Cond) -> raise_exception(Msg)
  ; true
  ).

% ------------------------------------------------------------------------------
% if_warning_else_fail(Msg,Cond)
% ------------------------------------------------------------------------------
% if Cond holds, provides warning message Msg, otherwise fails
% ------------------------------------------------------------------------------
if_warning_else_fail(Msg,Cond):-
  if_warning(Msg,Cond),
  Cond.

new_if_warning_else_fail(Msg,Cond):-
  if(call(Cond),
     (print_message(warning,Msg),
      fail),
     (!,fail))
  ; true.

% ------------------------------------------------------------------------------
% if_warning(Msg,Cond)
% ------------------------------------------------------------------------------
% if condition Cond holds, prints out Msg;  always succeeds
% ------------------------------------------------------------------------------
if_warning(Msg,Cond):-
  telling(FileName),
  tell(user),
  ( Cond, 
    write_list(['  *Warning: '|Msg]),
    nl,nl,
    fail
  ; told,
    tell(FileName)
  ).

new_if_warning(Msg,Cond):-
  if(call(Cond),
     (print_message(warning,Msg),
      fail),
     !)
  ; true.

(W warning) :- print_message(warning,W).

% ------------------------------------------------------------------------------
% write_list(Xs)
% ------------------------------------------------------------------------------
% writes out elements of Xs with spaces between elements
% ------------------------------------------------------------------------------
write_list([]).
write_list([X|Xs]):-
  write(X), write(' '), write_list(Xs).

write_list([],_).
write_list([X|Xs],Stream) :-
  write(Stream,X), write(Stream,' '),
  write_list(Xs,Stream).
% ------------------------------------------------------------------------------
% query_user(Query)
% ------------------------------------------------------------------------------
% writes Query and then tries to read a y. from user
% ------------------------------------------------------------------------------
query_user(QueryList):-
  nl, nl, write_list(QueryList),
  read(y).

% ------------------------------------------------------------------------------
% duplicated(X,Xs)
% ------------------------------------------------------------------------------
% holds if X occurs more than once in Xsd
% ------------------------------------------------------------------------------
duplicated(X,[X|Xs]):-
  member(X,Xs).
duplicated(X,[_|Xs]):-
  duplicated(X,Xs).

% ------------------------------------------------------------------------------
% feat_cycle(S:<type>, Fs:<path>)
% ------------------------------------------------------------------------------
% holds if following the path Fs in the appropriateness definitions
% leads from S to S.  calls an auxiliary function which avoids infinite
% loops and tracks the features so far followed in reverse with an accumulator
% ------------------------------------------------------------------------------
feat_cycle(S,Fs):-
  feat_cycle2(S,S,[S],[],Fs).

% ------------------------------------------------------------------------------
% feat_cycle2(S1:<type), S2:<type), Ss:<list(<type>)>, 
%             FsIn:<path>, FsOut:<path>)
% ------------------------------------------------------------------------------
% assumes following reverse of FsIn led to S2 from S1, visiting
% Ss along the way.  FsOut is the result of appending a path that will
% get from S2 back to S1 to the reverse of FsIn
% ------------------------------------------------------------------------------
feat_cycle2(S1,S2,_Ss,FsIn,FsOut):-
  approp(F,S2,S1),
  reverse([F|FsIn],FsOut).
feat_cycle2(S1,S2,Ss,FsIn,FsOut):-
  approp(F,S2,S3),
  \+ member(S3,Ss),
  feat_cycle2(S1,S3,[S2|Ss],[F|FsIn],FsOut).


% ==============================================================================
% Generator
% ==============================================================================
% KNOWN BUG: at present, forall rules are *not* applied in generator.

% ------------------------------------------------------------------------------
% split_dtrs(+Dtrs:<dtr>s, -Head:<desc>,
%            -SemGoalBefore:<goal>, -SemGoalAfter:<goal>,
%            -DtrsBefore:<dtr>s, -DtrsAfter:<dtr>s)
% ------------------------------------------------------------------------------
% splits the RHS of a chain rule into Head, SemGoalBefore the Head, SemGoalAfter
% the Head, DtrsBefore the Head, and DtrsAfter the Head
% ------------------------------------------------------------------------------
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head,sem_goal> SemGoalAfter,
            DtrsAfter),
           Head,SemGoalBefore,SemGoalAfter,empty,DtrsAfter) :- 
  !.
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head,sem_goal> SemGoalAfter),
           Head,SemGoalBefore,SemGoalAfter,
           empty,empty) :- 
  !.
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head,DtrsAfter),
           Head,SemGoalBefore,empty,empty,DtrsAfter) :- 
  !.
split_dtrs((sem_goal> SemGoalBefore,sem_head> Head),
           Head,SemGoalBefore,empty,empty,empty) :- 
  !.
split_dtrs((sem_head> Head,sem_goal> SemGoalAfter,DtrsAfter),
           Head,empty,SemGoalAfter,empty,DtrsAfter) :- 
  !.
split_dtrs((sem_head> Head,sem_goal> SemGoalAfter),
           Head,empty,SemGoalAfter,empty,empty) :- 
  !.
split_dtrs((sem_head> Head,DtrsAfter),Head,empty,empty,empty,DtrsAfter) :- 
  !.
split_dtrs((sem_head> Head),Head,empty,empty,empty,empty) :- 
  !.
split_dtrs((Dtr,RestDtrs),Head,SemGoalBefore,SemGoalAfter,
           (Dtr,DtrsBefore),DtrsAfter) :- 
  !,split_dtrs(RestDtrs,Head,SemGoalBefore,SemGoalAfter,DtrsBefore,DtrsAfter).

% ------------------------------------------------------------------------------
% Run-time generation support
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% gen(+Cat:<desc>)
% gen(+Tag:<tag>, +SVs:<svs>, +Iqs:<ineq>)
% ------------------------------------------------------------------------------
% top-level user calls to generate a sentence from a descriptor Cat
% or a FS specified by Tag, SVs, Iqs
% ------------------------------------------------------------------------------
% __ port this to portray_cat/5 and figure out how to pass derivation tree.
gen(Cat) :-
  call_residue((add_to(Cat,FS),
		frozen_term(FS,Frozen),
                ((current_predicate(portray_fs_in_window,portray_fs_in_window(_,_,_,_)),
		  portray_fs_in_window(['INITIAL','CATEGORY'],FS,bot,Frozen)) -> true
		; nl, write('INITIAL CATEGORY: '), nl, flush_output,
                  pp_fs_res(FS,Frozen), nl
		),
                gen(FS,Words)),FS,Residue),
  ((current_predicate(portray_fs_in_window,portray_fs_in_window(_,_,_,_)),
    portray_fs_in_window(Words,FS,bot,Residue)) -> true
  ; nl, write('STRING: '),
    nl, write_list(Words), nl,
    \+ \+ (nl, write('FINAL CATEGORY: '),nl, flush_output,
	   pp_fs_res(FS,Residue)), nl
  ),
  query_proceed.

% ------------------------------------------------------------------------------
% gen(+Tag:<tag>, +SVs:<svs>, +IqsIn:<ineq>s, -Words:<word>s)
% ------------------------------------------------------------------------------
% top-level functional interface for the generator
% generates the list of Words from the semantic specification of Tag-SVs,Iqs
% ------------------------------------------------------------------------------
gen(FS,Words) :-
  generate(FS,Words,[]).

% ------------------------------------------------------------------------------
% generate(+Tag:<tag>, +SVs:<svs>, +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%          +Words:<word>s, +RestWords:<word>s)
% ------------------------------------------------------------------------------
% recursively generates the difference list Words-RestWords from the root
% Tag-SVs,IqsIn
% ------------------------------------------------------------------------------
generate(FS,Words,RestWords) if_h
    [GoalIndex,GoalPivot,
     non_chain_rule(PivotFS,FS,Words,RestWords)] :-
  semantics(Pred),
  cat_atoms('fs_',Pred,CompiledPred),
  functor(GoalIndex,CompiledPred,2),  % KNOWN BUG: need to check relation mode of Pred/2
  arg(1,GoalIndex,FS),
  arg(2,GoalIndex,IndexFS),
  functor(GoalPivot,CompiledPred,2),
  arg(1,GoalPivot,PivotFS),
  arg(2,GoalPivot,IndexFS).

% ------------------------------------------------------------------------------
% generate_list(+Sort:<sort>, +Vs:<vs>, +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%               -Words:<word>s, +RestWords:<word>s)
% ------------------------------------------------------------------------------
% generates a list of words Words-RestWords from a variable list of descriptions
% Sort(Vs)
% ------------------------------------------------------------------------------
generate_list(Type,ListFS,Words,RestWords) :-
  ( sub_type(e_list,Type) -> Words = RestWords
  ; sub_type(ne_list,Type) -> clause(fcolour(hd,HdPos),true),
                              arg(HdPos,ListFS,HdFS),
                              generate(HdFS,Words,MidWords),
                              clause(fcolour(tl,TlPos),true),
                              arg(TlPos,ListFS,TlFS),
                              get_type(TlFS,TlType),
                              generate_list(TlType,TlFS,MidWords,RestWords)
  ; error_msg((nl,write('error: cats> value with sort, '),write(Type),
               write(' is not a valid argument (e_list or ne_list)')))
  ).

% ------------------------------------------------------------------------------
% Compiler
% ------------------------------------------------------------------------------

:- dynamic current_chain_length/1.
current_chain_length(4).

% ------------------------------------------------------------------------------
% chain_length(N:<int>)
% ------------------------------------------------------------------------------
% asserts chain_length/1 to N -- controls depth of chain rules application
% ------------------------------------------------------------------------------
chain_length(N):-
  retractall(current_chain_length(_)),
  assert(current_chain_length(N)).

% ------------------------------------------------------------------------------
% non_chain_rule(+PivotTag:<tag>,
%                +PivotSVs:<svs>, +RootTag:<tag>, +RootSVs:<svs>,
%                +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%                -Words:<word>s, -RestWords:<word>s)
% ------------------------------------------------------------------------------
% compiles nonheaded grammar rules, lexical entries and empty categories into
% non_chain_rule predicates which unifies the mother against the
% PivotTag-PivotSVs FS, generates top-down the RHS, and connects the mother FS
% to the next chain rule
% the result Words-RestWords is the final list of words which includes the list
% NewWords-RestNewWords corresponding to the expansion of the current rule
% ------------------------------------------------------------------------------
non_chain_rule(_,_,_,_) if_b [fail] :-
  (current_predicate(empty,empty(_)) -> \+ empty(_) ; true),
  (current_predicate('--->',(_ ---> _)) -> \+ (_ ---> _) ; true),
  (current_predicate(rule,(_ rule _)) -> \+ (_ rule _) ; true).
non_chain_rule(PivotFS,RootFS,Words,RestWords) if_b SubGoals :-
  current_predicate(empty,empty(_)),
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(NVs),
  empty_avl(EMode),
  empty_avl(EMFS),
  initialise_mode([],EMode,ModeIn,EMFS,MFSIn),
  empty(Desc),
  compile_desc(Desc,PivotFS,SubGoals,
               [current_chain_length(Max),
                \+ \+ chained(0,Max,PivotFS,RootFS),
                chain_rule(0,Max,PivotFS,RootFS,Words,Words,Words,RestWords)],
	       [],serial,VarsIn,_,_FSPal,FSsIn,FSsOut,ModeIn,_,MFSIn,_,NVs),
  assert_empty_avl(FSsOut).
%  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsMid,non_chain_rule).
non_chain_rule(PivotFS,RootFS,Words,RestWords) if_b SubGoals :-
  secret_noadderrs_toggle(_), % turn off adderrs for lexical compilation
  current_predicate('--->', (_ ---> _)),
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(NVs),
  empty_avl(EMode),
  empty_avl(EMFS),
  initialise_mode([],EMode,ModeIn,EMFS,MFSIn),
  (WordStart ---> DescOrGoalStart),
  lex_desc_goal(DescOrGoalStart,DescStart,true,GoalStart),
  curr_lex_rule_depth(LRMax),
  gen_lex_close(0,LRMax,WordStart,DescStart,GoalStart,WordOut,DescOut,PriorVs,GoalOut),
%  SubGoalsMid = [lex_goal(_-(a_ WordOut),PivotTag-PivotSVs)|SubGoalsMid2],
  compile_desc(DescOut,PivotFS,SubGoalsFinal,
	       [current_chain_length(Max),
		\+ \+ chained(0,Max,PivotFS,RootFS),
		chain_rule(0,Max,PivotFS,RootFS,[WordOut|NewWords],NewWords,Words,RestWords)
	       |SubGoalsMid],[],serial,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSIn,MFSMid,NVs),
  compile_body(GoalOut,SubGoalsMid,[],serial,VarsMid,_,FSPal,FSsMid,FSsOut,MFSMid,_,NVs,PriorVs,[]),
%  assert_empty_avl(FSsOut),
  build_fs_palette(FSsOut,FSPal,SubGoals,SubGoalsFinal,non_chain_rule).
%  write(user_error,WordOut),nl(user_error),flush_output(user_error). %DEBUG
non_chain_rule(PivotFS,RootFS,Words,RestWords) if_b PGoals :-
  current_predicate(rule, (_ rule _)),
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(NVs),
  empty_avl(EMode),
  empty_avl(EMFS),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,EMFS,MFSIn),
  (_RuleName rule Mother ===> Dtrs),
  \+ split_dtrs(Dtrs,_,_,_,_,_),  % i.e., not a chain rule
  compile_desc(Mother,PivotFS,PGoals,
               [current_chain_length(Max),
                \+ \+ chained(0,Max,PivotFS,RootFS)
               |PGoalsDtrs],M,serial,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSIn,MFSsMid,NVs),
  term_variables(Mother,PriorVs),
  compile_gen_dtrs(Dtrs,HeadWords,RestHeadWords,PGoalsDtrs,
                   [chain_rule(0,Max,PivotFS,RootFS,HeadWords,RestHeadWords,Words,RestWords)],
		   serial,VarsMid,_,FSPal,FSsMid,FSsOut,MFSsMid,_,PriorVs),
  assert_empty_avl(FSsOut).
%  build_fs_palette(FSsOut,FSPal,PGoals,PGoalsMid,non_chain_rule).
%  write(user_error,RuleName),nl(user_error),flush_output(user_error). %DEBUG
  
% ------------------------------------------------------------------------------
% chain_rule(+PivotTag:<tag>, +PivotSVs:<svs>, +RootTag:<tag>, +RootSVs:<svs>,
%            +IqsIn:<ineq>s, -IqsOut:<ineq>s, +HeadWords:<word>s,
%            +RestHeadWords:<word>s, -Words:<word>s, RestWords:<word>s)
% ------------------------------------------------------------------------------
% compiles headed grammar rules into chain_rule predicates which unify the head
% agains the PivotTag-PivotSVS FS, generates top-down the rest of the RHS,
% and connects the mother FS to the next chain rule
% the result is the list Words-RestWords which includes the sublist
% HeadWords-RestHeadWords corresponding to the head
% ------------------------------------------------------------------------------
chain_rule(_,_,FS,FS,Words,RestWords,Words,RestWords) if_b []. % unify PivotFS and RootFS
                                                     % keep this clause first after multi-hashing 
chain_rule(N,Max,PivotFS,RootFS,HeadWords,RestHeadWords,Words,RestWords) if_b [N < Max|PGoalsSG] :-
  current_predicate(rule,(_ rule _)),
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(NVs),
  empty_avl(EMFS),
  empty_avl(EMode),
  genindex(M),  genindex(M2),
  (_RuleName rule Mother ===> Dtrs),
  split_dtrs(Dtrs,Head,SGBefore,SGAfter,DtrsBefore,DtrsAfter),
  prior_cont_vars(SGBefore,SGBeforeVars),
  term_variables(Head,HeadVars),
  prior_cont_vars(SGAfter,SGAfterVars),
  term_variables(Mother,MotherVars),
  prior_cont_vars(DtrsBefore,DtrsBeforeVars),
  prior_cont_vars(DtrsAfter,DtrsAfterVars),
  ord_union(HeadVars,SGBeforeVars,SGAfterPriorVs),
  ord_union(MotherVars,SGAfterVars,MotherSGAfterVars),
  ord_union(MotherSGAfterVars,SGAfterPriorVs,DtrsBeforePriorVs),
  ord_union(MotherVars,DtrsBeforeVars,MotherDtrsBeforeVars),
  ord_union(MotherDtrsBeforeVars,DtrsAfterVars,SGAfterContVs),
  ord_union(DtrsBeforeVars,DtrsBeforePriorVs,DtrsAfterPriorVs),
  ord_union(HeadVars,SGAfterVars,HeadSGAfterVars),
  ord_union(HeadSGAfterVars,SGAfterContVs,SGBeforeContVs),
  (SGBefore == empty
  -> PGoalsHead = PGoalsSG, VarsMid = VarsIn,
     FSsMid = FSsIn, MFSsMid = EMFS
   ; compile_body(SGBefore,PGoalsSG,PGoalsHead,serial,
                  VarsIn,VarsMid,FSPal,FSsIn,FSsMid,EMFS,MFSsMid,NVs,[],SGBeforeContVs)),
  initialise_mode(M,EMode,ModeIn,MFSsMid,MFSsMid2),
  compile_desc(Head,PivotFS,PGoalsHead,PGoalsMother,M,serial,VarsMid,
               VarsMid2,FSPal,FSsMid,FSsMid2,ModeIn,_,MFSsMid2,MFSsMid3,NVs),
  (SGAfter == empty
  -> PGoalsSGAfter = PGoalsMother, VarsMid3=VarsMid2,
     FSsMid3 = FSsMid2, MFSsMid4 = MFSsMid3
   ; compile_body(SGAfter,PGoalsMother,PGoalsSGAfter,
                  serial,VarsMid2,VarsMid3,FSPal,FSsMid2,FSsMid3,MFSsMid3,MFSsMid4,NVs,
                  SGAfterPriorVs,SGAfterContVs)),
  initialise_mode(M2,EMode,ModeIn2,MFSsMid4,MFSsMid5),
  empty_avl(EAssoc),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsSGAfter,
		   PGoalsIVar,M2,serial,VarsMid3,VarsMid4,FSPal,FSsMid3,FSsMid4,ModeIn2,_,
		   MFSsMid5,MFSsMid6,NVs),
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsIVar,[SN is N + 1,
						 \+ \+ chained(SN,Max,MotherFSVar,RootFS)
						|PGoalsLeft]),
  FS = fs(MotherFSVar),
  compile_gen_dtrs(DtrsBefore,NewWords,HeadWords,
                   PGoalsLeft,PGoalsRight,serial,VarsMid4,VarsMid5,FSPal,FSsMid4,
                   FSsMid5,MFSsMid6,MFSsMid7,DtrsBeforePriorVs), % ,DtrsAfterVars
  compile_gen_dtrs(DtrsAfter,RestHeadWords,RestNewWords,PGoalsRight,
                   [chain_rule(SN,Max,MotherFSVar,RootFS,
                               NewWords,RestNewWords,Words,
                               RestWords)],serial,VarsMid5,_,FSPal,FSsMid5,FSsOut,MFSsMid7,_,
                   DtrsAfterPriorVs), % ,[]
  assert_empty_avl(FSsOut).
%  build_fs_palette(FSsOut,FSPal,PGoalsSG,PGoalsSGBefore,chain_rule).

% ------------------------------------------------------------------------------
% compile_gen_dtrs(+Dtrs:<desc>, +IqsIn:<ineq>s, -IqsOut:<ineq>s,
%                  -Words:<word>s, -RestWords:<word>s,
%                  -Goals:<goal>s, -GoalsRest:<goal>s, +VarsIn:<avl>,
%                  -VarsOut:<avl>, +FSPal:<var>, +FSsIn:<fs>s, -FSsOut:<fs>s)
% ------------------------------------------------------------------------------
% compiles the top-down expansion of a sequence Dtrs of RHS items
% (daughters or goals)
% ------------------------------------------------------------------------------
compile_gen_dtrs(empty,Words,Words,PGoals,PGoals,_,Vars,Vars,_,FSs,
                 FSs,MFSs,MFSs,_) :- 
  !.
compile_gen_dtrs((cat> Dtr),Words,RestWords,PGoalsDtr,PGoalsRest,Context,VarsIn,
		 VarsOut,FSPal,FSsIn,FSsOut,MFSsIn,MFSsOut,_) :-
  !, empty_avl(NVs), empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSsIn,MFSsMid),
  empty_avl(EAssoc),
  compile_desc_act(Dtr,EAssoc,ImplicitVars,PGoalsDtr,PGoalsMid,
		   M,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,ModeIn,_,MFSsMid,MFSsOut,NVs),
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid,[generate(DtrFSVar,Words,RestWords)|PGoalsRest]),
  FS = fs(DtrFSVar).
compile_gen_dtrs((cat> Dtr,RestDtrs),Words,RestWords,
                 PGoalsDtr,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSsIn,MFSsOut,PriorVs) :-
  !, empty_avl(NVs), empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSsIn,MFSsMid),
  empty_avl(EAssoc),
  compile_desc_act(Dtr,EAssoc,ImplicitVars,PGoalsDtr,PGoalsMid,
                   M,Context,VarsIn,VarsMid,FSPal,
		   FSsIn,FSsMid,ModeIn,_,MFSsMid,MFSsMid2,NVs),
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid,[generate(DtrFSVar,Words,WordsMid)|PGoalsDtrs]),
  FS = fs(DtrFSVar),
  term_variables(Dtr,DtrVars),
  ord_union(DtrVars,PriorVs,RestPriorVs),
  compile_gen_dtrs(RestDtrs,WordsMid,RestWords,PGoalsDtrs,PGoalsRest,Context,VarsMid,VarsOut,
		   FSPal,FSsMid,FSsOut,MFSsMid2,MFSsOut,RestPriorVs).
compile_gen_dtrs((goal> Goal),Words,Words,
                 PGoalsBody,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSsIn,MFSsOut,PriorVs) :-
  !, empty_avl(NVs),
  compile_body(Goal,PGoalsBody,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,
	       MFSsIn,MFSsOut,NVs,PriorVs,[]).
compile_gen_dtrs((goal> Goal,RestDtrs),Words,RestWords,
                 PGoalsBody,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSsIn,MFSsOut,PriorVs) :- 
  !, empty_avl(NVs),
  prior_cont_vars(RestDtrs,ContVs),
  compile_body(Goal,PGoalsBody,PGoalsDtrs,Context,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,MFSsIn,MFSsMid,NVs,PriorVs,ContVs),
  prior_cont_vars(Goal,GoalVars),
  ord_union(GoalVars,PriorVs,RestPriorVs),
  compile_gen_dtrs(RestDtrs,Words,RestWords,
                   PGoalsDtrs,PGoalsRest,Context,VarsMid,VarsOut,FSPal,FSsMid,FSsOut,MFSsMid,MFSsOut,
                   RestPriorVs).
compile_gen_dtrs((cats> Dtrs),Words,RestWords,
                 PGoalsDtrs,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSsIn,MFSsOut,_) :- 
  !, empty_avl(NVs), empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSsIn,MFSsMid),
  empty_avl(EAssoc),
  compile_desc_act(Dtrs,EAssoc,ImplicitVars,PGoalsDtrs,PGoalsMid,
		   M,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,ModeIn,_,MFSsMid,MFSsOut,NVs),
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid,[get_type(ListFSVar,Type),
					      generate_list(Type,ListFSVar,Words,RestWords)
					     |PGoalsRest]),
  FS = fs(ListFSVar).
compile_gen_dtrs((cats> Dtrs,RestDtrs),Words,RestWords,
                 PGoalsDtrs,PGoalsRest,Context,VarsIn,VarsOut,FSPal,FSsIn,FSsOut,MFSsIn,MFSsOut,PriorVs) :- 
  !, empty_avl(NVs), empty_avl(EMode),
  genindex(M),
  initialise_mode(M,EMode,ModeIn,MFSsIn,MFSsMid),
  empty_avl(EAssoc),
  compile_desc_act(Dtrs,EAssoc,ImplicitVars,PGoalsDtrs,PGoalsMid,
		   M,Context,VarsIn,VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSsMid,MFSsMid2,NVs),
  ivar_fresh(M,M,ImplicitVars,FS,_,PGoalsMid,[get_type(ListFSVar,Type),
					      generate_list(Type,ListFSVar,Words,NewWords)
					     |PGoalsRestDtrs]),
  FS = fs(ListFSVar),
  term_variables(Dtrs,DtrsVars),
  ord_union(DtrsVars,PriorVs,RestPriorVs),
  compile_gen_dtrs(RestDtrs,NewWords,RestWords,
                   PGoalsRestDtrs,PGoalsRest,Context,VarsMid,VarsOut,FSPal,FSsMid,
                   FSsOut,MFSsMid2,MFSsOut,RestPriorVs).

% ------------------------------------------------------------------------------
% chained(+PivotTag:<tag>, +PivotSVs:<svs>, +RootTag:<tag>,
%         +RootSVs:<svs>, +IqsIn:<ineq>s, -IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% checks whether PivotTag-PivotSVs and RootTag-RootSVs can be connected through
% a chain of grammar rules
% ------------------------------------------------------------------------------
chained(_,_,FS,FS) if_b [].    % keep this clause first after multi-hashing
chained(N,Max,PivotFS,RootFS) if_b [N<Max|PGoals] :-
  current_predicate(rule,(_ rule _)),
  empty_avl(VarsIn),
  empty_avl(FSsIn),
  empty_avl(NVs),
  empty_avl(EMode),
  empty_avl(EMFS),
  genindex(M), genindex(M2),
  initialise_mode(M,EMode,ModeIn,EMFS,MFSsIn),
  (_Rule rule Mother ===> Body),
  split_dtrs(Body,HeadIn,_,_,_,_),
  compile_desc(HeadIn,PivotFS,PGoals,PGoalsPivot,M,serial,VarsIn,
               VarsMid,FSPal,FSsIn,FSsMid,ModeIn,_,MFSsIn,MFSsMid,NVs),
  initialise_mode(M2,EMode,ModeIn2,MFSsMid,MFSsMid2),
  empty_avl(EAssoc),
  compile_desc_act(Mother,EAssoc,ImplicitVars,PGoalsPivot,PGoalsFSVar,
		   M2,serial,VarsMid,_,FSPal,FSsMid,FSsOut,ModeIn2,_,MFSsMid2,_,NVs),
  ivar_fresh(M2,M2,ImplicitVars,FS,_,PGoalsFSVar,[SN is N + 1,
						  chained(SN,Max,NewPivFSVar,RootFS)]),
  FS = fs(NewPivFSVar),
  assert_empty_avl(FSsOut).
%  build_fs_palette(FSsOut,FSPal,PGoals,PGoalsMid,chained).

% ------------------------------------------------------------------------------
% gen_lex_close(+N:<int>, +Max:<int>, +WordIn:<word>, +MotherIn:<desc>,
%               -WordOut<word>, -MotherOut:<desc>, 
%               +IqsIn:<ineq>s, -IqsOut:<ineq>s)
% ------------------------------------------------------------------------------
% computes the closure of lexical entries under lexical rules to get additional
% lexical grammar rules MotherOut ===> DtrsOut
% ------------------------------------------------------------------------------
gen_lex_close(N,Max,WordStart,DescStart,GoalStart,WordEnd,DescEnd,PriorVsEnd,GoalEnd) :-
  gen_lex_close(N,Max,WordStart,DescStart,[],GoalStart,WordEnd,DescEnd,PriorVsEnd,GoalEnd).
gen_lex_close(_,_,Word,Desc,PriorVs,Goal,Word,Desc,PriorVs,Goal).
gen_lex_close(N,Max,WordStart,DescStart,_,GoalStart,WordEnd,DescEnd,PriorVsEnd,GoalEnd) :-
  current_predicate(lex_rule,(_ lex_rule _)),
  N < Max,
  add_to(DescStart,FSIn),
  ( (_RuleName lex_rule DescOrGoalIn **> DescOrGoalOut morphs Morphs),
    Cond = true
  ; (_RuleName lex_rule DescOrGoalIn **> DescOrGoalOut if Cond morphs Morphs)
  ),
  lex_desc_goal(DescOrGoalIn,DescIn,_,GoalStart),
  lex_desc_goal(DescOrGoalOut,DescOut,true,GoalOut),
  add_to(DescIn,FSIn),
  query_goal(Cond),
%  call(Goal), --- query_goal/1 now calls its Goal
  morph(Morphs,WordStart,WordOut,_,_), % no sense binding selected patterns until we apply forall rules
  SN is N + 1,
  prior_cont_vars(Cond,CondPriorVs),
  term_variables(term(DescIn,DescOut,Morphs),OtherPriorVs),  
  ord_union(CondPriorVs,OtherPriorVs,PriorVsOut),
  gen_lex_close(SN,Max,WordOut,DescOut,PriorVsOut,GoalOut,WordEnd,DescEnd,PriorVsEnd,GoalEnd).

% ------------------------------------------------------------------------------

% 5/15/96 - Octav -- changed to display the new version and add the banner to
% the version/0 message
% SP4: must render quoted newline with \n
:- nl,write('\nALE Version 4.0 alpha; September, 2006\nCopyright (C) 1992-1995, Bob Carpenter and Gerald Penn\nCopyright (C) 1998,1999,2001--2006 Gerald Penn\nAll rights reserved'),nl,
  initialise_ale_flags,
  clear_index,
  clear_edgenum.

%to_file(File) :-
%  bagof(e(I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName),
%        edge(I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName),
%        Es),
%  tell(File),
%  to_file_act(Es),
%  nl,told.

%to_file_act([]).
%to_file_act([e(I,Left,Right,Tag,SVs,Iqs,Dtrs,RuleName)|Es]) :-
%  write('edge('),write(I),comma,write(Left),comma,write(Right),comma,
%  write(Tag),comma,write(SVs),comma,write(Iqs),comma,write(Dtrs),comma,
%  write(RuleName),write(').'),
%  nl,to_file_act(Es).

%comma :- write(',').

%same(A, B) :-
%        edge(A, C, D, E, F, G, _,_),
%        edge(B, C, D, E, F, G, _,_).

%subfind(I,J,LReln,RReln) :-
%  edge(I,Left,Right,Tag,SVs,Iqs,_,_),
%  edge(J,Left,Right,STag,SSVs,SIqs,_,_),
%  subsume([s(Tag,SVs,STag,SSVs)],Iqs,SIqs,<,>,LReln,RReln,[],[]),
%  comparable(LReln,RReln).

%comparable(LReln,RReln) :-
%  (LReln \== #,! ; RReln \== #).

% [269,266,263,260,220,214,177,171]

subsume(Desc1,Desc2,LReln,RReln) :-
  call_residue(add_to(Desc1,FS1),FS1,Residue1),
  call_residue(add_to(Desc2,FS2),FS2,Residue2),
  empty_avl(H),
  empty_avl(K),
  filter_iqs(Residue1,Iqs1,_),
  filter_iqs(Residue2,Iqs2,_),
  subsume(s(FS1,FS2,sdone),<,>,LReln,RReln,H,K,Iqs1,Iqs2).
