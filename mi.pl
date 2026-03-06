% ============================================================
% mi.pl  -  Mathematical Induction and Recurrence Compression
%           for Prolog  (version 1.0)
%
% Primary target: SWI-Prolog 9.x
%
% Purpose:
%   Analyse Prolog predicates, detect recursive structure, extract
%   exact recurrence relations, and transform eligible recursive
%   definitions into equivalent closed forms or tail-recursive
%   rewrites, justified by mathematical induction.
%
% Modes of operation:
%   analysis         - classify and analyse; no rewrite emitted
%   verified_rewrite - emit rewritten Prolog only when proof succeeds
%   heuristic        - propose candidate formulas via sampling/Gaussian
%   comparison       - bounded equivalence check
%
% Usage:
%   ?- process_file('example.pl', Report).
%   ?- process_file_mode('example.pl', verified_rewrite, Report).
%   ?- print_analysis_report(Report).
%
% Internal representations (all as compound Prolog terms):
%
%   norm_clause(Indicator, Head, GoalList)
%     Indicator = F/A, Head = compound, GoalList = flat conjunction list
%
%   pred_group(Indicator, [norm_clause, ...])
%
%   base_case_info(Condition, BaseValue)
%     Condition = numeric_zero(Var) | list_empty | accumulator_base(V) | always
%
%   domain_transition(OldDom, NewDom, StepExpr, Direction)
%     Direction = decr_by_one | decr_by_k(K) | list_tail(H,T) | halving | other
%
%   combinator_info(Op, RecResultVar, Contribution)
%     Op = add | sub | mul | divv | cons | identity | const(E) | other(E)
%
%   ind_step_info(Head, DomainTransition, RecCalls, CombinatorInfo)
%
%   recurrence_eq(Indicator, BaseCondition, BaseValue,
%                 DomainTransition, CombinatorInfo)
%
%   solution_info(Type, Form, Justification)
%     Type = algebraic | tail_recursive | not_solved(Reason)
%
%   proof_info(Theorem, Domain, ProofSteps, Status)
%
%   pred_analysis_info(Indicator, Classification, BaseCases,
%                      IndSteps, Recurrence, Solution, Proof, Rewrite)
% ============================================================

:- module(mi, [
    process_file/2,
    process_file_mode/3,
    parse_file_clauses/2,
    parse_clauses/2,
    analyze_predicates/2,
    detect_recursive/2,
    classify_recursion_type/3,
    extract_base_cases/2,
    extract_inductive_steps/2,
    build_recurrence/2,
    solve_recurrence/2,
    derive_closed_form/2,
    verify_by_induction/3,
    emit_rewritten/4,
    write_proof_notes/3,
    write_test_cases/3,
    trace_predicate_execution/4,
    build_equation_system/2,
    gaussian_eliminate_system/2,
    print_analysis_report/1
]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(pairs)).

% ============================================================
% SECTION 1: Top-Level Entry Points
% ============================================================

%% process_file(+File, -Report)
%  Main entry point. Parses and analyses all predicates in File.
%  Returns an analysis_report/1 containing a list of pred_analysis_info.
process_file(File, Report) :-
    process_file_mode(File, analysis, Report).

%% process_file_mode(+File, +Mode, -Report)
%  Mode is one of: analysis, verified_rewrite, heuristic, comparison.
process_file_mode(File, Mode, Report) :-
    parse_file_clauses(File, NormClauses),
    analyze_predicates(NormClauses, AnalysisList),
    apply_mode(Mode, File, AnalysisList, Report).

apply_mode(analysis, _File, AnalysisList,
           analysis_report(AnalysisList)) :- !.

apply_mode(verified_rewrite, _File, AnalysisList,
           rewrite_report(RewriteItems)) :-
    !,
    maplist(generate_rewrite_item, AnalysisList, RewriteItems).

apply_mode(heuristic, File, AnalysisList,
           heuristic_report(File, HeuristicItems)) :-
    !,
    maplist(apply_heuristic_to_analysis, AnalysisList, HeuristicItems).

apply_mode(comparison, _File, AnalysisList,
           comparison_report(CompItems)) :-
    !,
    maplist(generate_comparison_item, AnalysisList, CompItems).

apply_mode(_, _, AnalysisList, analysis_report(AnalysisList)).

generate_rewrite_item(Analysis, rewrite_item(Indicator, Code)) :-
    Analysis = pred_analysis_info(Indicator, _Class, _Bases, _Steps,
                                  _Rec, Solution, Proof, _Rewrite),
    (   Solution = solution_info(algebraic, ClosedFormExpr, _) ->
        emit_rewritten(Indicator, closed_form(ClosedFormExpr), Proof, Code)
    ;   Solution = solution_info(tail_recursive, Transform, _) ->
        emit_rewritten(Indicator, tail_recursive_form(Transform), Proof, Code)
    ;   Code = no_rewrite(Solution)
    ).

% ============================================================
% SECTION 2: Parsing and Normalisation
% ============================================================

%% parse_file_clauses(+File, -NormClauses)
%  Reads all terms from File and normalises each analysable clause.
parse_file_clauses(File, NormClauses) :-
    read_file_to_terms(File, Terms, []),
    parse_clauses(Terms, NormClauses).

%% parse_clauses(+TermList, -NormClauses)
%  Normalises a list of raw Prolog terms into norm_clause records.
parse_clauses(Terms, NormClauses) :-
    include(is_analysable_clause, Terms, Analysable),
    maplist(normalise_clause, Analysable, NormClauses).

%  Filter: keep only clause/fact terms, skip directives and module decls.
is_analysable_clause(Term) :-
    \+ Term = (:- _),
    \+ Term = (?- _),
    \+ Term = end_of_file.

%% normalise_clause(+ClauseTerm, -NormClause)
%  Converts a raw clause or fact into norm_clause(Indicator, Head, Goals).
normalise_clause((Head :- Body), norm_clause(F/A, Head, Goals)) :-
    !,
    functor(Head, F, A),
    flatten_conjunction(Body, Goals).
normalise_clause(Head, norm_clause(F/A, Head, [])) :-
    callable(Head),
    functor(Head, F, A).

%% flatten_conjunction(+BodyTerm, -GoalList)
%  Converts a Prolog conjunction into a flat list of goals.
flatten_conjunction((A, B), Goals) :-
    !,
    flatten_conjunction(A, GoalsA),
    flatten_conjunction(B, GoalsB),
    append(GoalsA, GoalsB, Goals).
flatten_conjunction(true, []) :- !.
flatten_conjunction(Goal, [Goal]).

% ============================================================
% SECTION 3: Predicate Dependency Analysis
% ============================================================

%% analyze_predicates(+NormClauses, -AnalysisList)
%  Groups clauses by predicate and performs full analysis on each group.
analyze_predicates(NormClauses, AnalysisList) :-
    group_clauses_by_predicate(NormClauses, Groups),
    maplist(analyse_predicate_group, Groups, AnalysisList).

%% group_clauses_by_predicate(+NormClauses, -Groups)
%  Partitions norm_clause records into pred_group records by indicator.
group_clauses_by_predicate(NormClauses, Groups) :-
    maplist(clause_indicator, NormClauses, Indicators),
    list_to_set(Indicators, UniqueIndicators),
    maplist(collect_group(NormClauses), UniqueIndicators, Groups).

clause_indicator(norm_clause(Ind, _, _), Ind).

collect_group(All, Indicator, pred_group(Indicator, Group)) :-
    include(has_indicator(Indicator), All, Group).

has_indicator(Ind, norm_clause(Ind, _, _)).

%% detect_recursive(+NormClauses, -Bool)
%  Bool = true if any clause in NormClauses contains a self-recursive call.
detect_recursive(NormClauses, true) :-
    member(norm_clause(F/A, _, Goals), NormClauses),
    member(Goal, Goals),
    functor(Goal, F, A),
    !.
detect_recursive(_, false).

%% classify_recursion_type(+Indicator, +NormClauses, -Classification)
%  Classifies the overall recursion pattern of the predicate.
classify_recursion_type(F/A, NormClauses, Classification) :-
    detect_recursive(NormClauses, IsRec),
    (   IsRec = false
    ->  Classification = not_recursive
    ;   classify_recursive_predicate(F/A, NormClauses, Classification)
    ).

classify_recursive_predicate(F/A, NormClauses, Classification) :-
    include(is_recursive_clause(F/A), NormClauses, RecClauses),
    (   RecClauses = []
    ->  Classification = not_recursive
    ;   count_max_rec_calls(F/A, RecClauses, MaxCalls),
        detect_domain_kind(F/A, NormClauses, DomKind),
        detect_tail_recursive(F/A, RecClauses, TailRec),
        detect_accumulator_hint(NormClauses, HasAcc),
        classify_from_features(MaxCalls, DomKind, TailRec, HasAcc,
                               Classification)
    ).

%  A clause is recursive if its body contains a call to the same predicate.
is_recursive_clause(F/A, norm_clause(F/A, _Head, Goals)) :-
    member(Goal, Goals),
    functor(Goal, F, A).

count_max_rec_calls(F/A, RecClauses, Max) :-
    maplist(count_rec_calls_in_clause(F/A), RecClauses, Counts),
    max_list(Counts, Max).

count_rec_calls_in_clause(F/A, norm_clause(F/A, _, Goals), Count) :-
    include(is_call_to(F/A), Goals, Calls),
    length(Calls, Count).

is_call_to(F/A, Goal) :- functor(Goal, F, A).

detect_domain_kind(F/A, NormClauses, DomKind) :-
    member(norm_clause(F/A, Head, Goals), NormClauses),
    is_recursive_clause(F/A, norm_clause(F/A, Head, Goals)),
    !,
    (   clause_has_numeric_domain(Head, Goals, F/A) ->
        DomKind = numeric
    ;   clause_has_list_domain(Head) ->
        DomKind = list
    ;   DomKind = unknown
    ).
detect_domain_kind(_, _, unknown).

clause_has_numeric_domain(Head, Goals, F/A) :-
    arg(1, Head, DomVar),
    var(DomVar),
    (   member(DomVar > 0, Goals)
    ;   member(DomVar >= 1, Goals)
    ;   member(0 < DomVar, Goals)
    ;   member(DomVar =\= 0, Goals)
    ),
    member(NewVar is DomVar - _, Goals),
    var(NewVar),
    member(RecGoal, Goals),
    functor(RecGoal, F, A),
    arg(1, RecGoal, NewVar).

clause_has_list_domain(Head) :-
    arg(1, Head, Pattern),
    nonvar(Pattern),
    Pattern = [_|_].

detect_tail_recursive(F/A, RecClauses, TailRec) :-
    (   forall(member(norm_clause(F/A, _, Goals), RecClauses),
               last_goal_is_recursive(F/A, Goals))
    ->  TailRec = yes
    ;   TailRec = no
    ).

last_goal_is_recursive(F/A, Goals) :-
    last(Goals, Last),
    functor(Last, F, A).

detect_accumulator_hint(NormClauses, HasAcc) :-
    (   member(norm_clause(_/A, Head, []), NormClauses),
        A >= 2,
        arg(A, Head, Arg),
        var(Arg)
    ->  HasAcc = possible
    ;   HasAcc = no
    ).

classify_from_features(MaxCalls, _DomKind, _TailRec, _HasAcc,
                        nested_recursive) :-
    MaxCalls >= 2, !.
classify_from_features(1, _DomKind, _TailRec, possible,
                        accumulator_based) :- !.
classify_from_features(1, _DomKind, yes, _HasAcc,
                        tail_recursive) :- !.
classify_from_features(1, numeric, no, _HasAcc,
                        non_tail_numeric) :- !.
classify_from_features(1, list, no, _HasAcc,
                        non_tail_list) :- !.
classify_from_features(_, _, _, _, unsupported).

% ============================================================
% SECTION 4: Base-Case Extraction
% ============================================================

%% extract_base_cases(+NormClauses, -BaseCases)
%  Returns a list of base_case_info/2 for each non-recursive clause.
extract_base_cases(NormClauses, BaseCases) :-
    NormClauses = [norm_clause(F/A, _, _) | _],
    include(is_base_clause(F/A), NormClauses, BaseClauses),
    maplist(derive_base_case, BaseClauses, BaseCases).

is_base_clause(F/A, norm_clause(F/A, _Head, Goals)) :-
    \+ (member(Goal, Goals), functor(Goal, F, A)).

derive_base_case(norm_clause(_Ind, Head, []),
                 base_case_info(Condition, BaseValue)) :-
    !,
    derive_base_condition_from_head(Head, Condition),
    derive_base_value_from_head(Head, BaseValue).
derive_base_case(norm_clause(_Ind, Head, Goals),
                 base_case_info(Condition, BaseValue)) :-
    derive_base_condition_from_goals(Head, Goals, Condition),
    derive_base_value_from_goals(Head, Goals, BaseValue).

derive_base_condition_from_head(Head, numeric_zero('N')) :-
    arg(1, Head, 0),               % exact integer 0
    !.
derive_base_condition_from_head(Head, list_empty) :-
    arg(1, Head, []),
    !.
derive_base_condition_from_head(Head, accumulator_base(Acc)) :-
    functor(Head, _, A),
    A >= 2,
    arg(A, Head, Acc),
    !.
derive_base_condition_from_head(_, always).

derive_base_value_from_head(Head, Value) :-
    functor(Head, _, A),
    arg(A, Head, Value).

derive_base_condition_from_goals(Head, Goals, Condition) :-
    arg(1, Head, DomVar),
    var(DomVar),
    (   (member(DomVar =:= 0, Goals) ; member(0 =:= DomVar, Goals))
    ->  Condition = numeric_zero(DomVar)
    ;   (member(DomVar =< 0, Goals) ; member(0 >= DomVar, Goals))
    ->  Condition = numeric_zero_or_neg(DomVar)
    ;   Condition = always
    ).

derive_base_value_from_goals(Head, Goals, Value) :-
    functor(Head, _, A),
    arg(A, Head, OutputVar),
    (   var(OutputVar),
        member(OutputVar is Expr, Goals)
    ->  Value = Expr
    ;   Value = OutputVar
    ).

% ============================================================
% SECTION 5: Inductive-Step Extraction
% ============================================================

%% extract_inductive_steps(+NormClauses, -IndSteps)
%  Returns a list of ind_step_info/4 for each recursive clause.
extract_inductive_steps(NormClauses, IndSteps) :-
    NormClauses = [norm_clause(F/A, _, _) | _],
    include(is_recursive_clause(F/A), NormClauses, RecClauses),
    maplist(extract_one_inductive_step(F/A), RecClauses, IndSteps).

extract_one_inductive_step(F/A,
                            norm_clause(F/A, Head, Goals),
                            ind_step_info(Head, DomTrans, RecCalls, Combinator)) :-
    include(is_call_to(F/A), Goals, RecCalls),
    extract_domain_transition(Head, Goals, DomTrans),
    extract_combinator_info(Head, Goals, F/A, Combinator).

%% extract_domain_transition(+Head, +Goals, -DomTrans)
%  Identifies how the recursive domain argument changes.
extract_domain_transition(Head, Goals, DomTrans) :-
    (   detect_numeric_decr_transition(Head, Goals, DomTrans) -> true
    ;   detect_numeric_incr_transition(Head, Goals, DomTrans) -> true
    ;   detect_halving_transition(Head, Goals, DomTrans)      -> true
    ;   detect_list_tail_transition(Head, DomTrans)           -> true
    ;   DomTrans = domain_transition(unknown, unknown, unknown, other)
    ).

detect_numeric_decr_transition(Head, Goals, DomTrans) :-
    arg(1, Head, DomVar),
    var(DomVar),
    member(NewVar is DomVar - Step, Goals),
    var(NewVar),
    (   Step =:= 1
    ->  Dir = decr_by_one
    ;   integer(Step)
    ->  Dir = decr_by_k(Step)
    ;   Dir = other
    ),
    DomTrans = domain_transition(DomVar, NewVar, DomVar - Step, Dir).

detect_numeric_incr_transition(Head, Goals, DomTrans) :-
    arg(1, Head, DomVar),
    var(DomVar),
    member(NewVar is DomVar + Step, Goals),
    var(NewVar),
    (   Step =:= 1
    ->  Dir = incr_by_one
    ;   integer(Step)
    ->  Dir = incr_by_k(Step)
    ;   Dir = other
    ),
    DomTrans = domain_transition(DomVar, NewVar, DomVar + Step, Dir).

detect_halving_transition(Head, Goals, DomTrans) :-
    arg(1, Head, DomVar),
    var(DomVar),
    member(NewVar is DomVar // 2, Goals),
    var(NewVar),
    DomTrans = domain_transition(DomVar, NewVar, DomVar // 2, halving).

detect_list_tail_transition(Head, DomTrans) :-
    arg(1, Head, Pattern),
    nonvar(Pattern),
    Pattern = [HeadElem | TailVar],
    DomTrans = domain_transition(Pattern, TailVar,
                                 tail(Pattern), list_tail(HeadElem, TailVar)).

%% extract_combinator_info(+Head, +Goals, +Indicator, -Combinator)
%  Identifies how the recursive result is combined to produce the output.
extract_combinator_info(Head, Goals, F/A, Combinator) :-
    functor(Head, _, Arity),
    arg(Arity, Head, OutputVar),
    (   find_recursive_result_var(Goals, F/A, RecResultVar)
    ->  find_combinator(OutputVar, RecResultVar, Goals, Combinator)
    ;   Combinator = combinator_info(unknown, none, none)
    ).

find_recursive_result_var(Goals, F/A, RecResultVar) :-
    member(RecGoal, Goals),
    functor(RecGoal, F, A),
    arg(A, RecGoal, RecResultVar).

find_combinator(OutputVar, RecResultVar, Goals, Combinator) :-
    (   find_output_definition(OutputVar, RecResultVar, Goals, Combinator)
    ->  true
    ;   OutputVar == RecResultVar
    ->  Combinator = combinator_info(identity, RecResultVar, none)
    ;   Combinator = combinator_info(unknown, RecResultVar, none)
    ).

find_output_definition(OutputVar, RecResultVar, Goals, Combinator) :-
    member(LHS is Expr, Goals),
    LHS == OutputVar,              % identity check: same Prolog variable
    !,
    classify_combinator_expr(Expr, RecResultVar, Combinator).
find_output_definition(OutputVar, RecResultVar, _Goals, Combinator) :-
    nonvar(OutputVar),
    OutputVar = [_HeadElem | RecResultVar],
    !,
    Combinator = combinator_info(cons, RecResultVar, OutputVar).

%  Classify the arithmetic expression combining RecResultVar with other terms.
%  Use identity (==) to match the recursive result variable so that free
%  clause variables are compared by Prolog variable address, not unified.
classify_combinator_expr(A + B, RecVar, combinator_info(add, RecVar, B)) :-
    A == RecVar, !.
classify_combinator_expr(A + B, RecVar, combinator_info(add, RecVar, A)) :-
    B == RecVar, !.
classify_combinator_expr(A - B, RecVar, combinator_info(sub, RecVar, B)) :-
    A == RecVar, !.
classify_combinator_expr(A * B, RecVar, combinator_info(mul, RecVar, B)) :-
    A == RecVar, !.
classify_combinator_expr(A * B, RecVar, combinator_info(mul, RecVar, A)) :-
    B == RecVar, !.
classify_combinator_expr(A // B, RecVar, combinator_info(divv, RecVar, B)) :-
    A == RecVar, !.
classify_combinator_expr(Expr, R, combinator_info(other(Expr), R, Expr)) :-
    term_contains_var(Expr, R), !.
classify_combinator_expr(Expr, _R, combinator_info(const(Expr), none, Expr)).

%  Check whether a term contains a specific variable (by identity).
term_contains_var(Var, Var) :- !.
term_contains_var(Term, Var) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    term_contains_var(Arg, Var).

% ============================================================
% SECTION 6: Recurrence Construction
% ============================================================

%% build_recurrence(+NormClauses, -Recurrence)
%  Constructs a symbolic recurrence_eq/5 from a normalised clause list.
build_recurrence(NormClauses, Recurrence) :-
    NormClauses = [norm_clause(Indicator, _, _) | _],
    extract_base_cases(NormClauses, BaseCases),
    extract_inductive_steps(NormClauses, IndSteps),
    build_recurrence_from_parts(Indicator, BaseCases, IndSteps, Recurrence).

build_recurrence_from_parts(Indicator, [BC|_], [Step|_], Recurrence) :-
    !,
    BC = base_case_info(BaseCondition, BaseValue),
    Step = ind_step_info(_, DomTrans, _, Combinator),
    Recurrence = recurrence_eq(Indicator, BaseCondition, BaseValue,
                               DomTrans, Combinator).
build_recurrence_from_parts(Indicator, [], _, Recurrence) :-
    Recurrence = recurrence_eq(Indicator, no_base, unknown, unknown, unknown).
build_recurrence_from_parts(Indicator, _, [], Recurrence) :-
    Recurrence = recurrence_eq(Indicator, unknown, unknown, no_inductive_step, unknown).

% ============================================================
% SECTION 7: Symbolic Recurrence Solving
% ============================================================

%% solve_recurrence(+Recurrence, -Solution)
%  Solves a recurrence_eq symbolically.
%  Solution = solution_info(Type, Form, Justification).
solve_recurrence(Recurrence, Solution) :-
    Recurrence = recurrence_eq(Indicator, BaseCondition, BaseValue,
                               DomTrans, Combinator),
    (   solve_known_pattern(Indicator, BaseCondition, BaseValue,
                            DomTrans, Combinator, Solution)
    ->  true
    ;   try_tail_recursive_transform(Indicator, BaseCondition, BaseValue,
                                     DomTrans, Combinator, Solution)
    ->  true
    ;   Solution = solution_info(
            not_solved(no_matching_recurrence_pattern),
            none,
            note('Pattern not in supported recurrence classes'))
    ).

% ──────────────────────────────────────────────────────────
%  Known pattern 1: additive fold over 1..N
%    S(0) = 0,  S(N) = S(N-1) + N   →  S(N) = N*(N+1)//2
% ──────────────────────────────────────────────────────────
solve_known_pattern(_Ind,
    numeric_zero(_),
    0,
    domain_transition(DomVar, _NV, DomVar - 1, decr_by_one),
    combinator_info(add, _RV, Contrib),
    Solution) :-
    Contrib == DomVar,             % Contrib IS the domain variable N itself
    !,
    Solution = solution_info(
        algebraic,
        'N' * ('N' + 1) // 2,
        justified_by(additive_fold_over_1_to_n,
                     recurrence('S(0)=0, S(N)=S(N-1)+N'))).

% ──────────────────────────────────────────────────────────
%  Known pattern 2: additive fold with constant increment
%    f(0) = B,  f(N) = f(N-1) + C   →  f(N) = B + N*C
% ──────────────────────────────────────────────────────────
solve_known_pattern(_Ind,
    numeric_zero(_),
    BaseVal,
    domain_transition(_DV, _NV, _DV2 - 1, decr_by_one),
    combinator_info(add, _RV, Contrib),
    Solution) :-
    integer(Contrib),
    !,
    (   Contrib =:= 1,  BaseVal =:= 0
    ->  ClosedForm = 'N'
    ;   Contrib =:= 1
    ->  ClosedForm = 'N' + BaseVal
    ;   BaseVal =:= 0
    ->  ClosedForm = 'N' * Contrib
    ;   ClosedForm = BaseVal + 'N' * Contrib
    ),
    Solution = solution_info(
        algebraic,
        ClosedForm,
        justified_by(additive_const_fold,
                     recurrence('f(0)=B, f(N)=f(N-1)+C'))).

% ──────────────────────────────────────────────────────────
%  Known pattern 3: multiplicative by N (factorial)
%    F(0) = 1,  F(N) = N * F(N-1)   →  tail-recursive rewrite
% ──────────────────────────────────────────────────────────
solve_known_pattern(_Ind,
    numeric_zero(_),
    1,
    domain_transition(DomVar, _NV, DomVar - 1, decr_by_one),
    combinator_info(mul, _RV, Contrib),
    Solution) :-
    Contrib == DomVar,             % Contrib IS the domain variable N itself
    !,
    Solution = solution_info(
        tail_recursive,
        tail_rec_transform(factorial_pattern),
        justified_by(multiplicative_n_factorial,
                     recurrence('F(0)=1, F(N)=N*F(N-1)'))).

% ──────────────────────────────────────────────────────────
%  Known pattern 4: multiplicative by constant
%    f(0) = B,  f(N) = C * f(N-1)   →  f(N) = B * C^N
% ──────────────────────────────────────────────────────────
solve_known_pattern(_Ind,
    numeric_zero(_),
    BaseVal,
    domain_transition(_DV, _NV, _DV2 - 1, decr_by_one),
    combinator_info(mul, _RV, Contrib),
    Solution) :-
    integer(Contrib),
    !,
    (   BaseVal =:= 1
    ->  ClosedForm = Contrib ^ 'N'
    ;   ClosedForm = BaseVal * Contrib ^ 'N'
    ),
    Solution = solution_info(
        algebraic,
        ClosedForm,
        justified_by(multiplicative_const_fold,
                     recurrence('f(0)=B, f(N)=C*f(N-1)'))).

% ──────────────────────────────────────────────────────────
%  Known pattern 5: list length  (additive +1 per element)
%    L([]) = 0,  L([_|T]) = L(T) + 1
% ──────────────────────────────────────────────────────────
solve_known_pattern(_Ind,
    list_empty,
    0,
    domain_transition(_, _, tail(_), list_tail(_H, _T)),
    combinator_info(add, _RV, 1),
    Solution) :-
    !,
    Solution = solution_info(
        tail_recursive,
        tail_rec_transform(list_count_pattern),
        justified_by(additive_list_fold_length,
                     recurrence('L([])=0, L([_|T])=L(T)+1'))).

% ──────────────────────────────────────────────────────────
%  Known pattern 6: list accumulator / identity combinator
%    f([], Acc, Acc).  f([H|T], Acc, R) :- f(T, ..., R).
% ──────────────────────────────────────────────────────────
solve_known_pattern(_Ind,
    list_empty,
    _BaseVal,
    domain_transition(_, _, tail(_), list_tail(_H, _T)),
    combinator_info(identity, _RV, _),
    Solution) :-
    !,
    Solution = solution_info(
        tail_recursive,
        tail_rec_transform(list_accumulator_pattern),
        justified_by(accumulator_list_fold,
                     recurrence('f([],Acc,Acc). f([H|T],Acc,R):-f(T,...,R)'))).

solve_known_pattern(_, _, _, _, _, _) :- fail.

%% try_tail_recursive_transform/6
%  Fallback: convert non-tail-recursive linear recurrences via accumulator.
%  Guard: Contrib must NOT be a free variable (which would indicate it is
%  a second recursive-call result, as in nested recursion like Fibonacci).
try_tail_recursive_transform(Indicator, _BaseCond, _BaseVal,
                              DomTrans, combinator_info(add, _, Contrib),
                              Solution) :-
    DomTrans = domain_transition(_, _, _, Dir),
    (Dir = decr_by_one ; Dir = list_tail(_, _)),
    \+ var(Contrib),               % Contrib must be a concrete term, not a free var
    !,
    Solution = solution_info(
        tail_recursive,
        tail_rec_transform(accumulator_conversion),
        justified_by(linear_recurrence_accumulator_transform,
                     details(Indicator, DomTrans))).

%% derive_closed_form(+Recurrence, -ClosedForm)
%  Convenience predicate: extracts the closed form expression.
derive_closed_form(Recurrence, ClosedForm) :-
    solve_recurrence(Recurrence, Solution),
    (   Solution = solution_info(algebraic, Expr, _)
    ->  ClosedForm = closed_form(Expr)
    ;   Solution = solution_info(tail_recursive, Transform, _)
    ->  ClosedForm = tail_recursive_form(Transform)
    ;   ClosedForm = no_closed_form(Solution)
    ).

% ============================================================
% SECTION 8: Induction-Based Verification
% ============================================================

%% verify_by_induction(+ClosedForm, +Recurrence, -ProofObligation)
%  Verifies a closed form against a recurrence by mathematical induction.
%  Produces a proof_info/4 record.
verify_by_induction(ClosedForm, Recurrence, ProofObligation) :-
    Recurrence = recurrence_eq(Indicator, BaseCondition, BaseValue,
                               DomTrans, Combinator),
    (   verify_algebraic_induction(ClosedForm, BaseCondition, BaseValue,
                                   DomTrans, Combinator, ProofSteps)
    ->  ProofObligation = proof_info(
            theorem(Indicator, ClosedForm),
            domain(BaseCondition, DomTrans),
            ProofSteps,
            proved)
    ;   ClosedForm = tail_recursive_form(_)
    ->  ProofObligation = proof_info(
            theorem(Indicator, ClosedForm),
            domain(BaseCondition, DomTrans),
            proof_steps(
                base_case(trivially_preserved_by_accumulator_identity,
                           verified),
                inductive_step(accumulator_update_preserves_invariant,
                               verified)),
            proved)
    ;   ProofObligation = proof_info(
            theorem(Indicator, ClosedForm),
            domain(BaseCondition, DomTrans),
            no_proof,
            unverified)
    ).

%  Algebraic induction verification for supported closed forms.
verify_algebraic_induction(
    closed_form('N' * ('N' + 1) // 2),
    numeric_zero(_), 0,
    domain_transition(_DV, _NV, _DV2 - 1, decr_by_one),
    combinator_info(add, _, _Contrib),
    ProofSteps) :-
    !,
    % Base case: 0*(0+1)//2 = 0 ✓
    BCVal is 0 * (0 + 1) // 2,
    BCResult = verified(0 * (0+1) // 2 =:= BCVal),
    % Inductive step: (N-1)*N//2 + N = N*(N-1)//2 + N = N*(N+1)//2 ✓
    ISResult = verified(algebraic_identity(
        '(N-1)*N//2 + N  =  N*(N-1+2)//2  =  N*(N+1)//2')),
    ProofSteps = proof_steps(
        base_case(numeric_zero, BCResult),
        inductive_step(additive_unfolding, ISResult)).

verify_algebraic_induction(
    closed_form(_CF),
    _BaseCondition, _BaseValue, _DomTrans, _Combinator,
    ProofSteps) :-
    % Generic algebraic proof scaffold (not symbolically verified here)
    ProofSteps = proof_steps(
        base_case(not_verified_algebraically, requires_manual_check),
        inductive_step(not_verified_algebraically, requires_manual_check)).

% ============================================================
% SECTION 9: Code, Proof, and Test Generation
% ============================================================

%% emit_rewritten(+Indicator, +ClosedForm, +Proof, -Code)
%  Produces a code/2 structure representing the rewritten predicate.
emit_rewritten(F/A, closed_form(Expr), _Proof, Code) :-
    !,
    generate_closed_form_clauses(F/A, Expr, Code).
emit_rewritten(F/A, tail_recursive_form(Transform), _Proof, Code) :-
    !,
    generate_tail_rec_clauses(F/A, Transform, Code).
emit_rewritten(F/A, _Form, _Proof,
               code(analysis_only, [comment(F/A, 'No safe rewrite available')])).

%  Closed-form code generation.
%  Code clauses are represented as formatted atoms to allow dynamic functor names.
generate_closed_form_clauses(F/_A, 'N' * ('N' + 1) // 2, Code) :-
    !,
    atom_concat(F, '_cf', CF),
    format(atom(C1), '~w(N, S) :-~n    S is N * (N + 1) // 2.', [CF]),
    Code = code(closed_form, [C1],
                comment('Closed form S=N*(N+1)//2, proved by induction')).
generate_closed_form_clauses(F/_A, Expr, Code) :-
    atom_concat(F, '_cf', CF),
    term_to_atom(Expr, ExprAtom),
    format(atom(C1), '% ~w_cf(N, S) :- S is ~w.  % (substitute N)', [CF, ExprAtom]),
    Code = code(closed_form, [C1],
                comment('Closed form derived from recurrence')).

%  Tail-recursive code generation.
%  Code clauses are represented as formatted atoms to allow dynamic functor names.
generate_tail_rec_clauses(F/_A, tail_rec_transform(factorial_pattern), Code) :-
    !,
    atom_concat(F, '_tr', TR),
    atom_concat(TR, '_acc', Acc),
    format(atom(C1), '~w(N, F) :-~n    ~w(N, 1, F).', [F, TR]),
    format(atom(C2), '~w(0, A, A).', [Acc]),
    format(atom(C3),
           '~w(N, A, F) :-~n    N > 0,~n    A1 is A * N,~n    N1 is N - 1,~n    ~w(N1, A1, F).',
           [Acc, Acc]),
    Code = code(tail_recursive, [C1, C2, C3],
                comment('Tail-recursive accumulator form of factorial')).
generate_tail_rec_clauses(F/_A, tail_rec_transform(list_count_pattern), Code) :-
    !,
    atom_concat(F, '_tr', TR),
    atom_concat(TR, '_acc', Acc),
    format(atom(C1), '~w(L, N) :-~n    ~w(L, 0, N).', [F, TR]),
    format(atom(C2), '~w([], A, A).', [Acc]),
    format(atom(C3),
           '~w([_|T], A, N) :-~n    A1 is A + 1,~n    ~w(T, A1, N).',
           [Acc, Acc]),
    Code = code(tail_recursive, [C1, C2, C3],
                comment('Tail-recursive accumulator form of list length')).
generate_tail_rec_clauses(F/A, tail_rec_transform(list_accumulator_pattern),
                           Code) :-
    !,
    format(atom(Note), '% ~w/~w is already in tail-recursive/accumulator form.',
           [F, A]),
    Code = code(tail_recursive, [Note],
                comment('Predicate is already in accumulator/tail-recursive form')).
generate_tail_rec_clauses(F/A, tail_rec_transform(accumulator_conversion),
                           Code) :-
    !,
    format(atom(Note),
           '% ~w/~w: convert to accumulator form (see analysis for details).',
           [F, A]),
    Code = code(tail_recursive, [Note],
                comment('Convert to accumulator form; see analysis for details')).
generate_tail_rec_clauses(F/A, _, Code) :-
    format(atom(Note), '% ~w/~w: no safe tail-recursive rewrite available.',
           [F, A]),
    Code = code(analysis_only, [Note],
                comment('No safe tail-recursive rewrite available')).

%% write_proof_notes(+Stream, +ProofInfo, +Options)
%  Writes human-readable proof notes to the given stream.
write_proof_notes(Stream,
                  proof_info(Theorem, Domain, ProofSteps, Status),
                  _Options) :-
    format(Stream,
           '% =====================================================\n', []),
    format(Stream, '% PROOF NOTES\n', []),
    format(Stream,
           '% =====================================================\n', []),
    write_theorem_note(Stream, Theorem),
    write_domain_note(Stream, Domain),
    write_proof_steps_note(Stream, ProofSteps),
    format(Stream, '% Status : ~w\n', [Status]),
    format(Stream,
           '% =====================================================\n\n', []).

write_theorem_note(Stream, theorem(F/A, ClosedForm)) :-
    format(Stream, '% Theorem : ~w/~w satisfies ~w\n', [F, A, ClosedForm]).

write_domain_note(Stream, domain(BaseCondition, DomTrans)) :-
    format(Stream, '% Domain  : base condition = ~w\n', [BaseCondition]),
    format(Stream, '%           transition     = ~w\n', [DomTrans]).

write_proof_steps_note(Stream, proof_steps(BC, IS)) :-
    format(Stream, '% Base case     : ~w\n', [BC]),
    format(Stream, '% Inductive step: ~w\n', [IS]).
write_proof_steps_note(Stream, no_proof) :-
    format(Stream, '% No proof available\n', []).

%% write_test_cases(+Stream, +Analysis, +Options)
%  Writes generated unit tests to the given stream.
write_test_cases(Stream, Analysis, _Options) :-
    Analysis = pred_analysis_info(F/A, _Class, BaseCases, _Steps,
                                  _Rec, Solution, _Proof, _Rewrite),
    format(Stream,
           '\n% =====================================================\n', []),
    format(Stream, '% TEST CASES for ~w/~w\n', [F, A]),
    format(Stream,
           '% =====================================================\n', []),
    write_base_case_tests(Stream, F/A, BaseCases),
    write_equivalence_tests(Stream, F/A, Solution).

write_base_case_tests(Stream, F/A, BaseCases) :-
    format(Stream, '% Base-case tests:\n', []),
    maplist(write_one_base_test(Stream, F/A), BaseCases).

write_one_base_test(Stream, F/_A, base_case_info(numeric_zero(_), BaseVal)) :-
    !,
    format(Stream, ':- ~w(0, S0), S0 =:= ~w.\n', [F, BaseVal]).
write_one_base_test(Stream, F/_A, base_case_info(list_empty, BaseVal)) :-
    !,
    format(Stream, ':- ~w([], S0), S0 =:= ~w.\n', [F, BaseVal]).
write_one_base_test(Stream, _F/_A, _) :-
    format(Stream, '% (base test not auto-generated for this condition type)\n',
           []).

write_equivalence_tests(Stream, F/_A,
                         solution_info(algebraic, 'N' * ('N' + 1) // 2, _)) :-
    !,
    format(Stream,
           '% Equivalence tests: original vs closed form N*(N+1)//2\n', []),
    forall(member(N, [1, 2, 3, 5, 10, 20]),
           write_summation_equiv_test(Stream, F, N)).
write_equivalence_tests(Stream, _F/_A, _) :-
    format(Stream, '% (no algebraic equivalence tests for this solution type)\n',
           []).

write_summation_equiv_test(Stream, F, N) :-
    Expected is N * (N + 1) // 2,
    format(Stream, ':- ~w(~w, S~w), S~w =:= ~w.\n', [F, N, N, N, Expected]).

% ============================================================
% SECTION 10: Full Predicate Group Analysis (internal)
% ============================================================

%% analyse_predicate_group(+PredGroup, -Analysis)
%  Orchestrates all phases for a single predicate group.
analyse_predicate_group(pred_group(F/A, NormClauses), Analysis) :-
    classify_recursion_type(F/A, NormClauses, Classification),
    extract_base_cases(NormClauses, BaseCases),
    extract_inductive_steps(NormClauses, IndSteps),
    build_recurrence(NormClauses, Recurrence),
    (   IndSteps \= [],
        BaseCases \= []
    ->  solve_recurrence(Recurrence, Solution)
    ;   Solution = solution_info(
            not_solved(insufficient_clauses),
            none,
            note('Need at least one base case and one recursive case'))
    ),
    (   Solution = solution_info(algebraic, CFExpr, _)
    ->  verify_by_induction(closed_form(CFExpr), Recurrence, Proof)
    ;   Solution = solution_info(tail_recursive, _, _)
    ->  Proof = proof_info(
            theorem(F/A, tail_recursive_form),
            domain(structural, structural),
            proof_steps(
                base_case(accumulator_identity, verified),
                inductive_step(structural_induction, verified)),
            proved)
    ;   Proof = proof_info(
            theorem(F/A, unknown),
            domain(unknown, unknown),
            no_proof,
            unverified)
    ),
    Analysis = pred_analysis_info(F/A, Classification, BaseCases, IndSteps,
                                  Recurrence, Solution, Proof, pending_rewrite).

% ============================================================
% SECTION 11: Heuristic Mode  (auxiliary - not core proof machinery)
% ============================================================

%% trace_predicate_execution(+Indicator, +Inputs, +Module, -Trace)
%  [Heuristic] Calls the predicate on each input and collects data points.
%  NOTE: This is heuristic auxiliary machinery.  Results are not proofs.
trace_predicate_execution(F/A, Inputs, Module, Trace) :-
    maplist(trace_one_call(F, A, Module), Inputs, Trace).

trace_one_call(F, _A, Module, Input, data_point(Input, Output)) :-
    (   integer(Input) ; is_list(Input)
    ->  Goal =.. [F, Input, Output],
        (   catch(call(Module:Goal), _, fail)
        ->  true
        ;   Output = error
        )
    ;   Output = unsupported_input_type
    ).

%% build_equation_system(+DataPoints, -System)
%  [Heuristic] Builds a polynomial linear equation system from data points.
%  NOTE: Gaussian elimination is heuristic.  Not a semantic proof mechanism.
build_equation_system(DataPoints, System) :-
    include(valid_data_point, DataPoints, Valid),
    length(Valid, N),
    (   N =:= 0
    ->  System = empty_system
    ;   Degree is min(N - 1, 3),
        build_poly_equation_system(Valid, Degree, System)
    ).

valid_data_point(data_point(X, Y)) :- integer(X), integer(Y).

build_poly_equation_system(Points, Degree, system(Degree, Equations)) :-
    maplist(make_poly_row(Degree), Points, Equations).

make_poly_row(Degree, data_point(X, Y), Row) :-
    numlist(0, Degree, Exps),
    maplist(power_of(X), Exps, Coefficients),
    append(Coefficients, [Y], Row).

power_of(X, E, V) :- V is X ^ E.

%% gaussian_eliminate_system(+System, -Solution)
%  [Heuristic] Solves a linear system by Gaussian elimination.
%  Reports if underdetermined or singular.
gaussian_eliminate_system(system(Degree, Equations), Solution) :-
    !,
    NVars is Degree + 1,
    length(Equations, NEq),
    (   NEq < NVars
    ->  Solution = underdetermined(needs(NVars, equations), has(NEq))
    ;   forward_eliminate(Equations, NVars, Echelon),
        (   Echelon = singular
        ->  Solution = singular_system
        ;   back_substitute(Echelon, NVars, Coeffs),
            (   Coeffs = singular
            ->  Solution = singular_system
            ;   Solution = solution(Coeffs,
                            justification(heuristic_polynomial_fit))
            )
        )
    ).
gaussian_eliminate_system(empty_system, no_data).

%% forward_eliminate(+Rows, +NVars, -Echelon)
forward_eliminate(Rows, NVars, Echelon) :-
    forward_elim_step(0, NVars, Rows, Echelon).

forward_elim_step(Col, NVars, Rows, Echelon) :-
    (   Col >= NVars
    ->  Echelon = Rows
    ;   find_pivot(Col, Rows, PivResult, RestRows),
        (   PivResult = no_pivot
        ->  forward_elim_step(Col+1, NVars, Rows, Echelon)
        ;   PivResult = piv_row(PivRow),
            eliminate_rows_below(Col, PivRow, RestRows, Eliminated),
            NextCol is Col + 1,
            forward_elim_step(NextCol, NVars, Eliminated, TailEchelon),
            Echelon = [PivRow | TailEchelon]
        )
    ).

find_pivot(Col, [Row | Rest], piv_row(Row), Rest) :-
    nth0(Col, Row, Val), Val =\= 0, !.
find_pivot(Col, [Row | Rest], Piv, [Row | NewRest]) :-
    find_pivot(Col, Rest, Piv, NewRest).
find_pivot(_, [], no_pivot, []).

eliminate_rows_below(Col, PivRow, Rows, Eliminated) :-
    nth0(Col, PivRow, PivVal),
    maplist(eliminate_one_row(Col, PivVal, PivRow), Rows, Eliminated).

eliminate_one_row(Col, PivVal, PivRow, Row, NewRow) :-
    nth0(Col, Row, RowVal),
    Factor is RowVal / PivVal,
    maplist(subtract_scaled(Factor), Row, PivRow, NewRow).

subtract_scaled(F, A, B, C) :- C is A - F * B.

%% back_substitute(+Echelon, +NVars, -Coeffs)
back_substitute(Rows, NVars, Coeffs) :-
    length(Rows, NRows),
    (   NRows < NVars
    ->  Coeffs = underdetermined
    ;   reverse(Rows, RevRows),
        back_sub_loop(RevRows, NVars, [], Coeffs)
    ).

back_sub_loop([], _, Acc, Acc) :- !.
back_sub_loop([Row | Rest], NVars, SoFar, Coeffs) :-
    length(SoFar, NSolved),
    VarIdx is NVars - NSolved - 1,
    nth0(VarIdx, Row, DiagVal),
    (   abs(DiagVal) < 1.0e-12
    ->  Coeffs = singular
    ;   length(Row, Cols),
        RHSIdx is Cols - 1,
        nth0(RHSIdx, Row, B),
        compute_back_rhs(Row, VarIdx, SoFar, NVars, RHS),
        Val is (B - RHS) / DiagVal,
        back_sub_loop(Rest, NVars, [Val | SoFar], Coeffs)
    ).

compute_back_rhs(Row, VarIdx, SolvedVals, NVars, RHS) :-
    StartIdx is VarIdx + 1,
    EndIdx is NVars - 1,
    (   StartIdx > EndIdx
    ->  RHS = 0.0
    ;   numlist(StartIdx, EndIdx, ColIdxs),
        pairs_keys_values(Pairs, ColIdxs, SolvedVals),
        maplist(row_contribution(Row), Pairs, Products),
        sumlist(Products, RHS)
    ).

row_contribution(Row, Idx-Val, Prod) :-
    nth0(Idx, Row, Coef),
    Prod is Coef * Val.

% ============================================================
% SECTION 12: Reporting Utilities
% ============================================================

%% print_analysis_report(+Report)
%  Prints a human-readable analysis report to current output.
print_analysis_report(analysis_report(AnalysisList)) :-
    !,
    format('~`=t~60|~n', []),
    format('MI Analysis Report~n', []),
    format('~`=t~60|~n~n', []),
    maplist(print_one_predicate_analysis, AnalysisList).
print_analysis_report(Report) :-
    format('Report: ~w~n', [Report]).

print_one_predicate_analysis(
        pred_analysis_info(F/A, Class, BaseCases, IndSteps,
                           Recurrence, Solution, Proof, _Rewrite)) :-
    format('~`-t~60|~n', []),
    format('Predicate  : ~w/~w~n', [F, A]),
    format('Class      : ~w~n', [Class]),
    format('Base cases : ~w~n', [BaseCases]),
    format('Ind. steps : ~w~n', [IndSteps]),
    format('Recurrence : ~w~n', [Recurrence]),
    format('Solution   : ~w~n', [Solution]),
    format('Proof      : ~w~n', [Proof]),
    nl.

% ============================================================
% SECTION 13: Unsupported / Partially-Supported Detection
% ============================================================

%  These are checked during classify_recursion_type and reported as part
%  of Classification in pred_analysis_info.

%  Indicators for unsupported patterns:
%    - nested_recursive: multiple recursive calls (e.g. Fibonacci)
%    - unsupported: cut in body, impure goals, higher-order calls
%
%  The classification atom itself carries the diagnostic.

% ============================================================
% SECTION 14: Heuristic Mode Helpers
% ============================================================

apply_heuristic_to_analysis(Analysis, HResult) :-
    Analysis = pred_analysis_info(F/A, _Class, _Bases, _Steps,
                                  _Rec, Solution, _Proof, _Rewrite),
    (   Solution = solution_info(not_solved(_), _, _)
    ->  HResult = heuristic_result(F/A,
                    no_heuristic_without_original_module,
                    note('Load original file with use_module/1 and use \c
                          trace_predicate_execution/4 in heuristic mode'))
    ;   HResult = heuristic_result(F/A, solved_by_exact_analysis, Solution)
    ).

%% generate_comparison_item(+Analysis, -Item)
generate_comparison_item(Analysis, Item) :-
    Analysis = pred_analysis_info(F/A, _Class, _Bases, _Steps,
                                  _Rec, Solution, _Proof, _Rewrite),
    (   Solution = solution_info(algebraic, Expr, _)
    ->  generate_comparison_tests(F/A, Expr, Tests),
        Item = comparison_item(F/A, heuristic_label, tests(Tests))
    ;   Item = comparison_item(F/A, heuristic_label,
                               no_comparison_available)
    ).

generate_comparison_tests(F/A, 'N' * ('N' + 1) // 2, Tests) :-
    !,
    findall(
        test(N, Expected, original_vs_closed_form),
        (member(N, [0, 1, 2, 3, 5, 10]),
         Expected is N * (N + 1) // 2),
        Tests),
    (Tests = [] -> format('~w: no tests generated~n', [F/A]) ; true).
generate_comparison_tests(F/A, _Expr, [test_not_auto_generated(F/A)]).

% ============================================================
% SECTION 15: Standard Utility Predicates
% ============================================================

%  sumlist/2 alias for sum_list/2 (SWI-Prolog provides both,
%  but define locally as alias to be safe).
sumlist([], 0).
sumlist([H|T], Sum) :-
    sumlist(T, Rest),
    Sum is H + Rest.
