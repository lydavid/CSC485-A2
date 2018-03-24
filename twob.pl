% David Ly, lydavid1, 1001435501
:- ale_flag(subtypecover,_,off).
:- discontiguous sub/2,intro/2.

bot sub [mood, tense, sem, cat, pos, verbal, nominal, role].

	% parts of speech
    pos sub [n, p, v, det, toinf].
		toinf sub [].	% infinitival to
        n sub [].       % noun
        v sub [].       % verb
        p sub [].       % preposition?
        det sub [].     % determinant

    % phrasal categories
    cat sub [vproj, np].
        vproj sub [inf_clause, s, vp] intro [mood:mood].
			s intro [mood:indicative].
            inf_clause intro [mood:infinitive].
			vp intro [mood:indicative].
		np sub [].

    verbal sub [v, vproj] intro [vsem:v_sem].
    nominal sub [n, np] intro [nsem:n_sem].

	% mood and tense for verbs
	tense sub [past, present].
		past sub [].
		present sub [].
    mood sub [indicative,infinitive].
        indicative intro [tense:tense].
        infinitive sub [].

    % The possible roles for our verbs' obj/subj
    % the hierarchy allows our grammar to accept a broader category of roles such as "theme" as the obj
    role sub [agent, beneficiary, theme].
        agent sub [preferrer, persuader, promiser, expecter].
            preferrer sub []. % obj of sleep
            persuader sub [].
            promiser sub []. % obj of sleep
            expecter sub [].
        beneficiary sub [persuadee, promisee].
            persuadee sub []. % obj of sleep
            promisee sub [].
        theme sub [preferree, expectee].
            preferree sub [].
            expectee sub []. % obj of sleep

	% semantics for verbs and nouns
	sem sub [v_sem, n_sem].

		% semantics for verbs
		v_sem sub [prefer, persuade, promise, expect, sleep]
                % subj: which role is the subject of the verb
                % obj: which role is the object of the verb
                % ref: which role of the verb will be referenced as the obj of a later verb (sleep)
                intro [vtense:tense, subj:role, obj:role, ref:role].

			prefer sub [].
			persuade sub [].
			promise sub [].
			expect sub [].
			sleep sub [].

		% semantics for nouns
		n_sem sub [student, teacher].
			student sub [].
			teacher sub [].

% Lexicon
the ---> det.
student ---> (n, nsem:student).
teacher ---> (n, nsem:teacher).
preferred ---> (v, vsem:(vtense:past, subj:preferrer, obj:preferree, ref:preferrer)).
persuaded ---> (v, vsem:(vtense:past, subj:persuader, obj:persuadee, ref:persuadee)).
promised ---> (v, vsem:(vtense:past, subj:promiser, obj:promisee, ref:promiser)).
expected ---> (v, vsem:(vtense:past, subj:expecter, obj:expectee, ref:expectee)).
to ---> toinf.
sleep ---> (v, vsem:(vtense:present, obj:Role, ref:expectee)).


% S -> NP VP
srule rule
(s, vsem:(vtense:past, subj:Subj, obj:Obj, ref:Gap))
===>
cat> np,
cat> (vp, vsem:(vtense:past, subj:Subj, obj:Obj, ref:Gap)).

% VP -> V NP
% "...'preferred' 'the teacher'"
vp_rule rule
(vp, vsem:(vtense:Tense, subj:preferrer))
===>
cat> (v, vsem:(vtense:Tense, subj:preferrer)),
cat> np.

% VP -> V inf_clause
% "...'preferred/expected/' 'to sleep'"
vp_rule rule
(vp, vsem:(vtense:Tense, subj:Subj, obj:theme, ref:Gap))
===>
cat> (v, vsem:(vtense:Tense, subj:Subj, obj:theme, ref:Gap)),
cat> (inf_clause, vsem:(vtense:Tense, subj:Subj, obj:theme, ref:Gap)).

% VP -> V NP inf_clause
% "...'persuaded/promised' 'the teacher' 'to sleep'" (both have beneficiary as its obj)
vp_rule rule
(vp, vsem:(vtense:Tense, subj:Subj, obj:beneficiary, ref:Gap))
===>
cat> (v, vsem:(vtense:Tense, subj:Subj, obj:beneficiary, ref:Gap)),
cat> np,
cat> (inf_clause, vsem:(vtense:Tense, subj:Subj, obj:beneficiary, ref:Gap)).

% VP -> V S
% "...'expected' 'the teacher persuaded the student to sleep'"
vp_rule rule
(vp, mood:(tense:Tense))
===>
cat> (v, vsem:(vtense:Tense, obj:expectee)),
cat> (s, mood:(tense:Tense)).

% NP -> Det N
% "the teacher"
% "the student"
% won't ever have NP -> N in this grammar, so we ignore it
np_rule rule
np
===>
cat> det,
cat> n.

% inf_clause -> toinf V
% "...to sleep"
% V can't be any other verb here, cause they aren't in infinitive form
inf_clause_rule rule
(inf_clause, vsem:(vtense:past, subj:Subj, obj:Obj, ref:Gap))
===>
cat> toinf,
cat> (v, vsem:(vtense:present)).

% inf_clause -> NP toinf V
% "...the teacher to sleep"
% only expect can use this rule
inf_clause_rule rule
(inf_clause, vsem:(vtense:past, subj:Subj, obj:Obj, ref:Gap))
===>
cat> np,
cat> toinf,
cat> (v, vsem:(vtense:present, ref:Gap)).
