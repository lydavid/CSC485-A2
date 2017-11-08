% David Ly, lydavid1, 1001435501
:- ale_flag(subtypecover,_,off).
:- discontiguous sub/2,intro/2.

bot sub [mood, tense, sem, cat, pos, verbal, nominal].

	% parts of speech
    pos sub [n,p,v,det,toinf].
		toinf sub [].	% infinitival to
        n sub [].       % noun
        v sub [].       % verb
        p sub [].       % preposition? -> doesn't look like any in lexicon though...
        det sub [].     % determinant

    % phrasal categories
    cat sub [vproj, np]. % subtypes: vproj?, noun phrase
        vproj sub [inf_clause, s, vp] intro [mood:mood].  % vproj has subtype infinitive clause, sentence, verb phrase with var mood that could take on values from mood
			s intro [mood:indicative].   % sentence had var mood that could take on values from indicative
            inf_clause intro [mood:infinitive]. % infinitive clause has var mood that could take on values from infinitive
			vp intro [mood:indicative].  % verb phrase has var mood that could take on values from indicative
		np sub [].    % noun phrase has no subtype

    verbal sub [v, vproj] intro [vsem:v_sem].    % verbal has subtype verb, vproj?, with var vsem that could take on values from v_sem
    nominal sub [n, np] intro [nsem:n_sem].      % nominal has subtypes noun, noun phrase, with var nsem

	% mood and tense for verbs
	tense sub [past, present]. % tense has subtypes past and present -> we don't have to handle present tense (ex: the student expects the teacher to sleep)
		past sub [].
		present sub [].
    mood sub [indicative,infinitive].
        indicative intro [tense:tense]. % indicative has var tense that can take on values from tense
        infinitive sub [].

    % sentences and verb phrases take on indicative mood -> which have tense and should match throughout
        % The indicative mood is used to make factual statements, ask questions,
        %   or express opinions as if they were facts. Any verb tense may be deployed in the indicative mood.

    % infinitive clause takes on infinitive mood -> which don't have tense
        % Verbs in the infinitive mood are used as parts of speech more than verbs. It expresses being or action.
        %   I may go to the beach later.
        %   They came to speak to me.
        %   It's important to eat well.



	% semantics for verbs and nouns
	sem sub [v_sem, n_sem].

        % only add features for v_sem and its subtypes
        % nope, can add types anywhere such as subtyping existing types,
        % just don't alter what's already given (ie rearrange hierarchy)

		% semantics for verbs
		v_sem sub [prefer, persuade, promise, expect, sleep]
                intro [vtense:tense].   % This should not be empty!  Fill in features for this and
                                  %  the following subtypes:
			prefer sub []. %[preferrer:np, preferree:np]. % preferrer must be a noun phrase, preferree could be anything?
			persuade sub [].
			promise sub [].
			expect sub [].
			sleep sub [].

		% semantics for nouns
		n_sem sub [student, teacher].
			student sub [].
			teacher sub [].

% add lexicon? using sem that matches itself
the ---> det.
student ---> (n, nsem:student).
teacher ---> (n, nsem:teacher).
preferred ---> (v, vsem:(vtense:past)).
persuaded ---> (v, vsem:(vtense:past)).
promised ---> (v, vsem:(vtense:past)).
expected ---> (v, vsem:(vtense:past)).
to ---> toinf.
sleep ---> (v, vsem:(vtense:present)).

% add rules

% S -> NP VP
srule rule
(s, mood:(tense:Tense))
===>
cat> np,
cat> (vp, mood:(tense:Tense)).

% VP -> V NP
% "...'persuaded/promised/preferred' 'the teacher'"
% *"the student expected the teacher" -> actually kinda makes sense
vp_rule rule
(vp, mood:(tense:Tense))
===>
cat> (v, vsem:(vtense:Tense)),
cat> np.

% VP -> V inf_clause
% "...'preferred/expected/promised' 'to sleep'" -> all confirmed grammatically correct on bb
% *"the student persuaded to sleep"
vp_rule rule
vp
===>
cat> v,
cat> inf_clause.

% VP -> V NP inf_clause
% "...'persuaded/promised' 'the teacher' 'to sleep'"
% *"the student preferred the teacher to sleep"
% "the student expected the teacher to sleep" is correct, but not of this form, coincidence it's accepted here

% VP -> V complement?
% "...'expected' 'the teacher to sleep'"
% persuaded/promised needs to assign beneficiary AND theme, but only has a complement constituent here
% *"the student preferred the teacher to sleep"

% VP -> V S
% "...'expected' 'the teacher persuaded the student to sleep'"
% *"the student promised the teacher persuaded the student to sleep" -> promise needs beneficiary AND theme
% *"the student preferred the teacher persuaded the student to sleep"
% *"the student persuaded the teacher promised the student to sleep"

% VP -> V NP S
% "...'promised' 'the teacher' 'the student preferred to sleep'"

% NP -> Det N
% "the teacher"
% "the student"
% won't ever have NP -> N in this grammar, so ignore it
np_rule rule
np
===>
cat> det,
cat> n.

% inf_clause -> toinf V
% "...to sleep"
% can't use with any other verb here, cause they aren't in infinitive form (not base)
inf_clause_rule rule
inf_clause
===>
cat> toinf,
cat> v.

% special cases
% "the student promised" is definitely grammatical
