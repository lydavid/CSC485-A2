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

	% semantics for verbs and nouns
	sem sub [v_sem, n_sem].

        % only add features for v_sem and its subtypes

		% semantics for verbs
		v_sem sub [prefer, persuade, promise, expect, sleep]
                intro [].   % This should not be empty!  Fill in features for this and
                                  %  the following subtypes:
			prefer sub [].
			persuade sub [].
			promise sub [].
			expect sub [].
			sleep sub [].

		% semantics for nouns
		n_sem sub [student, teacher].
			student sub [].
			teacher sub [].
