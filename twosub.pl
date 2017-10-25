bot sub [mood, tense, sem, cat, pos, semantic].

	% parts of speech
        pos sub [n,p,v,det,toinf].
		toinf sub [].	% infinitival to
                n sub [].
                v sub [].
                p sub [].
                det sub [].
	% phrasal categories
	cat sub [vproj,np].
		vproj sub [inf_clause,s,vp].
			s sub [] intro [mood:indicative].
                        inf_clause sub [] intro [mood:infinitive].
			vp sub [].
		np sub [].

        semantic sub [verbal, nominal] intro [sem:sem].
          verbal sub [v,vproj] intro [sem:v_sem, mood:mood].
          nominal sub [n,np] intro [sem:n_sem].
	
	% mood and tense for verbs
	tense sub [past, present].
		past sub [].	
		present sub [].
        mood sub [indicative,infinitive].
                indicative sub [tense:tense].
                infinitive sub [].

	% semantics for verbs and nouns
	sem sub [v_sem, n_sem].

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
