% David Ly, lydavid1, 1001435501

bot sub [case, number, cat, type].

% declare features
case sub [nom,acc].
    nom sub [].
    acc sub [].
number sub [sing,plural].
    sing sub [].
    plural sub [].
type sub [noun, pronoun].
    noun sub [].
    pronoun sub [].

% declare the categories
cat sub [s,np,vp,pp,p,det,v,n].
    s sub [].
    %n sub [noun,pronoun] intro [case:case].
    %    noun sub [] intro [number:number].
    %    pronoun sub [].

    n sub [] intro [case:case, number:number, type:type].

    np sub [] intro [head:n]. % noun phrase with head as noun (top-level)
    vp sub [] intro [obj_vp:np]. % verb phrase with object as np
    pp sub [] intro [obj_pp:np]. % preposition phrase with object as np
    p sub [].
    det sub [].
    v sub [].

% specify their grammar features
she ---> (n, type:pronoun, case:nom).
fed ---> v.
the ---> det.
dog ---> (n, type:noun, case:nom, number:sing).
dog ---> (n, type:noun, case:acc, number:sing).
puppies ---> (n, type:noun, case:nom, number:plural).
puppies ---> (n, type:noun, case:acc, number:plural).
him ---> (n, type:pronoun, case:acc).
with ---> p.

% augment Grammar 2 with features so as to restrict it to the language of Grammar 1

% Grammar 1: S -> NP VP | PROnom VP
% Grammar 2: S -> NP VP
srule rule
s
===>
cat> (np, head:(case:nom)),
cat> (vp, obj_vp:(head:(case:acc))).

% Grammar 1: VP -> V NP | V PROacc
% Grammar 2: VP -> V NP
vp_rule rule
(vp, obj_vp:(head:(case:acc)))
===>
cat> v,
cat> (np, head:(case:acc)).

% Grammar 1: PP -> P NP | P PROacc
% Grammar 2: PP -> P NP
pp_rule rule
(pp, obj_pp:(head:(case:acc)))
===>
cat> p,
cat> (np, head:(case:acc)).

% Grammar 1: NP -> Npl PP
% Grammar 2: NP -> N PP
np_rule rule
(np, head:(number:plural, type:noun))
===>
cat> (n, number:plural, type:noun),
cat> pp.

% Grammar 1: NP -> Det Nsg | Det Npl
% Grammar 2: NP -> Det N
np_rule rule
(np, head:(type:noun))
===>
cat> det,
cat> (n, type:noun).

% Grammar 1: NP -> Det Nsg PP | Det Npl PP
% Grammar 2: NP -> Det N PP
np_rule rule
(np, head:(type:noun))
===>
cat> det,
cat> (n, type:noun),
cat> pp.

% Grammar 1: NP -> Npl | PROnom | PROacc
% Grammar 2: NP -> N
%np_rule rule
%(np, head:(number:plural))
%===>
%cat> (noun, number:plural).

np_rule rule
(np, head:(number:plural, case:Case))
===>
cat> (n, number:plural, case:Case).

% separating the rules like this is cheating?
%np_rule rule
%(np, head:(case:Case))
%===>
%cat> (pronoun, case:Case).
