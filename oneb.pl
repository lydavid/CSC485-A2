% David Ly, lydavid1, 1001435501

% declare the features
%index sub [] intro [c:case, n:number, t:type].
%    case sub [nom, acc]. % nominative, accusative
%        nom sub [].
%        acc sub [].
%    number sub [sing, plural]. % singular, plural
%        sing sub [].
%        plural sub [].
%    type sub [common, pronoun]. % common noun, pronoun
%        common sub [].
%        pronoun sub [].


% declare features for np
%index_np sub [] intro [c:case,t:type].
%    case sub [nom, acc]. % nominative, accusative
%        nom sub [].
%        acc sub [].
%    type sub [common, pronoun]. % common noun, pronoun
%        common sub [].
%        pronoun sub [].

% declare features for n
%index_n sub [] intro [n:number].
%    number sub [sing, plural]. % singular, plural
%        sing sub [].
%        plural sub [].

bot sub [case, number, cat].

case sub [nom,acc].
    nom sub [].
    acc sub [].
number sub [sing,plural].
    sing sub [].
    plural sub [].

% now, how to incorporate np features?

% declare the parts of speech
cat sub [s,np,vp,pp,p,det,v,n].
    s sub [].
    %noun sub [] intro [index:index]. % declare noun with index var
    n sub [noun,pronoun] intro [case:case].
        noun sub [] intro [number:number].
        pronoun sub [].
    np sub [] intro [head:n]. % noun phrase with head as noun [head is used to pass down index var to other rules]
    vp sub [] intro [obj:np]. % verb phrase with subject as np [subj is used to pass down index var to other rules]
    pp sub [] intro [obj2:np].
    p sub [].

    det sub [].
    v sub [].

% specify their grammar features
she ---> (pronoun, case:nom). %(noun, index:(c:nom,t:pronoun)). %n.
fed ---> v. %(v, obj:(head:(index:(c:acc)))). %v.
the ---> det.
dog ---> (noun, case:nom, number:sing).%(noun, index:(c:nom,n:sing,t:common)). %n.
dog ---> (noun, case:acc, number:sing). %(noun, index:(c:acc,n:sing,t:common)). %n.
puppies ---> (noun, case:nom, number:plural). %(noun, index:(c:nom,n:plural,t:common)). %n.
puppies ---> (noun, case:acc, number:plural). %(noun, index:(c:acc,n:plural,t:common)). %n.
him ---> (pronoun, case:acc). %(noun, index:(c:acc,t:pronoun)). %n.
with ---> p.

% augment Grammar 2 with features so as to restrict it to the language of Grammar 1

% Grammar 1: S -> NP VP | PROnom VP
% Grammar 2: S -> NP VP
srule rule
s
===>
cat> (np,head:(case:nom)), % restricts to only allowing nominative
cat> (vp,obj:(head:(case:acc))).

% Grammar 1: VP -> V NP | V PROacc
% Grammar 2: VP -> V NP
vp_rule rule
(vp,obj:(head:(case:acc)))
===>
cat> v,
cat> (np,head:(case:acc)).

% Grammar 1: PP -> P NP | P PROacc
% Grammar 2: PP -> P NP
pp_rule rule
(pp,obj2:(head:(case:acc)))
===>
cat> p,
cat> (np,head:(case:acc)).

% Grammar 1: NP -> Npl PP
% Grammar 2: NP -> N PP
np_rule rule
(np,head:(number:plural))
===>
cat> (noun,number:plural),
cat> pp.

% Grammar 1: NP -> Det Nsg | Det Npl
% Grammar 2: NP -> Det N
np_rule rule
(np,head:noun)
===>
cat> det,
cat> noun.

% Grammar 1: NP -> Det Nsg PP | Det Npl PP
% Grammar 2: NP -> Det N PP
np_rule rule
(np,head:noun)
===>
cat> det,
cat> noun,
cat> pp.

% Grammar 1: NP -> Npl | PROnom | PROacc
% Grammar 2: NP -> N
np_rule rule
(np,head:(number:plural)) % should receive a var Case from srule
===>
cat> (noun, number:plural). % this rule allows it to accept she, which is a problem

np_rule rule
(np,head:(case:Case))
===>
cat> (pronoun, case:Case).
