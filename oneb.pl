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
index_np sub [] intro [c:case,t:type].
    case sub [nom, acc]. % nominative, accusative
        nom sub [].
        acc sub [].
    type sub [common, pronoun]. % common noun, pronoun
        common sub [].
        pronoun sub [].

% declare features for n
index_n sub [] intro [n:number].
    number sub [sing, plural]. % singular, plural
        sing sub [].
        plural sub [].

% now, how to incorporate np features?

% declare the parts of speech
cat sub [s,np,vp,pp,p,det,v].
    s sub [].
    noun sub [] intro [index:index]. % declare noun with index var
    np sub [] intro [head:noun]. % noun phrase with head as noun [head is used to pass down index var to other rules]
    vp sub [] intro [obj:np]. % verb phrase with subject as np [subj is used to pass down index var to other rules]
    pp sub [].
    p sub [].

det sub [].
v sub [].

% specify their grammar features
she ---> (noun, index:(c:nom,t:pronoun)). %n.
fed ---> v. %(v, obj:(head:(index:(c:acc)))). %v.
the ---> det.
dog ---> (noun, index:(c:nom,n:sing,t:common)). %n.
dog ---> (noun, index:(c:acc,n:sing,t:common)). %n.
puppies ---> (noun, index:(c:nom,n:plural,t:common)). %n.
puppies ---> (noun, index:(c:acc,n:plural,t:common)). %n.
him ---> (noun, index:(c:acc,t:pronoun)). %n.
with ---> p.

% augment Grammar 2 with features so as to restrict it to the language of Grammar 1

% Grammar 1: S -> NPnom VP
% Grammar 2: S -> NP VP
srule rule
s
===>
cat> (np,head:(index:(c:nom))), % restricts to only allowing nominative
cat> (vp,obj:(head:(index:(c:acc)))).

% Grammar 1: VP -> V NPacc
% Grammar 2: VP -> V NP
vp_rule rule
(vp,obj:(head:(index:(c:acc))))
===>
cat> v,
cat> (np,head:(index:(c:acc))).

% Grammar 1: PP -> P NPacc
% Grammar 2: PP -> P NP
pp_rule rule
pp
===>
cat> p,
cat> np.

% Grammar 1: NP -> Nsg PP | Npl PP
% Grammar 2: NP -> N PP
np_rule rule
(np,head:(index:(n:plural; t:pronoun)))
===>
cat> (noun,index:(n:plural; t:pronoun)),
cat> pp.

% Grammar 1: NP -> Det Nsg | Det Npl
% Grammar 2: NP -> Det N
np_rule rule
(np,head:(index:(t:common))) % should accept plural as well
===>
cat> det,
cat> (noun,index:(t:common)).

% Grammar 1: NP -> Det Nsg PP | Det Npl PP
% Grammar 2: NP -> Det N PP
np_rule rule
(np,head:(index:(t:common)))
===>
cat> det,
cat> (noun,index:(t:common)),
cat> pp.

% Grammar 1: NP -> Nsg | Npl
% Grammar 2: NP -> N
np_rule rule
(np,head:(index:(n:plural; t:pronoun)))
===>
cat> (noun,index:(n:plural; t:pronoun)). % this rule allows it to accept she, which is a problem
