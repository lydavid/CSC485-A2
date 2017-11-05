% David Ly, lydavid1, 1001435501

% declare the features
index sub [] intro [c:case, n:number, t:type].
    case sub [nom, acc]. % nominative, accusative
        nom sub [].
        acc sub [].
    number sub [sing, plural]. % singular, plural
        sing sub [].
        plural sub [].
    type sub [common, pronoun]. % common noun, pronoun
        common sub [].
        pronoun sub [].

% declare the parts of speech
cat sub [s,np,vp,pp,p,det].
    s sub [].
    noun sub [] intro [index:index]. % declare noun with index var
    np sub [] intro [head:noun]. % noun phrase with head as noun [head is used to pass down index var to other rules]
    vp sub [] intro [subj:np, obj:np]. % verb phrase with subject as np [subj is used to pass down index var to other rules]
    pp sub [].
    p sub [].

det sub [].

% specify their grammar features
she ---> (noun, index:(c:nom)). %n.
fed ---> (vp, obj:(head:(index:(c:acc)))). %v.
the ---> det.
dog ---> (noun, index:(c:nom,n:sing)). %n.
dog ---> (noun, index:(c:acc,n:sing)). %n.
puppies ---> (noun, index:(c:nom,n:plural)). %n.
puppies ---> (noun, index:(c:acc,n:plural)). %n.
him ---> (noun, index:(c:acc)). %n.
with ---> p.

% augment Grammar 2 with features so as to restrict it to the language of Grammar 1
% do not change the grammar below
% actually, will have to change the specification
% but we won't be adding/removing any of these below, only modifying

% S -> NP VP
srule rule
s
===>
cat> (np,head:(index:(c:nom))), % restricts to only allowing nominative
cat> (vp,subj:(head:(index:Index)),obj:(head:(index:Index))).

% VP -> V NP
vp_rule rule
vp
cat> v,
cat> np.

% PP -> P NP
pp_rule rule
pp
cat> p,
cat> np.

% NP -> N
np_rule rule
(np,head:(index:Index))
===>
cat> (noun,index:Index).

% NP -> Det N
np_rule rule
(np,head:(index:Index))
cat> det,
cat> (noun,index:Index).

% NP -> Det N PP
np_rule rule
(np,head:(index:Index))
cat> det,
cat> (noun,index:Index),
cat> pp.

% NP -> N PP
np_rule rule
(np,head:(index:Index))
cat> (noun,index:Index),
cat> pp.
