% David Ly, lydavid1, 1001435501

bot sub [s,np,vp,pp,np_nom,np_acc,n,det,nsg,npl,pro_nom,pro_acc,v,p].


s sub [].  
np sub [].
vp sub [].
pp sub [].
np_nom sub [].
np_acc sub [].
n sub [].
det sub [].
nsg sub [].
npl sub [].
pro_nom sub [].
pro_acc sub [].
v sub [].

% specify their grammar features
she ---> n.
fed ---> v.
the ---> det.
dog ---> n.
puppies ---> n.
him ---> n.
with ---> p.

% augment Grammar 2 with features so as to restrict it to the language of Grammar 1
% do not change the grammar below
% actually, will have to change the specification
% but we won't be adding/removing any of these below, only modifying

% S -> NP VP
srule rule
s
===>
cat> np,
cat> vp. 

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
np
cat> n.

% NP -> Det N
np_rule rule
np
cat> det,
cat> n.

% NP -> Det N PP
np_rule rule
np
cat> det,
cat> n,
cat> pp.

% NP -> N PP
np_rule rule
np
cat> n,
cat> pp.
