% David Ly, lydavid1, 1001435501

% Declare types
bot sub [s,np,vp,pp,
        np_nom,np_acc,
        nsg,npl,pro_nom,pro_acc,
        n,det,v,p].
    s sub [].
    np sub [].
    vp sub [].
    pp sub [].

    np_nom sub [].
    np_acc sub [].

    nsg sub [].
    npl sub [].
    pro_nom sub [].
    pro_acc sub [].

    n sub [].
    det sub [].
    v sub [].
    p sub [].

% Lexicon
she ---> pro_nom.
fed ---> v.
the ---> det.
dog ---> nsg.
puppies ---> npl.
him ---> pro_acc.
with ---> p.

% Grammar Rules
srule rule
s
===>
cat> np_nom,
cat> vp.

vp_rule rule
vp
===>
cat> v,
cat> np_acc.

pp_rule rule
pp
===>
cat> p,
cat> np_acc.

np_nom_rule rule
np_nom
===>
cat> np.

np_nom_rule rule
np_nom
===>
cat> pro_nom.

np_acc_rule rule
np_acc
===>
cat> np.

np_acc_rule rule
np_acc
===>
cat> pro_acc.

np_rule rule
np
===>
cat> det,
cat> n.

np_rule rule
np
===>
cat> det,
cat> n,
cat> pp.

np_rule rule
np
===>
cat> npl.

np_rule rule
np
===>
cat> npl,
cat> pp.

n_rule rule
n
===>
cat> nsg.

n_rule rule
n
===>
cat> npl.
