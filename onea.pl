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


she ---> pro_nom.
fed ---> v.
the ---> det.
dog ---> nsg.
puppies ---> npl.
him ---> pro_acc.
with ---> p.

srule rule
s
===>
cat> np_nom,
cat> vp. 

vp
===>
cat> v,
cat> np_acc.

pp
===>
cat> p,
cat> np_acc.

np_nom
===>
cat> np.

np_nom
===>
cat> pro_nom.

np_acc
===>
cat> np.

np_acc
===>
cat> pro_acc.

np
===>
cat> det,
cat> n.

np
===>
cat> det,
cat> n,
cat> pp.

np
===>
cat> npl.

np
===>
cat> npl,
cat> pp.

n
===>
cat> nsg.

n
===>
cat> npl.
