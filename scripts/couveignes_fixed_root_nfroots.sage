#!/usr/bin/env sage

# Code in support of arXiv:xxxx.xxxxx [pp.sss]
# Copyright 2023, Andrea Lesavourey
# GPL-3.0-only (see LICENSE file)

sys.path.append("../Tw-Sti/src/");

import sys
from nf import *
from cyclotomics import *

load("../src/cf_roots.sage");

proof.number_field(False);
proof.arithmetic(False);

# necessary for finite fields embeddings
from sage.rings.finite_rings.hom_finite_field import FiniteFieldHomomorphism_generic

set_random_seed(12345)

# Pari stack size for computing Cl_K+
pari.allocatemem(10^10); # Avoid "out of memory" when using Pari on the laptop
p  = ZZ(sys.argv[1]);
nb_tests = ZZ(sys.argv[2]);
    
# --------------------------------------------------------------------------

def myprint(*args,**kwargs):
    print(*args,**kwargs,flush=True)
    
### experiment on a random element


sol_sizes = [10, 50, 100]

str_file = '../data/couveignes_fixed_root_' + str(p) + '_nfroots'

e = p

for q in range(3, 300):
    if (q % p ==0) or (euler_phi(q)%e == 0) or (not is_prime_power(q)):
        continue
    if q%4 == 0:
        continue

    
    mL = p*q;

    if euler_phi(mL) > 300:
        continue

    myprint("************ Relative conductor is ", q,  " *************" );
    L.<zm> = CyclotomicField(mL);
    nL = L.degree();
    f = open(str_file, 'a')
    f.write(str(mL) + "\t" + str(nL) + "\t")
    f.close()
    
    K.<ze> = CyclotomicField(e);
    mK = cf_get_conductor(K);
    nK = K.degree();

    mLK = mL / mK

    m = [mK, mL]
    Times_gp = [0 for _i in range(len(sol_sizes))]

    for j in range(len(sol_sizes)):
        
        sol_size = sol_sizes[j]
        myprint("___ Size of solution is: ", sol_size,  " ___" );
        
        time_gp = 0;
        
        for i in range(nb_tests):

            myprint("Test nb ", i+1,  " over ", nb_tests);
            
            # compute random e-power
            A = L.random_element(2^sol_size, integral_coefficients=True)
            
            B = A^e;

            _time_gp = cputime()
            pol = pari.polcyclo(mL, 'y')
            eq = x^e - B.polynomial('y')
            A1 = pari.nfroots(pol, eq)
            time_gp += cputime(_time_gp)

            
        Times_gp[j] = 1.*time_gp / nb_tests;

    myprint("Average timings are: ", Times_gp)

    Times_gp = ["%.2f" % v for v in Times_gp]
    
    f = open(str_file, 'a')
    for _t in Times_gp:
        f.write(" " + str(_t) + "\t")
    f.write("\n")
    f.close()

        
###
