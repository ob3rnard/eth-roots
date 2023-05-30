#!/usr/bin/env sage

# Code in support of arXiv:2305.17425 [math.NT]
# Copyright 2023, Andrea Lesavourey
# GPL-3.0-only (see LICENSE file)

import sys
TWSTI_PATH="../Tw-Sti/"; 
sys.path.append(TWSTI_PATH + "src/");

from sage import *
load("../src/cf_roots.sage");

proof.number_field(False);
proof.arithmetic(False);

set_random_seed(12345)
Zx.<X> = PolynomialRing(ZZ);


# necessary for finite fields embeddings
from sage.rings.finite_rings.hom_finite_field import FiniteFieldHomomorphism_generic


# Pari stack size for computing Cl_K+
pari.allocatemem(10^10); # Avoid "out of memory" when using Pari on the laptop


p = ZZ(sys.argv[1]);
nb_tests = ZZ(sys.argv[2]);

# ----------------------------------------------------------------------------

def myprint(*args,**kwargs):
    print(*args,**kwargs,flush=True)


### experiment on a random element -- nfroots version

sol_sizes = [10, 50, 100]

str_file = '../data/crt_' + str(p) + '_nfroots'


for m in range(5, 300):
    if m%p==0 or (2==mod(m,4)):
        continue
    mL = m;
    myprint("************ Conductor is ", mL,  " *************" );
    e = p;
    L.<zm> = CyclotomicField(mL);
    nL = L.degree();
    f = open(str_file, 'a')
    f.write(str(mL) + "\t" + str(nL) + "\t")
    f.close()

    Times_gp = [0 for _i in range(len(sol_sizes))]

    for j in range(len(sol_sizes)):

        sol_size = sol_sizes[j]

        myprint("___ Size of solution is: ", sol_size,  " ___" );
        
        time_crt = 0;
        time_gp = 0;
        
        for i in range(nb_tests):
            
            myprint("Test nb ", i+1,  " over ", nb_tests);

            # compute random e-power
            A = L.random_element(2^sol_size, integral_coefficients=True)
            B = A^e;
                        
            # pari/gp nfroots function
            _time_gp = cputime()
            pol = pari.polcyclo(mL, 'y')
            eq = x^e - B.polynomial('y')
            A1 = pari.nfroots(pol, eq)
            time_gp += cputime(_time_gp)
            
        Times_gp[j] = 1.*time_gp / nb_tests;
    
    print("Average timings are: ", Times_gp, flush=True)

    Times_gp = ["%.2f" % v for v in Times_gp]
        
    f = open(str_file, 'a')
    for _t in Times_gp:
        f.write(" " + str(_t) + "\t")
    f.write("\n")
    f.close()

###
