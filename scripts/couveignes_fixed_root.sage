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
print(len(sys.argv))
p  = ZZ(sys.argv[1]);
nb_tests = ZZ(sys.argv[2]);
if len(sys.argv) == 3:
    method = 'pari'
else:
    method = sys.argv[3]

    
# --------------------------------------------------------------------------

def myprint(*args,**kwargs):
    print(*args,**kwargs,flush=True)



### couveignes generalisation in *cyclotomic fields*
### NOT IN COMPACT FORM, + method thing
def cf_couveignes_raw(B, e, L, K, m, method='pari'):
    r"""
    Computes B^(1/e) in OL where B = prod U[i] ^ Exps[i]
    
    Input:
    - 'U': number field elements; belongs to L
    - 'Exps': list of integers; prod U[i]^Exps[i] is of the form A^e
    - 'e': integer; e is the exponent
    - 'L': number field; field where we want to retrieve a e-th root of B
    - 'K': number field; subfield of L verifying good properties
    ( gcd([L:K], e) == 1, zeta_e belongs to K)
    """
    Zx.<X> = PolynomialRing(ZZ);
    
    my_t = cputime()
    
    print("time taken for technical stuff is: ", cputime(my_t))
    nL = L.degree()
    zL = L.gen()

    ze = zL^(m[1]/e)

    nK = K.degree()
    nLK = ZZ(nL / nK)
    my_t = cputime()

    Re = RealField(300);
    bound_basis = max([abs(log(vector(Re,_u).norm(2), 2)) for _u in [B]])
    bound_norm = round(2**(bound_basis*nLK)/2 * sqrt(nL)*nLK/2)
    NA = cf_relative_norms([B], L, K)[0]
    
    time_norm = cputime(my_t)
    print("time taken for relative norm is: ", time_norm)

    my_t = cputime()
    if method=='pari':
        pol = pari.polcyclo(m[0], 'y')
        eq = x^e - NA.polynomial('y')
        NA = K(pari.liftall(pari.nfroots(pol, eq)[0]))
    else:
        NA = cf_padic_lifting([NA], [ZZ(1)], ZZ(e), ceil(RR(bound_norm).nth_root(e)))

    time_root_norm = cputime(my_t)
    print("time taken for root in subfield is: ", time_root_norm)
    
    A_crt = [];
    bound = bound_basis; # (log(max([abs(_b) for _b in B]), 2))
    bound = 2^(1.5*(bound/e).round());

    crt_p = [];
    crt_Ip = [];
    crt_Jp = [];
    crt_Ap = [];
    p = randint(2^20, 2^21);
    p = p - p%mK + 1
    prod_crt_p = 1;

    my_t = cputime();
    while prod_crt_p < bound:
        p, Ip, Jp = cf_couveignes_good_prime(L, K, m, next=p,e=e);
        prod_crt_p *= p;
        crt_p += [p];
        crt_Ip += [Ip];
        crt_Jp += [Jp];
    # print("time taken for computation of primes is:", cputime(my_t));

    for i in range(len(crt_p)):
        # print("prime is: ", crt_p[i]);
        my_t = cputime();
        crt_Ap += [cf_couveignes_mod_p([B], [ZZ(1)], e, NA, L, K, m, crt_p[i],
                                       [crt_Ip[i], crt_Jp[i]])];
        # print("time taken for couveignes_mod_p is:", cputime(my_t));
        # print("******************************");
    print("everything is done")
    crt_Ap = [Zx(_ap) for _ap in crt_Ap];
    my_t = cputime();
    A_big = CRT(crt_Ap, crt_p) if len(crt_p)>1 else crt_Ap[0];
    print("time taken for CRT is:", cputime(my_t));
    A = L([(_a if _a < prod_crt_p/2. else _a - prod_crt_p) for _a in A_big]);
    return A, time_norm, time_root_norm;



### experiment on a random element

sol_sizes = [10, 50, 100]

str_file = '../data/couveignes_fixed_root_' + str(p) + '_' + method

e = p

for q in range(3, 300):
    if (q % p ==0) or (euler_phi(q)%e == 0) or (not is_prime_power(q)):
        continue
    if q%4 == 0:
        continue
    
    mL = p*q;
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
    Times_couv = [0 for _i in range(len(sol_sizes))]
    Times_norm = [0 for _i in range(len(sol_sizes))]
    Times_root_norm = [0 for _i in range(len(sol_sizes))] 


    for j in range(len(sol_sizes)):
        
        sol_size = sol_sizes[j]
        myprint("___ Size of solution is: ", sol_size,  " ___" );
        
        time_couv = 0;
        time_norm = 0;
        time_root_norm = 0;
        
        for i in range(nb_tests):

            myprint("Test nb ", i+1,  " over ", nb_tests);
            
            # compute random e-power
            A = L.random_element(2^sol_size, integral_coefficients=True)
            
            B = A^e;

            _time_couv = cputime()

            # print("time taken before start of computation is: ", cputime(my_time))
            A1, t_norm, t_root_norm = cf_couveignes_raw(B, e, L, K, m, method)
            time_couv += cputime(_time_couv)
            time_norm += t_norm
            time_root_norm += t_root_norm
            # assert(A1^e==B)


            
        Times_couv[j] = 1.*time_couv / nb_tests;
        Times_norm[j] =  1.*time_norm / nb_tests;
        Times_root_norm[j] =  1.*time_root_norm / nb_tests;


    myprint("Average timing are: ", Times_couv)


    Times_couv = ["%.2f" % v for v in Times_couv]
    Times_norm = ["%.2f" % v for v in Times_norm]
    Times_root_norm = ["%.2f" % v for v in Times_root_norm]


    
    f = open(str_file, 'a')
    for _t in Times_norm:
        f.write(" " + str(_t) + "\t")
    for _t in Times_root_norm:
        f.write(" " + str(_t) + "\t")
    for _t in Times_couv:
        f.write(" " + str(_t) + "\t")
    f.write("\n")
    f.close()

        
###
