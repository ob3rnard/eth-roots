#!/usr/bin/env sage

# Code in support of arXiv:2305.17425 [math.NT]
# Copyright 2023, Olivier Bernard, Andrea Lesavourey
# GPL-3.0-only (see LICENSE file)

import sys
TWSTI_PATH="../Tw-Sti/"; 
sys.path.append(TWSTI_PATH + "src/");

from sage import *
load("../src/cf_roots.sage")

from pcmp_io import *
from nf import *
from cyclotomics import *
from circular import *
from stim_q import *
from saturation import *

proof.number_field(False);
proof.arithmetic(False);

# necessary for finite fields embeddings
from sage.rings.finite_rings.hom_finite_field import FiniteFieldHomomorphism_generic

set_random_seed(123457)

# ------------------------------------------------------------------------------
# Pari stack size for computing Cl_K+
pari.allocatemem(1.2*10^10); # Avoid "out of memory" when using Pari on the laptop

# ------------------------------------------------------------------------------
# which prime e to pick : min or max factor of gcd(m, h_m^-)
if len(sys.argv) == 1:
    type_prime="min"            # which e | gcd(m, h_m^-) : min or max
    size_primes=60              # size of primes taken in couv. method
elif len(sys.argv) == 2:
    type_prime=sys.argv[1]
    size_primes=60
elif len(sys.argv) == 3:
    type_prime=sys.argv[1]
    size_primes=ZZ(sys.argv[2])


# data file
str_file = '../data/cf_tw_sti_saturation_bad_' + type_prime + '_' + str(size_primes) + '_nfroots'

d = 2; # d = number of orbits 

for m in range(7, 400):

    if mod(m, 4)==2 or euler_phi(m) > 212 or cf_hplus(m)>1:
        continue

    print("_______________     Conductor is ", m, "     _______________")
    n  = euler_phi(m);
    K  = CyclotomicField(m);
    #hK = K.class_number();
    hm = cf_hminus(m); hK = hm;
    g = gcd(m,hK);
    if (g == 1):
        continue
    else:
        fg = g.factor()
        if type_prime=='min':
            ep = ZZ(fg[0][0])
        elif type_prime=='max':
            ep = ZZ(fg[-1][0])
        else:
            raise ValueError('type_prime should be min or max')
    if ep == 2:
        continue

    print("Non trivial factor / exponent found: ", ep)

    f = open(str_file, 'a')
    f.write(str(m) + "\t" + str(n) + "\t" + str(ep) + "\t")
    f.close()
    
    # computation of orbits for saturation
    Lp = cf_d_first_split_primes(K,d=d);
    L  = cf_d_orbits(K,d=d); L1 = L[:n]; L2 = L[n:]; 
    id_p = [ L[_d*n] for _d in range(d) ]; assert(len(id_p) == d);

    # -------------------------------------------------------------------------
    # then computation of the plain subgroup of S-units named URS as in ASIACRYPT'22 paper [Ber+22]
    # Read them from file instead ?
    urs_f = "../Tw-Sti/data/z{}/z{}_d{}.urs".format(m,m,d);
    if (os.path.exists(urs_f)):
        print("Reading S-units 'urs' from '{}'".format(urs_f));
        (yu_all, ysu_all), B_all, Vp_all = sunits_raw_read_data(urs_f, K);
        Uw = cf_cyclotomic_units(K);
        Rw = sum( (B_all[len(Uw)+_d*n:      len(Uw)+_d*n+n//2] for _d in range(d)), []);
        Sw = sum( (B_all[len(Uw)+_d*n+n//2: len(Uw)+(_d+1)*n]  for _d in range(d)), []);
        urs_valp = matrix(ZZ, sum( ( Vp_all[len(Uw)+_d*n: len(Uw)+_d*n+n//2] for _d in range(d)), [])
                          + sum( ( Vp_all[len(Uw)+_d*n+n//2: len(Uw)+(_d+1)*n] for _d in range(d)), []));
    else:
        Uw = cf_cyclotomic_units(K);
        Rw = sum( (real_gens(K,_p) for _p in Lp), []);
        Sw = sum( (sti_gens_alpha(K,_id_p)[1:] for _id_p in id_p), []);
        urs_valp = Matrix(ZZ,[[ _s.valuation(_id_p) for _id_p in L] for _s in Rw+Sw]);

    urs = Uw + Rw + Sw;
    print("S-units 'urs' ok", flush=True);
    assert(len(urs) == d*n + n//2 - 1);
    print("Valuations computed", flush=True);
    assert(urs_valp.is_square());
    assert(urs_valp.determinant().abs() ==
           2^(d*(n//2-1+(0 if ZZ(m).is_prime_power() else 2**(len(ZZ(m).factor())-2)-1))) * hm^(d-1) * hK);
    # ------------------------------------------------------------------------
    
    # Find a e-th root (bad case).
    er = ep

    # sauf erreur on n'a pas besoin de la torsion ssi gcd(e,n) = 1
    ##### Quand inclure la torsion ?? For (m,e)=(37,37) not needed, for (m,e)=(76,19) needed, idem for (69,23)
    ##### For (m,e) = (96,9): not needed.
    if (gcd(er,m)>1 and gcd(er,m)<m):
        print("gcd(er,m) = {} --> adding torsion units".format(gcd(er,m)));
        urs = [-K.gen()] + urs;
    print("Computing e-th root for e={}".format(er));

    # -------------------------------------------------------------------------
    # computation of characters and kernel to detect non trivial power

    print("Characters = 1[{}]".format(lcm(m,er)), flush=True);
    chi_e = sat_get_suitable_chip(urs, d=lcm(m,er), smooth_V=Lp[-1], __per_orbit=1, __overhead=10); # Returns list of pid
    # nb: overkill, we should reuse the matrix of valuations as free additional characters (as was done for e=2)
    
    
    t=cputime(); chi_B = matrix(IntegerModRing(er), [[log_chip_dth_power(_chi,_su,d=er) for _chi in chi_e] for _su in urs ]); t=cputime(t);
    print("Calcul characters: {:.2f}s".format(t));
    # En fait, il semble que la partie U+R n'est pas impliquée. En un sens c'est logique mais ça pose d'autres questions.
    if (er.is_prime()):
        H     = matrix(ZZ, matrix(GF(er),chi_B.left_kernel().basis_matrix())); # map in -e/2,e/2 ? quotients relous
    else:
        assert(er.is_prime_power());
        ###### Pb for detecting e^k !! No echelon_form algorithm mod non prime integers
        ###### See https://ask.sagemath.org/question/44815/finding-the-kernel-of-a-matrix-in-a-non-integral-domain/
        ###### --> For ZZ/e^kZZ:
        ######     - Write each coeff as polynomial in GF(e)[t]/<t^k> 
        ######     - Write an unknown vector of kernel as poly in GF(e)[t]/<t^k> (so k*dim indeterminates)
        ######     - Write the v.M product to obtain dim equations (poly deg k = 0)
        ######     - "Weil descent" to obtain a linear system over GF(e).
        print("Ooops! TODO: find kernel of matrix over {}".format(er));
        # Suggestion
        # Zerk = IntegerModRing(ep**k);
        # Fe = GF(ep);
        #    mult_tk = [ block_matrix(Fe, [[column_matrix(_k, k-_k), identity_matrix(k-_k)], [zero_matrix(_k,k)]], subdivide=False)
        #                for _k in range(k) ]; # Multiplication matrices by t^_k in GF(e)[t]/<t^k>
        
        # Try https://ask.sagemath.org/question/33890/how-to-find-kernel-of-a-matrix-in-mathbbzn/
        # Zi   = ZZ^(chi_B.nrows()); Zie = Zi/(er*Zi);
        # Zo   = ZZ^(chi_B.ncols()); Zoe = Zo/(er*Zo);
        # t = cputime(); Zermap = Zie.hom([ Zoe(_v) for _v in chi_B]); t = cputime(t);
        # print("construct Map on Z/{}Z: {:.2f}".format(er,t));
        # t=cputime(); H    = matrix(ZZ, [vector(ZZ, Zie(_v)) for _v in Zermap.kernel().gens()]); t = cputime(t);
        # print("Find kernel on Z/{}Z: {:.2f}".format(er,t));
        
        # Use Howell normal form (thx JP FLori) and matkermod() fct in Pari
        H     = matrix(ZZ, pari(matrix(ZZ,chi_B).transpose()).matkermod(er)).transpose(); # map in -e/2,e/2 ? quotients relous
        # print(H);
    
    print("Rang noyau: {}".format(H.rank()));

    # ------------------------------------------------------------------------

    phi = get_inf_places(K,5000);
    lurs = [ logarg_set(_u, phi) for _u in urs ];
    se   = [ logarg_mpow(lurs, _H) for _H in H.rows() ];

    print("[]-norm se: {:.2f}".format(logarg_lnSnorm_cf(se[0])));
    s    = [ logarg_pow(_s, 1/er) for _s in se ];
    print("[]-norm s:  {:.2f}".format(logarg_lnSnorm_cf(s[0])));

    # Quick-and-dirty thing that fits well with real measurements above
    Be = max([ sum(H[i][j]* log(vector(ComplexField(300), urs[j].complex_embeddings(prec=300)).norm(infinity),2)
                   for j in range(len(urs))) for i in range(H.nrows())]);
    print("log h(s^e) = {:.2f}".format(Be));

    B  = Be / er;
    print("log h(s) = {:.2f}".format(B));
    B = 2**B;


    red_fct = lll_ZZ;
    # red_fct = lambda M: bkz_ZZ(M, block_size=40);

    # ------------------- Tests methods : nfroots from pari/gp  ----------------
    s_pari=[];
    t_pari = 0;
    for i in range(H.nrows()):
        print("Sol {}".format(i));

        print("using nfroots")
        # global X, Y
        Zxy = PolynomialRing(QQ, 2, 'x, y');
        # Zy = PolynomialRing(ZZ, name='y');
        t = cputime()
        C = prod([urs[j]^H[i][j] for j in range(len(urs))])
        pol = pari.polcyclo(m, 'y')
        eq = x^er - Zxy(C.polynomial('y'))
        res = pari.nfroots(pol, eq)
        print("found a sol with pari?: ", len(res))
        res = K(pari.liftall(res[0])); t = cputime(t);
        t_pari += t;
        
        print("\tTime Root: {:.4f}s".format(t));
        s_pari.append(res);
        # Check
        ls_pari = logarg_set(s_pari[-1], phi);
        print("\tPari/Gp nfroots: Check log, arg mod 2pi/e: \x1b[{}OK\x1b[0m"
              .format("32m" if logarg_is_equal(ls_pari,s[i],argmod=er) else "31mN"));
        # The assert are here to quantify how far are the values for diagnostic
        assert(fp.fp_assert_equal("", ls_pari.inf, s[i].inf, target=1000));
        assert(fp.fp_assert_zero("", [min(_th.abs(), 1-_th.abs()) for _th in logarg_reduce_args(er*ls_pari.args) - logarg_reduce_args(er*s[i].args)], target=1000));

    t_pari = "%.2f" % t_pari
    f = open(str_file, 'a')
    f.write(str(H.nrows()) + "\t" + t_pari + "\n")
    f.close()

