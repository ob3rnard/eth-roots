#!/usr/bin/env sage

# Code in support of arXiv:xxxx.xxxxx [pp.sss]
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

set_random_seed(12345)

# ------------------------------------------------------------------------------
# Pari stack size for computing Cl_K+
pari.allocatemem(1.2*10^10); # Avoid "out of memory" when using Pari on the laptop

# ------------------------------------------------------------------------------
# which prime e to pick : min or max factor of gcd(m, h_m^-)
if len(sys.argv) == 1:
    type_prime = "min"            # which e | h_m^- : min or max
    exp_range = 14                # max bit-size for exponent to consider
elif len(sys.argv) == 2:
    type_prime = sys.argv[1]
    exp_range = 14
elif len(sys.argv) == 3:
    type_prime = sys.argv[1]
    exp_range = ZZ(sys.argv[2])

if type_prime == 'MAX':
    exp_min = exp_range;
    exp_max = infinity;
else:
    exp_min = max(1, exp_range-10);
    exp_max = exp_range;

# data file
str_file = '../data/cf_tw_sti_saturation_good_' + type_prime + '_' + str(exp_range)

d = 2; # d = number of orbits 

nb_cand=0;
for m in range(7, 1000):
    if mod(m, 4)==2 or euler_phi(m) > 210 or cf_hplus(m)>1:
        continue

    print("_______   Conductor is ", m, "   _______")
    n  = euler_phi(m);
    K  = CyclotomicField(m);
    #hK = K.class_number();
    hm = cf_hminus(m); hK = hm;
    g = gcd(m,hK);
    if (hK == 1):
        continue
    else:
        fK = hK.factor()
        fK = [_fk for _fk in fK if (exp_min < log(_fk[0], 2) < exp_max) and (m%_fk[0]!=0)]
    if len(fK)==0:
        continue
    else:
        if type_prime=='max' or type_prime=='MAX':   # max e | hm^- and m%e =/= 0
            ep = ZZ(fK[-1][0])
        elif type_prime=='min': # min e | hm^- and m%e =/= 0
            ep = ZZ(fK[0][0])
    if (ep == 2) or (m%ep==0):
        continue
    
    print("Non trivial factor / exponent found: ", ep, " (log_2=", RR(log(ep,2)), ")")
    nb_cand += 1;
    
    f = open(str_file, 'a')
    f.write(str(m) + "\t" + str(n) + "\t" + str(ep) + "\t")
    f.close()


    # computation of orbits for saturation
    Lp = cf_d_first_split_primes(K,d=d);
    L  = cf_d_orbits(K,d=d); L1 = L[:n]; L2 = L[n:]; 
    id_p = [ L[_d*n] for _d in range(d) ]; assert(len(id_p) == d);

    # --------------------------------------------------------------------------
    # then compute/read URS

    # Read them from file instead ?
    urs_f = TWSTI_PATH + "data/z{}/z{}_d{}.urs".format(m,m,d);
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
        Rw = sum( (real_gens(K,_p) for _p in Lp), []); # Could be very long
        Sw = sum( (sti_gens_alpha(K,_id_p)[1:] for _id_p in id_p), []);
        urs_valp = Matrix(ZZ,[[ _s.valuation(_id_p) for _id_p in L] for _s in Rw+Sw]);

    urs = Uw + Rw + Sw;
    print("S-units 'urs' ok", flush=True);
    assert(len(urs) == d*n + n//2 - 1);
    print("Valuations computed", flush=True);
    assert(urs_valp.is_square());
    assert(urs_valp.determinant().abs() ==
           2^(d*(n//2-1+(0 if ZZ(m).is_prime_power() else 2**(len(ZZ(m).factor())-2)-1))) * hm^(d-1) * hK);

    # --------------------------------------------------------------------------
    # Find a e-th root.
    er = ep
    if (gcd(er,m)>1 and gcd(er,m)<m):
        print("gcd(er,m) = {} --> adding torsion units".format(gcd(er,m)));
        urs = [-K.gen()] + urs;
    print("Computing e-th root for e={}".format(er));


    # -------------------------------------------------------------------------
    # computation of characters and kernel to detect non trivial power
    
    # Use Schirokauer maps ?
    if (not (ep**2).divides(hK)) and (ep > 2**10) : # comment this line and uncomment the next if there is some bug : Schirokauer maps can give elements which are not eth powers.
    # if False:
        print("Using Schirokauer maps", flush=True);
        # Schirokauer maps for detecting powers when e is a big prime, e^2 \not| hK
        Zey.<y> = PolynomialRing(IntegerModRing(er**2));
        Zx.<x>  = PolynomialRing(ZZ);
        shiro_exp = mod(er, m).multiplicative_order();

        def shiro(g):
            gy = Zey(g.polynomial());
            Ky = Zey(K.defining_polynomial());
            # shiro_pol = power_mod(gy, SExp, Ky);
            # Compute gy^(e^ord) ---> pedestrian version looks (slightly) faster (?)
            shiro_pol = gy;
            for _k in range(shiro_exp):
                shiro_pol = power_mod(shiro_pol, er, Ky);
                # Here g^(e^(k+1))
            # Actually we want gy^(e^ord - 1)
            shiro_pol = (shiro_pol * Zey((1/g).polynomial())).mod(Ky);
            shiro_map = K(Zx(Zx(shiro_pol-1) / er));
            return list(shiro_map);

        t=cputime();
        chi_B = block_matrix(IntegerModRing(er), [[ block_matrix([[zero_matrix(len(urs)-urs_valp.nrows(),urs_valp.ncols())],[urs_valp]], subdivide=False),
                                                    matrix([shiro(_su) for _su in urs ]) ]], subdivide=False);
        t=cputime(t);
    else:
        print("Characters = 1[{}]".format(lcm(m,er)), flush=True);
        chi_e = sat_get_suitable_chip(urs, d=lcm(m,er), smooth_V=Lp[-1], __per_orbit=1, __overhead=10); # Returns list of pid
        # nb: overkill, we should reuse the matrix of valuations as free additional characters (as was done for e=2)

        t=cputime(); chi_B = matrix(IntegerModRing(er), [[log_chip_dth_power(_chi,_su,d=er) for _chi in chi_e] for _su in urs ]); t=cputime(t);
        
    print("Calcul characters: {:.2f}s".format(t));
    t_shiro = t;
    if (er.is_prime()):
        H     = matrix(ZZ, matrix(GF(er),chi_B).left_kernel().basis_matrix());
    else:
        assert(er.is_prime_power());
        # Pb for detecting e^k !! No echelon_form algorithm mod non prime integers
        # Use Howell normal form (thanks J-P Flori) and matkermod() fct in Pari
        H     = matrix(ZZ, pari(matrix(ZZ,chi_B).transpose()).matkermod(er)).transpose(); 
            
    print("Rang noyau: {}".format(H.rank()),flush=True);

    
    # ------------------------------------------------------------------------
    # Essentially, have these for checking the result is not "dumb".
    phi = get_inf_places(K,10000); print("Inf places ok", flush=True); # 5000 is usually -- but not always -- sufficient
    lurs = [ logarg_set(_u, phi) for _u in urs ]; print("Compute lurs", flush=True);
    se   = [ logarg_mpow(lurs, _H) for _H in H.rows() ]; print("Compute log se", flush=True);

    print("[]-norm se: {:.2f}".format(logarg_lnSnorm_cf(se[0])), flush=True);
    s    = [ logarg_pow(_s, 1/er) for _s in se ];
    print("[]-norm s:  {:.2f}".format(logarg_lnSnorm_cf(s[0])), flush=True);

    
    # ----------------------- Tests methods : our rec method -------------------
    s_root=[];
    t_root = 0;
    for i in range(H.nrows()):
        print("Sol {}".format(i));

        t = cputime(); res, _ = cf_roots_rec(urs, H[i], ZZ(er), K, m, 58); t = cputime(t); 
        t_root += t;
        print("\tTime Root: {:.4f}s".format(t));
        s_root.append(res);

        # Check
        ls_root = logarg_set(s_root[-1], phi);
        print("\tOur method: Check log, arg mod 2pi/e: \x1b[{}OK\x1b[0m"
              .format("32m" if logarg_is_equal(ls_root,s[i],argmod=er) else "31mN"));
        # The assert are here to quantify how far are the values for diagnostic
        assert(fp.fp_assert_equal("", ls_root.inf, s[i].inf, target=1000));
        assert(fp.fp_assert_zero("", [min(_th.abs(), 1-_th.abs()) for _th in logarg_reduce_args(er*ls_root.args) - logarg_reduce_args(er*s[i].args)], target=1000));
    
    t_root  = "%.2f" % t_root
    t_shiro = "%.2f" % t_shiro
    f = open(str_file, 'a')
    f.write(str(H.nrows()) + "\t" + t_root + "\t" + t_shiro + "\n")
    f.close()
    

print ("Tot. candidates done: {}".format(nb_cand));
