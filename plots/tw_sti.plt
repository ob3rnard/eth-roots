# Code in support of arXiv:xxxx.xxxxx [pp.sss]
# Copyright 2023, Andrea Lesavourey
# GPL-3.0-only (see LICENSE file)

set border lw 2
set grid lw 1.25 lt 1 lc "grey"
set key right bottom
set key font ",12"
set key box lw 1 width -3 height 1
set xtics font ",12"
set ytics font ",12" 

set style line 1 dt 4 pt 2 lw 2 ps 1.5 lc "black" # gp
set style line 2 dt 5 pt 7 lw 1.8 ps 1.1 lc "orange"  # couveignes rec
set style line 3 dt 2 pt 6  lw 1.5 ps 1 lc "olive"   # norm


# some values a too big to consider 'normal' view
set logscale y			


# ##############################################################################
# BAD CASE i.e.  zeta_e | m

# type_exp = take min or max e possible
file_sat(type, type_exp) = sprintf('../data/cf_tw_sti_saturation_%s_%s_60',\
	       type, type_exp)
file_sat_nfroots(type, type_exp) = sprintf('../data/cf_tw_sti_saturation_%s_%s_60_nfroots',\
		       type, type_exp)
figure_sat(type, type_exp) = sprintf("figures/cf_tw_sti_saturation_%s_%s.png", type, type_exp)

TYPE="bad"

# if nothing has been computed, replace "max" by "", so that plot for good case
# can be treated
do for [TYPE_EXP in "max"] { 	
    plot file_sat_nfroots(TYPE, TYPE_EXP) u 2:($5/$4) ls 1 w p title "Pari/Gp nfroots",\
         file_sat(TYPE, TYPE_EXP) u 2:($6/$4) ls 2 w p title "Algorithm 4",\
	 # file_sat(TYPE, TYPE_EXP) u 2:($5/$4) ls 3 w p title "Relative norm in Alg. 4"
	 
    set terminal pngcairo
    set output figure_sat(TYPE, TYPE_EXP)
    replot
}


# ##############################################################################
# GOOD CASE 
# type_exp = take min or max e possible
# exp_range = bound for e ; only consider e s.t. log_2(e) < exp_range
file_sat_range_crt(type, type_exp, exp_range) =\
		     sprintf('../data/cf_tw_sti_saturation_%s_%s_%s',\
		     type, type_exp, exp_range)
file_sat_range_nfroots(type, type_exp, exp_range) =\
		     sprintf('../data/cf_tw_sti_saturation_%s_%s_%s_nfroots',\
		     type, type_exp, exp_range)
figure_sat(type, type_exp) = \
		       sprintf("figures/cf_tw_sti_saturation_%s_%s.png",\
		       type, type_exp)


TYPE="good"

do for [TYPE_EXP in "max"] {
    plot file_sat_range_nfroots(TYPE, TYPE_EXP, "10") u 2:($5/$4) ls 1 w p title "Pari/Gp nfroots",\
	 file_sat_range_crt(TYPE, TYPE_EXP, "10") u 2:($5/$4) ls 2 w p title "Algorithm 2",\
 	 file_sat_range_nfroots(TYPE, TYPE_EXP, "20") u 2:($5/$4) ls 1 w p notitle,\
	 file_sat_range_crt(TYPE, TYPE_EXP, "20") u 2:($5/$4) ls 2 w p notitle,\
	 file_sat_range_crt(TYPE, TYPE_EXP, "30") u 2:($5/$4) ls 2 w p notitle,\
    # file_sat_range_nfroots(TYPE, TYPE_EXP, "30") u 2:($5/$4) ls 1 w p notitle,\

    set terminal pngcairo
    set output figure_sat(TYPE, TYPE_EXP)
    replot
}





# # ###################  RATIO AGAINST EXPONENT E ###################


# # type = bad or good, i.e. zeta_e | m or not resp.
# # type_exp = within each of the previous categories, take min or max e possible
# # exp_range = bound for e ; only consider e s.t. log_2(e) < exp_range
# file_sat_range_crt(type, type_exp, exp_range) =\
# 		     sprintf('../data/cf_twphs_stickel_saturation_%s_%s_%s_crt',\
# 		     type, type_exp, exp_range)
# file_sat_range_pari(type, type_exp, exp_range) =\
# 		     sprintf('../data/cf_twphs_stickel_saturation_%s_%s_%s_nfroots',\
# 		     type, type_exp, exp_range)
# figure_sat(type, type_exp) = \
# 		       sprintf("figures/cf_twphs_stickel_saturation_ratio_%s_%s.png",\
# 		       type, type_exp)

# ratio(x, y)=x/y

# # unset logscale y
# set logscale x
# do for [TYPE in "good"] {
#     do for [TYPE_EXP in "max"] {
# 	plot '< paste '.file_sat_range_pari(TYPE, TYPE_EXP, "10").' '.file_sat_range_crt(TYPE, TYPE_EXP, "10") using ($2):($5/$10) w p lw 3 notitle

# 	# file_sat_range_pari(TYPE, TYPE_EXP, "10") u 2:($5/$4) ls 1 w p title "Pari/Gp nfroots",\
# 	#      file_sat_range_crt(TYPE, TYPE_EXP, "10") u 2:($5/$4) ls 3 w p title "Alg. 2",\
# 	#      file_sat_range_pari(TYPE, TYPE_EXP, "20") u 2:($5/$4) ls 1 w p notitle,\
# 	#      file_sat_range_crt(TYPE, TYPE_EXP, "20") u 2:($5/$4) ls 3 w p notitle
	
# 	set terminal pngcairo
# 	set output figure_sat(TYPE, TYPE_EXP)
# 	replot
#     }
# }
