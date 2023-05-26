# Code in support of arXiv:xxxx.xxxxx [pp.sss]
# Copyright 2023, Andrea Lesavourey
# GPL-3.0-only (see LICENSE file)

# set parameters of the grid
set border lw 2
set grid lw 1.25 lt 1 lc "grey"
set key bottom right
set key font ",12"
set key box lw 1 width -1 height 1
set xtics font ",12"
set ytics font ",12" 

# set line styles
set style line 1 dt 4 pt 2 ps 1 lw 2.8 lc "black" # gp
set style line 2 dt 5 pt 6 lw 2.8 lc "orange"  # crt

# put in logscale so we can see something
set logscale y


# data file for our crt-based method
file_crt(root) = sprintf('../data/crt_%s', root)
# data file for pari/gp nfroots function
file_crt_nfroots(root) = sprintf('../data/crt_%s_nfroots', root)
# figure file
figure_crt(root) = sprintf("figures/crt_%s.png", root)


# if we want we can restrict to a certain range for x and y coordinates
set xrange [0:300]
set yrange [0:10000]


do for [ROOT in "3 71 1637 13099"] {
    plot file_crt_nfroots(ROOT) u 2:5 ls 1 w p title "Pari/Gp nfroots",\
         file_crt(ROOT) u 2:5 ls 2 w p title "Algorithm 2"

    set terminal pngcairo
    set output figure_crt(ROOT)
    replot
}

