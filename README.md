# Computing $e$-th roots in number fields
Code given in support of arXiv preprint arXiv:xxxx.xxxx [pp.sss] (2023)


### Environment
The provided code has been tested with the following versions.

| Soft     | Version | Url                              |
|:---------|:--------|:---------------------------------|
| SageMath | v9.0    | https://www.sagemath.org/        |
| Pari/Gp  | v2.13.1 | https://pari.math.u-bordeaux.fr/ |
| Gnuplot  | v5.4    | http://www.gnuplot.info/         |
| fplll    | v5.3.2  | https://github.com/fplll/fplll   |


### Experiments rationale
Please take note that the last experiments are done within the context of 
the following ASIACRYPT 2022 paper, available on the IACR ePrint Archive
[ePrint:2021/1384](https://eprint.iacr.org/2021/1384):
> **Log-S-unit Lattices Using Explicit Stickelberger Generators to Solve Approx Ideal-SVP**
> Olivier Bernard, Andrea Lesavourey, Tuong-Huy Nguyen and Adeline Roux-Langlois

Other than that, the experiments (items 4. and 5. below) are designed to evaluate 
the general behaviour of our algorithms when compared to standard methods such
that Pari/Gp `nfroots` function. Thus we compute random elements $x$ of a given
number field $K$ such that $\log_2( \Vert x \Vert_{\infty})  < B$ and record 
the average time taken to compute the $e$th root of $y = x^e$, and this for several
bit-sizes $B$.

Note that some of the scripts given here will compute *more* data than showcased 
in the article. This is typically the case for Fig. 2, where conductors are now of the 
form $m = p*q$ where $q$ is a suitable integer, not necessarily a prime anymore.
This does not impact our results in any way.


### Computational workflow

We suppose that everything is executed from `./scripts`. In this folder, there 
are bash scripts (in .sh) for each set of experiments, creating each of the figures
provided in the paper. Beware that each of these bash scripts launch 2 (sometimes 3)
Python / SageMath processes, generally one for our methods and one for Pari/Gp nfroots.
Typically a script named `name.sh` will call `name.sage` and `name_nfroots.sage`. These will
print some logs in a corresponding file situated within the `./logs` folder, and experimental
results (mostly conductors, dimensions and timings) in files within the `./data` folder.
Some parameters can be modified within the bash script files, e.g. number of tests or some
parameters given in the calls to SageMath scripts.


0. Make sure that `logs` and `data` folders exist besides the `scripts` folder.
1. Computations for our CRT-based method (Figure 1), for primes `<p1>`...`<pr>`:
   ```
   ./crt.sh <p1> ... <pr>
   ```

2. Exp. for our relative Couveignes alg. with fixed relative degree $[K:k]$ (Figure 2), for primes `<p1>`...`<pr>`:
   ```
   ./couveignes_fixed_reldeg.sh <p1> ... <pr>
   ```
   This will launch three processes : one for `nfroots`, one for our implementation of 
   Alg. 5 using `nfroots` as function to compute the $e$-th root on the subfield, and
   one for our implementation of Alg. 5 using a Hensel lifting as function to compute the
   $e$-th root on the subfield (for suitable conductors).

3. Exp. for our relative Couveignes alg. with fixed exp. $e$ (Figure 3), for primes `<p1>`...`<pr>`:
   ```
   ./couveignes_fixed_root.sh <p1> ... <pr>
   ```
   This will launch three processes as for the previous script.

4. Exp. for saturation process from Twisted-Stickelberger approach, good case (Figure 4(a)),
exponent range `<r>` (i.e. only exp.  $e$   such that   $r-10 < \log_2(e) < r$:
   ```
   ./cf_roots_twphs_saturation_good.sh <r>
   ```
   Table 1 was specifically obtained using the following command (this computation took on the order of a few hours on a single core, assuming all `urs` data for `d=2` is available from Tw-Sti):
   ```
   ./cf_roots_twphs_saturation_good.sage MAX 39
   ```

5. Exp. for saturation process from Twisted-Stickelberger approach, bad case (Figure 4(b)):
   ```
   ./cf_roots_twphs_saturation_bad.sh
   ```


### Plotting results

First, make sure that `./figures` folder exists in the `./plots` folder.
In the Gnuplot script files, values are put as taken in the paper, but one can 
modify accordingly to his own experiments.


##### Obtaining Fig. 1
Run the `crt.plt` script as follows:
	```
	gnuplot crt.plt
	```
This creates files `crt_<p>.png` in folder `./figures`, for each value of `<p>` 
put in the script file.


##### Obtaining Fig. 2
Run the `couveignes_fixed_reldeg.plt` script as
	```
	gnuplot couveignes_fixed_reldeg.plt
	```
This creates file `couveignes_fixed_reldeg_<p>.png` in folder `./figures`, for 
each value of `<p>` put in the file. By uncommenting one line in the file, one can add data
points for our relative couveignes using a Hensel lifting as function for the root in the subfield.

##### Obtaining Fig. 3
Run the `couveignes_fixed_root.plt` script as
	```
	gnuplot couveignes_fixed_root.plt
	```
This creates file `couveignes_fixed_root_<p>.png` in folder `./figures`, for 
each value of `<p>` put in the file. 

##### Obtaining Fig. 4
Run the `saturation.plt` script as
	```
	gnuplot saturation.plt
	```
This creates file `cf_twphs_stickel_saturation_good_max.png` (Fig. 4(a)) and 
`cf_twphs_stickel_saturation_bad_max.png` (Fig. 4(b)) in folder `./figures`.
Careful that if one data file specified in the gnuplot script file does not exist, then 
gnuplot will stop all of its computations. Thus if no experiments were done for "bad fields", 
then one needs to modify slightly the file `saturation.plt` (line 34) as indicated by the 
comment just above it.

### Files organisation

##### Folder list
- `./src`: one file with all general functions.
- `./scripts`: Sage scripts. Each script shall be called _via_ its Bash `.sh` counterpart.
- `./Tw-Sti`: necessary material for saturation process taken from `Tw-Sti` git repo (given in support of the ASIACRYPT 2022 paper)
- `./data`: this is where all data are put. 
- `./logs`: logs of computations, including timings and many diagnostics.
- `./plots/`: Gnuplot scripts and 
- `./plots/figures`: plotted results


### License

&copy; 2023, Olivier Bernard, Andrea Lesavourey, Pierre-Alain Fouque.
This work is published under the GNU General Public License (GPL) v3.0.  
See the LICENSE file for complete statement.

