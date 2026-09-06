/*
Exact round_extract_gmp excerpt from IPFE-2023/src/rlwe_sife.c.
Pinned source commit and hash: see results/rlwe_source_results.json.
See EXTRACTED_CODE_LICENSES.md for both upstream attributions.
Optimized2023 modifications have no separately recorded upstream license;
the following original MIT notice is retained for inherited code.

MIT License

Copyright (c) 2021 Jose Maria Bermudo Mera and Angshuman Karmakar and Tilen Marc and Azam Soleimanian

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/
#include <stdint.h>
#include <stdio.h>
#include <gmp.h>
#include "/Users/ember/dev/zkml-research/research/learn_infer_only/experiments/private_construction/vendor/IPFE-RLWE/src/params.h"
void round_extract_gmp(mpz_t a[SIFE_N])
{
	int i;

	mpz_t SIFE_Q_gmp, SIFE_Q_gmp_by2, SIFE_P_gmp;
	mpz_init(SIFE_Q_gmp);
	mpz_init(SIFE_P_gmp);
	mpz_init(SIFE_Q_gmp_by2);

	if(mpz_set_str(SIFE_Q_gmp, SIFE_Q_str, 10)!=0){
		printf("--ERROR unable to set Q to gmp--\n");
		return;
	}

	if(mpz_set_str(SIFE_P_gmp, SIFE_P_str, 10)!=0){
		printf("--ERROR unable to set P to gmp--\n");
		return;
	}

	mpz_fdiv_q_ui(SIFE_Q_gmp_by2, SIFE_Q_gmp, 2);
	//gmp_printf("d[0]: %Zd\n", a[0]);
	#pragma omp parallel private(i) default(shared)
	{ 
		mpz_t quotient, rem, a_i;
		mpz_init(quotient);
		mpz_init(rem);
		mpz_init(a_i);
		#pragma omp for schedule(static) nowait
		for (i = 0; i < SIFE_N; ++i) {
			//mpz_set_ui(a_i, a[i]);
			mpz_set(a_i, a[i]);
			//mpz_mul_ui(a_i, a_i, SIFE_P);
			mpz_mul(a_i, a_i, SIFE_P_gmp);
			//mpz_fdiv_qr_ui(quotient, rem, a_i, SIFE_Q);
			mpz_fdiv_qr(quotient, rem, a_i, SIFE_Q_gmp);
			//if( mpz_cmp_ui(rem, (SIFE_Q_gmp >> 1)) > 0 ) {
			if( mpz_cmp(rem, SIFE_Q_gmp_by2 ) > 0 ) {
				mpz_add_ui(quotient, quotient, 1);
			} 
			//a[i] = mpz_get_ui(quotient);
			mpz_set(a[i], quotient);
		}
		mpz_clear(quotient);
		mpz_clear(rem);
		mpz_clear(a_i);
	}
	mpz_clear(SIFE_Q_gmp);
	mpz_clear(SIFE_P_gmp);
	mpz_clear(SIFE_Q_gmp_by2);
}
int main(void) {
  mpz_t a[SIFE_N], q, delta;
  mpz_init_set_str(q, SIFE_Q_str, 10);
  mpz_init_set_str(delta, SIFE_SCALE_M_str, 10);
  for (int i=0; i<SIFE_N; i++) { mpz_init(a[i]); mpz_sub_ui(a[i],q,1); }
  mpz_mul_ui(a[1],delta,5); mpz_add_ui(a[1],a[1],1);
  round_extract_gmp(a);
  gmp_printf("{\"phase_q_minus_one_decoded\": %Zd, \"positive_five_decoded\": %Zd}\n", a[0],a[1]);
  int ok=mpz_cmp_ui(a[0],50241)==0 && mpz_cmp_ui(a[1],5)==0;
  for(int i=0;i<SIFE_N;i++) mpz_clear(a[i]);
  mpz_clear(q); mpz_clear(delta); return ok?0:1;
}
