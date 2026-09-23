#!/bin/bash
. /tmp/gate_lib.sh
. /tmp/abr_env.sh
cd $ABR
S=/tmp/s6_rem_status.txt
rm -f $S
T=$ABR/src/abr_top/uvmf/uvmf_template_output/project_benches/mldsa/tb/tests/src
TESTS="ML_DSA_keygen_KATs_test ML_DSA_keygen_signing_KATs_test ML_DSA_verif_KATs_test \
ML_DSA_externalmu_KATs_test ML_DSA_externalmu_ACVP_KATs_test ML_DSA_ACVP_rejection_KATs_test \
ML_DSA_randomized_all_test ML_DSA_87_randomized_kg_sign_verify_test \
ML_KEM_keygen_KATs_test ML_KEM_encaps_KATs_test ML_KEM_decaps_KATs_test \
ML_KEM_1024_kg_encaps_decaps_test"
N=0
for t in $TESTS; do
  pb fe sim --tb integration_lib::uvmf_mldsa --testfile $T/$t.yml --submit-timeout-arg 3600 > /tmp/s6_rem_$t.log 2>&1 &
  N=$((N+1))
  if [ $((N % 4)) -eq 0 ]; then wait; fi
done
wait
for t in $TESTS; do gate_report $t $S; done
echo ALL_DONE >> $S
