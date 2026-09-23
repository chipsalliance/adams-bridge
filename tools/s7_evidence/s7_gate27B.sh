#!/bin/bash
. /tmp/gate_lib7.sh
. /tmp/abr_env.sh
cd $ABR
S=/tmp/s7_status27B.txt
rm -f $S
T=$ABR/src/abr_top/uvmf/uvmf_template_output/project_benches/mldsa/tb/tests/src
TESTS="ML_DSA_44_keygen_signing_KATs_test ML_DSA_65_keygen_signing_KATs_test \
ML_DSA_keygen_KATs_test ML_DSA_keygen_signing_KATs_test ML_DSA_verif_KATs_test \
ML_DSA_externalmu_KATs_test ML_DSA_externalmu_ACVP_KATs_test ML_DSA_ACVP_rejection_KATs_test \
ML_DSA_65_externalmu_ACVP_KATs_test ML_DSA_44_externalmu_ACVP_KATs_test \
ML_DSA_44_keygen_KATs_test ML_DSA_65_keygen_KATs_test \
ML_KEM_keygen_KATs_test ML_KEM_encaps_KATs_test ML_KEM_decaps_KATs_test \
ML_KEM_512_kg_encaps_decaps_test ML_KEM_768_kg_encaps_decaps_test ML_KEM_1024_kg_encaps_decaps_test \
ML_KEM_512_keygen_KATs_test ML_KEM_768_keygen_KATs_test \
ML_KEM_512_encaps_decaps_KATs_test ML_KEM_768_encaps_decaps_KATs_test \
ML_DSA_randomized_all_test \
ML_DSA_44_randomized_kg_sign_verify_test ML_DSA_65_randomized_kg_sign_verify_test \
ML_DSA_87_randomized_kg_sign_verify_test \
ML_DSA_MLKEM_param_set_mix_test"
N=0
for t in $TESTS; do
  pb fe sim --tb integration_lib::uvmf_mldsa --testfile $T/$t.yml --submit-timeout-arg 14400 +abr_rejb_profile > /tmp/s7B_$t.log 2>&1 &
  N=$((N+1))
  if [ $((N % 4)) -eq 0 ]; then wait; fi
done
wait
for t in $TESTS; do gate_report $t $S; done
echo ALL_DONE >> $S
