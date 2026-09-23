#!/bin/bash
. /tmp/gate_lib7.sh
. /tmp/abr_env.sh
cd $ABR
PKG=src/abr_sampler_top/rtl/abr_sampler_pkg.sv
cp $PKG /tmp/s7_pkg_backup.sv
# Negative control: starve the eta = 4 bank so the natural loop length becomes
# seed dependent. The pad must keep the *observable* length constant anyway.
sed -i "s/^\(  parameter REJB_NUM_SAMPLERS_ETA4 *= *\)20;/\18;/" $PKG
grep -n "REJB_NUM_SAMPLERS_ETA4" $PKG
pb fe build --tb integration_lib::uvmf_mldsa --submit-timeout-arg 3600 > /tmp/s7_negctl_build.log 2>&1
echo "BUILD_RC=$?" | tee /tmp/s7_negctl_build.rc
T=$ABR/src/abr_top/uvmf/uvmf_template_output/project_benches/mldsa/tb/tests/src
S=/tmp/s7_negctl_status.txt
rm -f $S
for t in ML_DSA_65_keygen_KATs_test ML_DSA_65_randomized_kg_sign_verify_test; do
  pb fe sim --tb integration_lib::uvmf_mldsa --testfile $T/$t.yml --submit-timeout-arg 14400 +abr_rejb_profile > /tmp/s7_neg_$t.log 2>&1 &
done
wait
for t in ML_DSA_65_keygen_KATs_test ML_DSA_65_randomized_kg_sign_verify_test; do gate_report $t $S; done
cp /tmp/s7_pkg_backup.sv $PKG
grep -n "REJB_NUM_SAMPLERS_ETA4" $PKG
echo NEG_DONE >> $S
