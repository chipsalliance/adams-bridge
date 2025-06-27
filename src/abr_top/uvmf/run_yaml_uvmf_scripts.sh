export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
python ${UVMF_HOME}/scripts/yaml2uvmf.py mldsa_predictor.yaml \
                                         mldsa_scoreboard.yaml \
                                         ../../../../caliptra-rtl/src/libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         mldsa_environment.yaml \
                                         mldsa_bench.yaml \
                                         -d uvmf_template_output

