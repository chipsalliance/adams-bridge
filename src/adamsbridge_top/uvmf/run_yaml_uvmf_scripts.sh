export UVMF_HOME='/home/cad/tools/mentor/uvmf/UVMF_2022.3'
python ${UVMF_HOME}/scripts/yaml2uvmf.py adamsbridge_predictor.yaml \
                                         adamsbridge_scoreboard.yaml \
                                         ../../../../caliptra-rtl/src/libs/uvmf/qvip_ahb_lite_slave_dir/uvmf/qvip_ahb_lite_slave_subenv_config.yaml \
                                         adamsbridge_environment.yaml \
                                         adamsbridge_bench.yaml \
                                         -d uvmf_template_output

