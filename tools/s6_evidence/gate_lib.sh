# Parse the UVM report summary, which is the only reliable pass/fail source.
# UVMF prints "UVM_ERROR /abs/path/file.svh(334) @ 1234ns" for each error, so a
# grep for 'UVM_ERROR @' never matches and always reports zero.
# The shared scratch area is subject to wholesale purges, so the summary block
# is archived to /tmp/s6_evidence immediately - a purge mid-gate otherwise
# destroys the evidence for every test that already passed.
gate_report() { # $1 = test name, $2 = status file
  local L E F
  L=$(ls -td /home/ws/caliptra/mojtabab/caliptra/ws2/scratch/mojtabab/simland/uvmf_mldsa/$1/20* 2>/dev/null | head -1)
  E=$(grep -oE "UVM_ERROR :[ ]*[0-9]+" "$L/sim.log" 2>/dev/null | grep -oE "[0-9]+$" | tail -1)
  F=$(grep -oE "UVM_FATAL :[ ]*[0-9]+" "$L/sim.log" 2>/dev/null | grep -oE "[0-9]+$" | tail -1)
  [ -z "$E" ] && E=NOSUMMARY
  [ -z "$F" ] && F=NOSUMMARY
  mkdir -p /tmp/s6_evidence
  if [ -f "$L/sim.log" ]; then
    { echo "=== $1  ($L) ==="; grep -nE "UVM_(INFO|WARNING|ERROR|FATAL) :" "$L/sim.log" | tail -20; } \
      > /tmp/s6_evidence/$1.summary 2>/dev/null
  fi
  echo "$1 UVM_ERROR=$E UVM_FATAL=$F LOG=$L" >> "$2"
}
