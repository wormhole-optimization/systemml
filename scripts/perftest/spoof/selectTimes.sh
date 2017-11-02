#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace

script_start=$(cat logs/script_start)
script_end=$(cat logs/script_end)
algs=() #( linregcg kmeans mlogreg l2svm ) #glm-binomial-probit )
confs=() # "default_spoof" "default" "none" "none_spoof" )


if [ "${#algs[@]}" == "0" ]; then
  while read -r line; do
    [[ $line = \#* ]] && continue
    algs+=(${line})
  done < "control_algs.txt"
fi

if [ "${#confs[@]}" == "0" ]; then
  while read -r line; do
    [[ $line = \#* ]] && continue
    confs+=(${line})
  done < "control_confs.txt"
fi


echo ${confs[@]}
return

function get_log_time() {
  ctime=$(grep "$1" "$2")
  [[ "${ctime}" =~ [^0123456789]*([0-9]+\.?[0-9]*)[^0123456789]* ]] && ctime=${BASH_REMATCH[1]}
  echo "${ctime}"
}
function leq() {
  [ "$1" == "$2" ] || [[ "$1" < "$2" ]]
}



echo "script_start: ${script_start}"
echo "script_end: ${script_end}"
for f in times_*; do
  rm "$f"
done
for alg in "${algs[@]}"; do
for conf in "${confs[@]}"; do
  for f in $(ls -1 "logs/${alg}_${conf}."*); do
    [[ "${f}" =~ ^logs/${alg}_${conf}\.log\.([0-9]{8}\.[0-9]{6})$ ]] && t=${BASH_REMATCH[1]} || continue
    if $(leq "${script_start}" "$t") && $(leq "$t" "${script_end}"); then
      echo $f
      ctime=$(get_log_time "Total compilation time:" "${f}")
      etime=$(get_log_time "Total execution time:" "${f}")
      num_rows=$(get_log_time "Number of rows: " "${f}")
      if [ -z "$ctime" ] && [ -z "$etime" ]; then
        ctime=0
        etime=$(get_log_time "Experiment Script Execution Time: " "${f}")
      fi
      echo "${alg} ${num_rows} ${ctime} ${etime}" >> times_${conf}.txt
    fi
  done
done
done



