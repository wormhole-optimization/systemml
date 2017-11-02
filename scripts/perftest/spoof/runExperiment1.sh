#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace
runner="./sparkDML.sh"
script_start="$(date '+%Y%m%d.%H%M%S')"

num_cols=10
sparsity=1.0
addOpts="--stats" # --explain2 hops"
genData=0
reps=1
saveTimes=0

algs=() # linregcg kmeans l2svm mlogreg ) #linregcg kmeans mlogreg l2svm ) #glm-binomial-probit )
confs=() # none none_spoof default_spoof default )

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


num_rowsArr=( 10000000 )
for num_rows in "${num_rowsArr[@]}"; do
for alg in "${algs[@]}"; do
    #if ! hdfs dfs -test -f "${fA}" || ! hdfs dfs -test -f "${fA}.mtd"; then
    if [ "${genData}" == 1 ]; then
        cmd=$(num_cols=${num_cols} num_rows=${num_rows} sparsity=${sparsity} \
                envsubst < queries/datagen_${alg}.txt)
        cmd="--config SystemML-config-default.xml ${cmd}"
        echo "${cmd}" | xargs "${runner}"
    fi
    for conf in "${confs[@]}"; do
        for rep in `seq 1 ${reps}`; do
            echo "$(date '+%Y%m%d.%H%M%S')" ${num_rows} ${alg} ${conf} \#${rep}
            cmd=$(num_cols=${num_cols} num_rows=${num_rows} sparsity=${sparsity} \
                envsubst < queries/alg_${alg}.txt)
            cmd="--config ./SystemML-config-${conf}.xml ${addOpts} ${cmd}"
            
            logfile="logs/${alg}_${conf}.log.$(date '+%Y%m%d.%H%M%S')"
            tstart=$SECONDS
            echo "${cmd}" | xargs "${runner}" &> "${logfile}" || echo "${logfile}"
            # maybe do 2>&1
			tend=$SECONDS
            echo "Experiment Script Execution Time: $(($tend - $tstart - 3))" >> ${logfile}
            echo "Number of rows: ${num_rows}" >> ${logfile}

            if [[ "${addOpts}" == *"--stats"* ]] && [[ "${conf}" == *"_spoof" ]]; then 
                mkdir -p stats
                cp stats.tsv stats/${alg}-${conf}-stats.tsv
                cp stats-inputs.tsv stats/${alg}-${conf}-stats-inputs.tsv
            fi
        done
    done
done
done
script_end="$(date '+%Y%m%d.%H%M%S')"
if [ -r logs/script_start ] && [ -r logs/script_end ]; then
    echo "old start-end is $(cat logs/script_start) $(cat logs/script_end)"
fi
echo "new start-end is ${script_start} ${script_end}"
echo "saveTimes is ${saveTimes}"
if [ "${saveTimes}" == 1 ]; then
    echo "${script_start}" > logs/script_start
    echo "${script_end}" > logs/script_end
fi
