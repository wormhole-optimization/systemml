#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace

num_cols=10
sparsity=1.0
addOpts="--stats"
genData=0
reps=1
runner="./sparkDML.sh"

algs=( mlogreg ) #kmeans l2svm  linregcg ) #glm-binomial-probit )
confs=( "none_spoof" ) #"default" "none" "none_spoof" )

num_rowsArr=( 10000000 )
for num_rows in "${num_rowsArr[@]}"
do
for alg in "${algs[@]}"
do
    #if ! hdfs dfs -test -f "${fA}" || ! hdfs dfs -test -f "${fA}.mtd"; then
    if [ "${genData}" == 1 ]; then
        cmd=$(num_cols=${num_cols} num_rows=${num_rows} sparsity=${sparsity} \
                envsubst < queries/datagen_${alg}.txt)
        cmd="${runner} --config SystemML-config-default.xml ${cmd}"
#        eval "${cmd}"
    fi
    for conf in "${confs[@]}"
    do
        for rep in `seq 1 ${reps}`
        do
            echo ${num_rows} ${alg} ${conf} \#${rep}
            cmd=$(num_cols=${num_cols} num_rows=${num_rows} sparsity=${sparsity} \
                envsubst < queries/alg_${alg}.txt)
            cmd="--config ./SystemML-config-${conf}.xml ${addOpts} ${cmd}"
            tstart=$SECONDS
            echo "${runner} ${cmd}"
            echo "${cmd}" | xargs "${runner}"
            echo "${alg} ${num_rows} $(($SECONDS - $tstart - 3))" >> times_${conf}.txt

            if [[ "${addOpts}" == *"--stats"* ]] && [[ "${conf}" == *"_spoof" ]]; then 
                mkdir -p stats
                cp stats.tsv stats/${alg}-${conf}-stats.tsv
                cp stats-inputs.tsv stats/${alg}-${conf}-stats-inputs.tsv
            fi
        done
    done
done
done
