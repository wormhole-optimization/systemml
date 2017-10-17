#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace

num_cols=10
sparsity=1.0
addOpts="--stats"
genData=0
reps_orig=1

runner="./sparkDML.sh"


save_statsArr=( 1 0 ) # set to ( 1 0 ) to do save_stats and then normal run
for save_stats in "${save_statsArr[@]}"
do
if [ save_stats == 1 ]
then num_rowsArr=( 10000000 )
else num_rowsArr=( 10000000 )
fi

for num_rows in "${num_rowsArr[@]}"
do
algs=( kmeans ) #l2svm mlogreg  linregcg ) #glm-binomial-probit )
for alg in "${algs[@]}"
do
    #if ! hdfs dfs -test -f "${fA}" || ! hdfs dfs -test -f "${fA}.mtd"; then
    if [ "${genData}" == 1 ]; then
        cmd=$(num_cols=${num_cols} num_rows=${num_rows} sparsity=${sparsity} \
                envsubst < queries/datagen_${alg}.txt)
        cmd="${runner} --config SystemML-config-default.xml ${cmd}"
#        eval "${cmd}"
    fi

    if [ save_stats == 1 ]; then
        confs=( "none_spoof" "default_spoof" )
        reps=1
    else
        confs=( "none" "none_spoof" "default" "default_spoof" )
        reps=${reps_orig}
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

            if [[ ${save_stats} == 1 ]]; then # "${addOpts}" == *"--stats"*
                mkdir -p stats
                cp stats.tsv stats/${alg}-${conf}-stats.tsv
                cp stats-inputs.tsv stats/${alg}-${conf}-stats-inputs.tsv
            fi
        done
    done
done
done
done
