#!/usr/bin/env bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace
runner="./sparkDML.sh"
script_start="$(date '+%Y%m%d.%H%M%S')"

sparsity=1.0
addOpts="--stats --explain2 hops" # --explain2 hops"
genData=0
reps=3
saveTimes=1

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
num_rowsArr_reduced=( 10000 )
# num_rowsArr_expanded=( 500000000 )
for alg in "${algs[@]}"; do
case "${alg}" in
    "als-cg"|"autoencoder")
        actual_rowsArr=${num_rowsArr_reduced}
        num_cols=10000 # als-cg: rank set to 10
        ;;
    # "linregcg")
    #     actual_rowsArr=${num_rowsArr_expanded}
    #     num_cols=10
    #     ;;
    *)
        actual_rowsArr=${num_rowsArr}
        num_cols=10
        ;;
esac

for num_rows in "${actual_rowsArr[@]}"; do
    #if ! hdfs dfs -test -f "${fA}" || ! hdfs dfs -test -f "${fA}.mtd"; then
    if [ "${genData}" == 1 ]; then
        cmd=$(num_cols=${num_cols} num_rows=${num_rows} sparsity=${sparsity} als_nnz=$(($num_rows * $num_cols / 100)) \
                envsubst < queries/datagen_${alg}.txt)
        cmd="--config SystemML-config-default.xml ${cmd}"
        echo "${cmd}" | xargs "${runner}"
    fi
    for conf in "${confs[@]}"; do
        if [ "$alg" == "als-cg" ] && [[ "$conf" == none* ]]; then
            myreps=1
        else
            myreps=${reps}
        fi
        for rep in `seq 1 ${myreps}`; do
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

echo "${script_start}" > latest_start
echo "${script_end}" > latest_end
./selectTimes.sh 1
./aggTimes.sh
PlotName="Experiment1-${script_end}.pdf"
Rscript plotAgg.r && cp Experiment1.pdf "${PlotName}" && xreader "${PlotName}" &
#dot -Tpdf explain.dot -o dot.pdf
