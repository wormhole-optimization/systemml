#!/bin/bash

num_cols=10
sparsity=1.0
stats=1
genData=1
reps=3

user=$(whoami)
num_cols=$1
sparsity=$2
stats=$3
genData=$4
reps=$5
if [ "${stats}" == 1 ]; then
    stats="--stats"
else
    stats=""
fi

#for all data sizes
for num_rows in 10000000 #100000000 airline78 mnist8m
do 
   #generate input data
   if [ "${genData}" == 1 ]; then
       ./sparkDML.sh --config SystemML-config_fused_gen.xml -f ./dml/DatagenClass.dml --args ${num_rows} ${num_cols} 5 5 \
       spoof/w5_${num_rows} spoof/X5_${num_rows} spoof/y5_${num_rows} 1 0 $2 binary 0
   fi
   
   #for all repetitions
   for rep in `seq 1 ${reps}`
   do
      #for all baselines
      arr=( "base" "base_spoof" "fused" "fused_spoof" "gen" "gen_spoof" "gen__fused" "gen__fused_spoof" )
      if [ "${stats}" == "--stats" ]; then
         arr=( "base_spoof" "fused_spoof" "gen_spoof" "gen__fused_spoof" )
      fi
      for conf in "${arr[@]}"
      do
         echo kmeans ${num_rows} ${conf}
         tstart=$SECONDS
         ./sparkDML.sh -f ./dml/Kmeans.dml --config ./SystemML-config_${conf}.xml ${stats} --nvargs \
         X=spoof/X5_${num_rows} k=5 runs=1 C=spoof/C_centroids.mtx maxi=20 tol=0.000000000001 fmt="binary"
         echo "kmeans "${num_rows}" "$(($SECONDS - $tstart - 3)) >> times_${conf}.txt
      if [ "${stats}" == "--stats" ]; then
         mkdir -p stats
         cp stats.tsv stats/kmeans-${conf}-stats.tsv
         cp stats-inputs.tsv stats/kmeans-${conf}-stats-inputs.tsv
      fi
      done
   done
done
