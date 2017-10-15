#!/bin/bash

num_cols=$1
user=$(whoami)

#for all data sizes
for num_rows in 10000000 #100000000 airline78 mnist8m
do 
   #generate input data
   ./sparkDML2.sh ./lib/SystemML.jar -f ./dml/DatagenClass.dml -args ${num_rows} ${num_cols} 5 5 \
   mboehm/spoof/w5_${num_rows} mboehm/spoof/X5_${num_rows} mboehm/spoof/y5_${num_rows} 1 0 $2 binary 0
   
   #for all repetitions
   for rep in 1 #{1..3}
   do
      #for all baselines
      for conf in "base" #"base_spoof" "fused" "fused_spoof" "gen" "gen_spoof" "fused_gen" "fused_gen_spoof"
      do
         tstart=$SECONDS
         ./sparkDML.sh -f ./dml/Kmeans.dml --config ./SystemML-config_${conf}.xml --stats --nvargs \
         X=spoof/X5_${num_rows} k=5 runs=1 C=spoof/C_centroids.mtx maxi=20 tol=0.000000000001 fmt="binary"
         echo "kmeans "${num_rows}" "$(($SECONDS - $tstart - 3)) >> times_${conf}.txt
      done
   done
done
