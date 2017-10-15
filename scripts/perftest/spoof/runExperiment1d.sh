#!/bin/bash

num_cols=$1
user=$(whoami)

#for all data sizes
for num_rows in 10000000 #100000000 airline78 mnist8m
do 
   #generate input data
   ./sparkDML2.sh ./lib/SystemML.jar -f ./dml/DatagenReg.dml -args ${num_rows} ${num_cols} 5 5 \
   spoof/w4_${num_rows} spoof/X4_${num_rows} spoof/y4_${num_rows} 1 0 $2 binary
   
   #for all repetitions
   for rep in 1 #{1..3}
   do
      #for all baselines
      for conf in "base" #"base_spoof" "fused" "fused_spoof" "gen" "gen_spoof" "fused_gen" "fused_gen_spoof"
      do
         tstart=$SECONDS
         ./sparkDML.sh -f ./dml/LinearRegCG.dml --config ./SystemML-config_${conf}.xml --stats --nvargs \
         X=spoof/X4_${num_rows} Y=spoof/y4_${num_rows} icpt=0 tol=0.000000000001 reg=0.001 maxi=20 B=spoof/w4 fmt="binary"
         echo "linregcg "${num_rows}" "$(($SECONDS - $tstart - 3)) >> times_${conf}.txt
      done
   done
done
