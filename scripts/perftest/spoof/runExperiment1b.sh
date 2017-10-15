#!/bin/bash

num_cols=$1
user=$(whoami)

#for all data sizes
for num_rows in 10000000 #100000000 airline78 mnist8m
do 
   #generate input data
#   ./sparkDML.sh --config SystemML-config_fused_gen.xml -f ./dml/DatagenClass.dml --args ${num_rows} ${num_cols} 5 5 spoof/w2_${num_rows} spoof/X2_${num_rows} spoof/y2_${num_rows} 1 0 $2 binary 0
   
   #for all repetitions
   for rep in 1 #{1..3}
   do
      #for all baselines
      for conf in "base" "base_spoof" "fused" "fused_spoof" "gen" "gen_spoof" "fused_gen" "fused_gen_spoof"
      do
         tstart=$SECONDS
         ./sparkDML.sh -f ./dml/MultiLogReg.dml --config ./SystemML-config_${conf}.xml --stats --nvargs X=spoof/X2_${num_rows} Y=spoof/y2_${num_rows} icpt=0 tol=0.000000000001 reg=0.001 moi=20 mii=10 B=spoof/w2 fmt="binary"
         echo "mlogreg "${num_rows}" "$(($SECONDS - $tstart - 3)) >> times_${conf}.txt
      done
   done
done
