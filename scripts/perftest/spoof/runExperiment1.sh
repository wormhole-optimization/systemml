#!/bin/bash

num_cols=10
sparsity=1.0
stats=0
genData=0

./runExperiment1a.sh ${num_cols} ${sparsity} ${stats} ${genData}
./runExperiment1b.sh ${num_cols} ${sparsity} ${stats} ${genData}
#./runExperiment1c.sh ${num_cols} ${sparsity} ${stats} ${genData}
./runExperiment1d.sh ${num_cols} ${sparsity} ${stats} ${genData}
./runExperiment1e.sh ${num_cols} ${sparsity} ${stats} ${genData}




