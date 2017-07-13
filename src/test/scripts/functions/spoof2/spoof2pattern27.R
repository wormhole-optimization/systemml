#-------------------------------------------------------------
#
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
# 
#   http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
#
#-------------------------------------------------------------

args<-commandArgs(TRUE)
options(digits=22)
library(Matrix)
X = matrix(  c(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15), nrow=5, ncol=3, byrow = TRUE)
num_records = 5
num_features = 3

avg_X_cols = t(colSums(X)) / num_records;
var_X_cols = (t(colSums (X ^ 2)) - num_records * (avg_X_cols ^ 2)) / (num_records - 1);

is_unsafe = var_X_cols <=  0.0

scale_X = 1.0 / sqrt (var_X_cols * (1 - is_unsafe) + is_unsafe);
scale_X [num_features, 1] = 1;
shift_X = - avg_X_cols * scale_X;
shift_X [num_features, 1] = 0;
rowSums_X_sq = (X ^ 2) %*% (scale_X ^ 2) + X %*% (2 * scale_X * shift_X) + sum (shift_X ^ 2);

writeMM(as(rowSums_X_sq, "CsparseMatrix"), paste(args[2], "S", sep=""));
