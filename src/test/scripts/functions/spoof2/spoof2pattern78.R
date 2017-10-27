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
library("Matrix")
library("matrixStats")
N = 20
D = 10
K = 2
X = matrix (0.5, nrow = N, ncol = D);
Y = matrix (1, nrow = N, ncol = (K+1));
#delta = 0.5 * sqrt (D) / 1.1
P = matrix (1, nrow = N, ncol = K+1);   ### exp_LT = exp (LT);
P = P / (K + 1);                        ### P =  exp_LT / (rowSums (exp_LT) %*% matrix (1, nrow = 1, ncol = K+1));
Grad = t(X) %*% (P [, 1:K] - Y [, 1:K]);
#norm_Grad = sqrt (sum (Grad ^ 2));
psi = 0.1;

    S = matrix (0, nrow = D, ncol = K);
	R = - Grad;
	norm_R2 = sum (R ^ 2);
	#innerconverge = (sqrt (norm_R2) <= psi * norm_Grad);
	#print(innerconverge)

#B = matrix (0, nrow = D, ncol = K);
#S = matrix (0.1, nrow = D, ncol = K);
#B_new = B + S;
#ssX_B_new = B_new
#lambda=1.5
#qk=-.9
#eta0 = 0.0001;
#obj=5


#    LT = cbind ((X %*% ssX_B_new), matrix (0, nrow = N, ncol = 1));
#    LT = LT - rowMaxs (LT) %*% matrix (1, nrow = 1, ncol = K+1);
#    exp_LT = exp (LT);
#    P_new  = exp_LT / (rowSums (exp_LT) %*% matrix (1, nrow = 1, ncol = K+1));
#    obj_new = - sum (Y * LT) + sum (log (rowSums (exp_LT))) + 0.5 * sum (lambda * (B_new ^ 2));
#
#    actred = (obj - obj_new);
#    print(obj)
#    print(obj_new)
#
#    rho = actred / qk;
#    is_rho_accepted = (rho > eta0);
#    snorm = sqrt (sum (S ^ 2));

print(sum(R))
OUT = as.matrix(norm_R2)

writeMM(as(OUT, "CsparseMatrix"), paste(args[2], "S", sep=""));
