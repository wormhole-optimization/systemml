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
Y=  matrix( c(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20), nrow=10, ncol=2, byrow=TRUE)
cb= matrix( c(2,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20), nrow=10, ncol=2, byrow=TRUE)
lt= matrix( c(0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0), nrow=10, ncol=2, byrow=TRUE)
flip_pos = matrix(c(0,1,1,0), nrow=2, ncol=2, byrow=TRUE);
flip_neg = matrix(c(0,-1,1,0), nrow=2, ncol=2, byrow=TRUE);

div = cb / rowSums(cb)
yp = div * (1.0 - rowSums(lt)) + lt
g_Y = rowSums(Y * (yp %*% flip_neg))
w = rowSums(Y * (yp %*% flip_pos) * yp)
R = cbind(g_Y, w)

writeMM(as(R, "CsparseMatrix"), paste(args[2], "S", sep=""));
