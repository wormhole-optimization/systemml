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

X= matrix(1, nrow=34, ncol=10)
Xw = matrix(0, nrow=nrow(X), ncol=1)
Y= matrix(1, nrow=34, ncol=1)
s = t(X) %*% Y
Xd = X %*% s
step_sz = 0.2
lambda=0.001
dd = lambda * sum(s * s)
w = matrix(0, nrow=ncol(X), ncol=1)
wd = lambda * sum(w * s)

tmp_Xw = Xw + step_sz*Xd
out = 1 - Y * (tmp_Xw)
sv = (out > 0)
out = out * sv
g = wd + step_sz*dd - sum(out * Y * Xd)
h = dd + sum(Xd * sv * Xd)
step_sz = step_sz - g/h

R= as.matrix(g*g)

writeMM(as(R, "CsparseMatrix"), paste(args[2], "S", sep=""));
