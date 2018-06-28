# Rscript plotAgg.r && xreader Experiment1.pdf &
require(graphics)
require(Matrix)
require(lattice)
require(data.table)
library(latticeExtra)
#source("plotAgg.r")

pdf(file="Experiment1.pdf",
  paper="a4r", family="serif", pointsize=14)
#width=4.6, height=4

T = read.table("all_times.tsv", sep="\t", header=TRUE)
T2 = data.table(alg=T$alg, type=T$type, compile=T$compile, execute=T$execute)
T2[order(alg, type)]
#T2$type <- factor(T2$type, levels=c("none", "none_spoof_no", "none_spoof_script", "none_spoof_best"))
#T2$type <- factor(T2$type, levels=c("default", "default_spoof_no", "default_spoof_script", "default_spoof_best")) 
T2$type <- factor(T2$type, levels=c("nofuse", "nofuse_spoof_no", "nofuse_spoof_script", "nofuse_spoof_best")) 
T2e = data.table(alg=T2$alg, type=T2$type, execute=T2$execute)
T2c = data.table(alg=T2$alg, type=T2$type, execute=T2$compile)
# T3 = rbind(data.table(alg=T2$alg, type=T2$type, execute=T2$execute),
#   data.table(alg=T2$alg, type=T2$type, execute=T2$compile * 10))
# T2[3:4,4]=0

colors=c("lightblue", "blue", "green", "darkgreen")
#colorsLeg=rbind(colors,c("orange"))
linetype=c(1,1,1,1) #2,2,2,2,1,1,1,1)
legdisp=c("Default SystemML", "Spoof, no + factorization", "Spoof, using script + factorization", "Spoof, using best of the two")
#compile + execute ~ alg
#auto.key=list(space="inside", x=0.01, y=0.93)

p1 <- barchart(execute ~ alg, groups=type, T2e, key=list(rep=FALSE, corner=c(0,0), x=0.44, y=0.88, text=list(legdisp), rectangles=list(col=colors)), outer=TRUE, par.settings=list(superpose.polygon=list(col=colors, lty=linetype)), main=paste("Performance of Optimized Plans"), sub=paste("Plotted", Sys.time(), " Size 10M x 10 except als-cg, autoencoder at 5k x 10k; sparsity 0.01"), ylim=c(0,max(T2$execute*1.02, T2$compile*1.02)), scales=list(x=list(rot=0)), ylab="Execution Time (s) [Compile time, including dynamic recompile, shown at bottom in orange]")
p2 <- barchart(execute ~ alg, groups=type, T2c, outer=TRUE, par.settings=list(superpose.polygon=list(col="orange", lty=linetype)))
p1 + p2

#, col=rainbow(length(unique(T2$type)))
#scales=list(y=list(log=10))
#main="Runtime with & without Spoof"
# axis(2, las=1,at=c(0.01,0.1,1,10, 100, 1000), labels=c("0.01","0.1","1","10","100","1000")) # horizontal y axis
# scales=list(cex=1.2)

dev.off() 

