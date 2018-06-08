  # Rscript plotAgg.r && xreader Experiment1.pdf &
  require(graphics)
  require(Matrix)
  require(lattice)
  require(data.table)
  #source("plotAgg.r")

pdf(file="Experiment1.pdf",
  paper="a4r", family="serif", pointsize=14)
#width=4.6, height=4

T = read.table("all_times.tsv", sep="\t", header=TRUE)
T2 = data.table(alg=T$alg, type=T$type, compile=T$compile, execute=T$execute)
T2$type <- factor(T2$type, levels=c("none", "none_spoof_best", "none_spoof_no", "none_spoof_script", "default", "default_spoof_no", "default_spoof_script", "default_spoof_best"))
T2[order(alg, type)]
# T2[3:4,4]=0
colors=c("lightblue", "blue", "green", "darkgreen")
barchart(compile + execute ~ alg, groups=type, T2, auto.key=list(space="inside", x=0.01, y=0.93), outer=TRUE, par.settings=list(superpose.polygon=list(col=colors)), main=paste("Spoof Experiment 1M x 10"), sub=paste("Plotted on", Sys.time()), ylim=c(0,max(T2$execute*1.04, T2$compile*1.04)), scales=list(x=list(rot=45)))
#, col=rainbow(length(unique(T2$type)))
#scales=list(y=list(log=10))
#main="Runtime with & without Spoof"
# axis(2, las=1,at=c(0.01,0.1,1,10, 100, 1000), labels=c("0.01","0.1","1","10","100","1000")) # horizontal y axis
# scales=list(cex=1.2)

dev.off() 

