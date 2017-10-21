require(graphics)
require(Matrix)
require(lattice)
require(data.table)
#source("plotAgg.r")

# pdf(file="Experiment1.pdf",
#   width=4.6, height=4, family="serif", pointsize=14)

T = read.table("all_times.tsv", sep="\t", header=TRUE)
T2 = data.table(alg=T$alg, type=T$type, compile=T$compile, execute=T$execute)
T2$type <- factor(T2$type, levels=c("none", "none_spoof", "default", "default_spoof"))
T2[order(alg, type)]

colors=c("lightblue", "blue", "green", "darkgreen")
barchart(compile + execute ~ alg, groups=type, T2, auto.key=list(space="right"), outer=TRUE, par.settings=list(superpose.polygon=list(col=colors)))

#, col=rainbow(length(unique(T2$type)))
#scales=list(y=list(log=10))
#main="Runtime with & without Spoof"
# axis(2, las=1,at=c(0.01,0.1,1,10, 100, 1000), labels=c("0.01","0.1","1","10","100","1000")) # horizontal y axis
