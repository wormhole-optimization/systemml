# Spoof Experiment

Set algoithm and config parameters for these scripts in `control_algs.txt` and `control_confs.txt`.

1. `./runExperiment1.sh` --- alter the `algs`, `configs`, `num_rows` to customize. Dumps logs in `logs/` and stats in `stats/`.
2. `./selectTimes.sh` --- Parses logs for compile/execution times into `times_*`. Only takes logs whose time is between `logs/script_end` and `logs/script_end` unless you customize.
3. `./aggTimes.sh` --- Take average of times in `times_*` into `all_times.tsv`.
4. `R ./plotAgg.r`
