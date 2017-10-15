#!/usr/bin/env bash

if [ -f "all_times.tsv" ]; then
    rm all_times.tsv
fi
tmpfile=$(mktemp)
for f in $(ls -1 times_*.txt); do
    t=${f#*_}
    conf=${t%.txt}
    #echo $conf
    awk "{
        arr[\$1, \$2]+=\$3
        cnt[\$1, \$2]+=1
    }
    END {
        for (key in arr) {
            split(key, keyarr, SUBSEP)
            printf(\"%s\t%s\t${conf}\t%s\n\", keyarr[1], keyarr[2], arr[key] / cnt[key])
        }
    }" "$f" >> "${tmpfile}" #| sort +0n -1
#    while IFS= read -r line; do
#
#    done < "$f"
done

sort "${tmpfile}" > "all_times.tsv"
