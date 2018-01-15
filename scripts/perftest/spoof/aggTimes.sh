#!/usr/bin/env bash

AllTimesFile="all_times.tsv"

if [ -f ${AllTimesFile} ]; then
    rm all_times.tsv
fi
tmpfile=$(mktemp)
for f in $(ls -1 times_*.txt); do
    t=${f#*_}
    conf=${t%.txt}
    #echo $conf
    awk "{
        carr[\$1, \$2]+=\$3
        earr[\$1, \$2]+=\$4
        cnt[\$1, \$2]+=1
    }
    END {
        for (key in carr) {
            split(key, keyarr, SUBSEP)
            printf(\"%s\t%s\t${conf}\t%s\t%s\n\", keyarr[1], keyarr[2], carr[key] / cnt[key], earr[key] / cnt[key])
        }
    }" "$f" >> "${tmpfile}" #| sort +0n -1
#    while IFS= read -r line; do
#
#    done < "$f"
done

printf "alg\trows\ttype\tcompile\texecute\n" > ${AllTimesFile}
sort "${tmpfile}" >> ${AllTimesFile}
rm "${tmpfile}"