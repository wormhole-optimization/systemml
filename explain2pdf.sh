#!/usr/bin/env bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace

# This script parses the explain output of a Hop Dag, writes out a DOT file graphing it, 
# and generates a PDF file displaing the DOT graph.

if [ "$#" -eq 0 ]; then
  echo "Usage: $0 <file1> ... <fileN>"
fi

#echo $@
s=""
for f in "$@"; do
  s="$s '$f'"
done
s="mvn exec:java -Dexec.mainClass=org.apache.sysml.utils.ParseExplain -Dexec.args=\"${s:1:${#s}-1}\""

echo ${s}
eval $s

for f in "$@"; do
  dotfile="${f%.txt}.dot"
  pdffile="${dotfile%.dot}.pdf"
  if [ "${dotfile}" -nt "${pdffile}" ]; then
      dot -Tpdf "${dotfile}" -o "${pdffile}"
      echo Wrote $pdffile
  fi
done
