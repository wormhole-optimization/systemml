#!/usr/bin/env bash
set -o errexit
set -o pipefail
set -o nounset
# set -o xtrace

dir="."

for dotfile in "${dir}"/*.dot; do
    pdffile="${dotfile%.dot}.pdf"

    if [ "${dotfile}" -nt "${pdffile}" ]; then
        dot -Tpdf "${dotfile}" -o "${pdffile}"
    fi
done

