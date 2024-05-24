#! /usr/bin/env bash

program_name=$1

rm programs/$program_name/*.head
rm programs/$program_name/*.body
rm programs/$program_name/*.cnf

for entry in "programs/$program_name"/*.pasp; do
    instance=$(echo $entry | cut -d'/' -f 3 | cut -d'.' -f 1)
    echo "Parsing $instance"
    python3 sdd_parser.py $entry
done
