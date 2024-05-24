#! /usr/bin/env bash

programs_dir=$1

rm sdd_compilation_results.txt

echo $(ls programs/$programs_dir/*.pasp)

for entry in $(ls programs/$programs_dir/*.pasp); do
    instance=$(echo $entry | cut -d'.' -f1)
    echo "Compiling $instance"
    sdd=$(julia sdd_compilation.jl $instance) > /dev/null
done
