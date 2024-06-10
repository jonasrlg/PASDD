#! /usr/bin/env bash

programs_dir=$1

rm programs/$programs_dir/sdd_compilation_results.txt

echo $(ls programs/$programs_dir/*.pasp)

for entry in $(ls programs/$programs_dir/*.pasp); do
    instance=$(echo $entry | cut -d'.' -f1)
    echo "Compiling $instance"
    sdd=$(julia sdd_compilation.jl $instance)
    sdd_size=$(echo $sdd | cut -d ' ' -f1)
    sdd_time=$(echo $sdd | cut -d ' ' -f2)
    sdd_model_count=$(echo $sdd | cut -d ' ' -f3)
    sdd_compression=$(echo $sdd | cut -d ' ' -f4)
    echo "$instance $sdd_size $sdd_time $sdd_model_count $sdd_compression" >> programs/$programs_dir/sdd_compilation_results.txt
done
