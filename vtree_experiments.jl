using LogicCircuits
using ProgressBars

function maximum_abs(vector)
    return maximum(abs.(vector))
end

function minimum_abs(vector)
    return minimum(abs.(vector))
end

function compile(file_prefix; vtree_type=:balanced, output_file="sdd_compilation_results.txt")
    heads = parse.(Int64, readlines(file_prefix * ".head"))
    aux = split.(readlines(file_prefix * ".body"), " ")
    bodies = [parse.(Int64, b) for b in aux]
    
    println("Compiling $file_prefix")
    println("Heads: $heads")
    println("Bodies: $bodies")
    println("Max on Heads: $(maximum(heads))")
    println("Max on Bodies: $(maximum(maximum_abs.(bodies)))")
    println("Min on Heads: $(minimum(heads))")
    println("Min on Bodies: $(minimum(minimum_abs.(bodies)))")
    
    unique_heads = unique(heads)
    println("Unique heads: $unique_heads")
    abs_bodies = abs.(vcat(bodies...))
    println("Unique abs_bodies: $abs_bodies")
    unique_bodies = unique(abs_bodies)
    all_indices = unique(vcat(unique_heads, unique_bodies))
    println("All indices: $all_indices")
    max_index = length(all_indices)
    println("Number of different (unique) variables: $max_index")
    manager = SddMgr(max_index, vtree_type)

    index_dic = Dict()
    for (i, val) in enumerate(all_indices)
        index_dic[val] = i
    end
    println("Index dictionary: $index_dic")

    pos_vars = pos_literals(Sdd, manager, max_index)
    neg_vars = neg_literals(Sdd, manager, max_index)
    


    nrules = length(heads)
    # Current index for the head
    curr_index = heads[1] 
    # Stores the final circuit
    circuit = SddConstantNode(true)
    # Disjunction of body clauses for the current head
    body_circuit = SddConstantNode(false) 
    elapsed_compilation=@elapsed for i in ProgressBar(1:nrules)
        head = heads[i]
        if (head > curr_index)
            # A head occurs if and only if one of its bodies 
            # occurs. Hence, we conjoin the circuit of the head 
            # with the inal circuit.
            circuit &= pos_vars[index_dic[curr_index]] ⇔ body_circuit
            curr_index = head
            # Reset body circuit
            body_circuit = SddConstantNode(false)
        end
        clause_circuit = SddConstantNode(true)
        for j in bodies[i]
            if (j > 0)
                clause_circuit &= pos_vars[index_dic[j]]
            elseif (j < 0)
                clause_circuit &= neg_vars[index_dic[-j]]
            else
                println("Error: Zero in body")
            end
        end
        body_circuit |= clause_circuit
    end
    
    # Conjoin with the last head circuit, resulting in the 
    # final circuit (representing the entire program)
    circuit &= pos_vars[index_dic[curr_index]] ⇔ body_circuit
    
    if (¬issmooth(circuit))
        println("Smoothing circuit with current size: $(sdd_size(circuit)) and  model count: $(model_count(circuit))")
        elapsed_compilation+=@elapsed circuit = smooth(circuit)
    end
    
    circuit_edges = num_edges(circuit)
    circuit_nodes = num_nodes(circuit)
    println("Circuit size: nodes - $circuit_nodes / edges - $circuit_edges")
    mc = model_count(circuit)
    println("Model count: $mc")
    println("Compilation time: $(elapsed_compilation)")
    compression_rate = round(mc / circuit_edges , digits=3)

    split_file = split(file_prefix, "/")
    file_name = split_file[length(split_file)]

    results_file =  open(output_file,"a")
    write(results_file, "$circuit_nodes & $circuit_edges & $elapsed_compilation\n")
end

vree_type = :balanced
output_file = "sdd_compilation_results.txt"

if ((length(ARGS) <= 1) || (length(ARGS) > 3))
    println("Usage: julia sdd_compilation.jl <file_prefix> [b/r/l/r] [output_file]")
    exit(1)
end
if length(ARGS) > 1
    vtree_type_str = ARGS[2]
    vtree_dict = Dict([("b", :balanced), ("r", :rightlinear), ("l", :leftlinear), ("rand", :random)])
    vtree_type = get(vtree_dict, vtree_type_str, :balanced)
    println("Vtree type: $vtree_type_str = $vtree_type")
end
if length(ARGS) > 2
    output_file = ARGS[3]
    println("Output file: $output_file")
end

compile(ARGS[1]; vtree_type=vtree_type, output_file=output_file)
