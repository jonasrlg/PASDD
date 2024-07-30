import pysdd

def maximum_abs(vector):
    return maximum(abs(vector))

def minimum_abs(vector):
    return minimum(abs(vector))

def compile(file_prefix, vtree_type="balanced", output_file="sdd_compilation_output.txt")
    heads = parse.(Int64, readlines(file_prefix * ".head"))
    aux = split.(readlines(file_prefix * ".body"), " ")
    bodies = [parse.(Int64, b) for b in aux]

    print("Compiling $file_prefix")
    print("Heads: $heads")
    print("Bodies: $bodies")
    print("Max on Heads: $(maximum(heads))")
    print("Max on Bodies: $(maximum(maximum_abs.(bodies)))")
    print("Min on Heads: $(minimum(heads))")
    print("Min on Bodies: $(minimum(minimum_abs.(bodies)))")

    unique_heads = unique(heads)
    print("Unique heads: $unique_heads")
    abs_bodies = abs.(vcat(bodies...))
    print("Unique abs_bodies: $abs_bodies")
    unique_bodies = unique(abs_bodies)
    all_indices = unique(vcat(unique_heads, unique_bodies))
    print("All indices: $all_indices")
    max_index = length(all_indices)
    print("Number of different (unique) variables: $max_index")
    manager = SddMgr(max_index, vtree_type)

    index_dic = Dict()
    for (i, val) in enumerate(all_indices)
        index_dic[val] = i
    end
    print("Index dictionary: $index_dic")

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
                print("Error: Zero in body")
            end
        end
        body_circuit |= clause_circuit
    end

    # Conjoin with the last head circuit, resulting in the
    # final circuit (representing the entire program)
    circuit &= pos_vars[index_dic[curr_index]] ⇔ body_circuit

    if (¬issmooth(circuit))
        print("Smoothing circuit with current size: $(sdd_size(circuit)) and  model count: $(model_count(circuit))")
        elapsed_compilation+=@elapsed circuit = smooth(circuit)
    end

    circuit_edges = num_edges(circuit)
    circuit_nodes = num_nodes(circuit)
    print("Circuit size: nodes - $circuit_nodes / edges - $circuit_edges")
    mc = model_count(circuit)
    print("Model count: $mc")
    print("Compilation time: $(elapsed_compilation)")
    compression_rate = round(mc / circuit_edges , digits=3)

    split_file = split(file_prefix, "/")
    file_name = split_file[length(split_file)]

    results_file =  open(output_file,"a")
    write(results_file, "$file_name & $circuit_nodes & $circuit_edges & $elapsed_compilation & $mc & $compression_rate\n")

    t = plot(circuit; simplify=true)
    TikzPictures.save(PDF("circuit_$file_name.pdf"), t)
end

vree_type = "balanced"
output_file = "sdd_compilation_output.txt"
names_dict = {1: "b(1)", -1: "¬b(1)", 2: "a(1)", -2: "¬a(1)", 3: "x(1)", -3: "¬x(1)", 4: "y(1,0)", -4: "¬y(1,0)", 5: "y(1,1)", -5: "¬y(1,1)"}
if ((length(ARGS) <= 1) || (length(ARGS) > 3))
    print("Usage: julia sdd_compilation.jl <file_prefix> [b/r/l/r] [output_file]")
    exit(1)
end
if length(ARGS) > 1
    vtree_type_str = ARGS[2]
    vtree_dict = Dict([("b", :balanced), ("r", :rightlinear), ("l", :leftlinear), ("rand", :random)])
    vtree_type = get(vtree_dict, vtree_type_str, :balanced)
    print("Vtree type: $vtree_type_str = $vtree_type")
end
if length(ARGS) > 2
    output_file = ARGS[3]
    print("Output file: $output_file")
end

compile(ARGS[1]; vtree_type=vtree_type, output_file=output_file)
