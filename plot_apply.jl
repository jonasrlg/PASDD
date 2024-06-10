using LogicCircuits
using Graphs
using TikzGraphs

function Graphs.DiGraph(vtree::Vtree)
    N = num_nodes(vtree)
    g = DiGraph(N)
    nv = num_variables(vtree)
    id = nv
    dict = Dict{PlainVtreeInnerNode, Int}()
    if id < N 
        dict[vtree] = (id += 1)
    end

    convert_rec(v::PlainVtreeLeafNode) = ()
    convert_rec(v::PlainVtreeInnerNode) = begin
        foreach(children(v)) do c
            c_id = isleaf(c) ? variable(c) : dict[c] = (id += 1)
            add_edge!(g, dict[v], c_id)
            convert_rec(c)
        end
    end

    convert_rec(vtree)
    @assert id == N
    label = [["$i" for i in 1 : nv];fill(".", nv - 1)]
    g, label
end

function getVal(d::Dict, k; default="error")
    return get(d, k, default)
end

function Graphs.DiGraph(lc::LogicCircuit; on_edge=noop, on_var=noop)
    nv = num_variables(lc)
    nn = num_nodes(lc)
    g = DiGraph(nn)
    id = 0
    dict = Dict{LogicCircuit, Int}()
    label = Vector{String}(undef, nn)
    dict[lc] = (id += 1)
    
    add_label!(g, dict, c::LogicCircuit) = begin
        label[dict[c]] = 
            if isliteralgate(c) getVal(names_dict, literal(c), default="error")
        elseif istrue(c)  "T"
        elseif isfalse(c)  "F"
        elseif is⋁gate(c) "⋁"
        else "⋀"
        end
    end

    if on_var == noop 
        on_var = add_label!
    end
    
    foreach_down(lc) do n
        on_var(g, dict, n)
        if has_children(n)
            foreach(children(n)) do c
                c_id = haskey(dict, c) ? dict[c] : dict[c] = (id += 1)
                add_edge!(g, dict[n], c_id)
                on_edge(g, dict, n, c, dict[n], c_id)
            end
        end
    end
    g, label
end

function myPlot(lc::LogicCircuit; simplify=false) 
    if simplify
        lc = propagate_constants(LogicCircuit(lc))
    end
    g, label = Graphs.DiGraph(lc)
    TikzGraphs.plot(g, label, node_style="draw, circle")
end

manager = SddMgr(3, :balanced)
a, b, c = pos_literals(Sdd, manager, 3)
names_dict = Dict(1 => "A", -1 => "¬A", 2 => "B", -2 => "¬B", 3 => "C", -3 => "¬C")
c1 = a ∧ b
c2 = ¬a ∨ ¬c
c = c1 ∧ c2

t = myPlot(c; simplify=true)
t1 = myPlot(c1; simplify=true)
t2 = myPlot(c2; simplify=true)

using TikzPictures

TikzPictures.save(PDF("sdd_apply1.pdf"), t1)
TikzPictures.save(PDF("sdd_apply2.pdf"), t2)
TikzPictures.save(PDF("sdd_apply.pdf"), t)
