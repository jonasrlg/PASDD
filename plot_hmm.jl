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


if (ARGS[1] == "r") 
    manager = SddMgr(5, :rightlinear)
    sufix = "_right"
elseif (ARGS[1] == "l")
    manager = SddMgr(5, :leftlinear)
    sufix = "_left"
end

b, a, x, y10, y11 = pos_literals(Sdd, manager, 5)
names_dict = Dict(1 => "b(1)", -1 => "¬b(1)", 2 => "a(1)", -2 => "¬a(1)", 3 => "x(1)", -3 => "¬x(1)", 4 => "y(1,0)", -4 => "¬y(1,0)", 5 => "y(1,1)", -5 => "¬y(1,1)")
x_rule = x ⇔ a
y10_body = b ∧ ¬x
y10_bodies = y10_body ∨ x
y10_rule = y10 ⇔ (y10_bodies ∧ ¬y11)
y11_body = ¬b ∧ ¬x
y11_bodies = y11_body ∨ x
y11_rule = y11 ⇔ (y11_bodies ∧ ¬y10)
c = x_rule ∧ y10_rule ∧ y11_rule

t = myPlot(c; simplify=true)

using TikzPictures

output = "hmm" * sufix * ".pdf"
TikzPictures.save(PDF(output), t)
