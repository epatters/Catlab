using Catlab.CategoricalAlgebra
using Catlab.Present
using Catlab.Theories
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.Graphs
using DataStructures: OrderedDict

"""
Reference: CT for computing science:
https://www.math.mcgill.ca/triples/Barr-Wells-ctcs.pdf

We are concerned with "Regular" sketches, where no node is the vertex of more
than one cone.

Here are also interesting examples + explanation of connection to Essentially
Algebraic Theories: https://www.math.mcgill.ca/barr/papers/sketch.pdf

Section 7.7 describes how this is essentially the same as the
syntactic version. Maybe useful to help convert between.

FD theories add cocones and model sum types. This goes beyond what we want to
model with a GAT, though may be interesting to consider for the model
enumeration project.

Also check Fiore: categorical semantics of dependent type theory
"""

"""
Section 7.3+10.1.3 Shorthand Caveats:
2. nodes a×b×c IMPLICITLY have a cone with projection legs.
3. likewise nodes labeled 1 are implicitly terminal (empty base limit)
4. arrows labeled ⟨f₁,f₂,...⟩:a->b₁×b₂×... , where edges fₙ all share a codomain, are implicitly assumed to have diagrams:
                fᵢ
              a ⟶ bᵢ
 ⟨f₁,f₂,...⟩  ↓   ↗ pᵢ
          b₁×b₂×...

5. arrows labeled f₁×f₂×...: a₁×a₂×...->b₁×b₂×...
are implicitly assumed to have diagrams:
                 pᵢ
      a₁×a₂×... --> aᵢ
f₁×f₂×...↓          ↓ fᵢ
      b₁×b₂×... --> bᵢ
                pᵢ

6. diagrams of the form of two paths with a common start and end can be specified as s₁;s₂;... = t₁;t₂;...
7. If one leg of the above paths is empty, we require an identity arrow and set the other path to be equal to it.
8. Nodes labeled a×ᵧb implies the existence of a cone
        a×ᵧb
       ↙   ↘
      a→ γ ←b
9. an arrow s: a↣b (i.e. s is monic) implies the existence of a cone
        a
   id ╱ | ╲ id
    ↙   ↓s  ↘
   a ⟶ b ⟵ a
     s     s
"""

"""
Combinatorial representation of data of a finite limit sketch

It is not yet clear whether this captures everything we want to capture, e.g.
we expect that the diagrams are trees without cycles so that there are only a
finite number of equations to check, but there could be alternative styles of
diagrams that would work better in a CSet.
"""
@present TheoryFLSketch(FreeSchema) begin
  # Main Graph
  (V, E)::Ob
  (src, tgt)::Hom(E,V)

  # Diagrams
  (Dv, De)::Ob
  root::Hom(V, Dv)
  (dSrc, dTgt)::Hom(De,Dv) # graph data of all diagrams (disjoint union)
  dV::Hom(Dv, V) # Partition union of graphs
  dE::Hom(De, V) # via map into V

  # Cones
  (Cone, Leg, Cv, Ce)::Ob
  (cSrc, cTgt)::Hom(Ce,Cv) # graph data of all cone bases (disjoint union)
  apex::Hom(Cone, V)    # Which object is the cone vertex?
  legCone::Hom(Leg, Cone) # Which Cone does this leg belong to?
  legTgt::Hom(Leg, Cv)
  legEdge::Hom(Leg, E)
  cV::Hom(Cv, Cone)    # Partition cone graph
  cE::Hom(Ce, Cone)    # via map into Cone

  # Homorphisms data
  cvMap::Hom(Cv, V)
  ceMap::Hom(Ce, E)
  dvMap::Hom(Dv, V)
  deMap::Hom(De, E)

  # Diagrams/cones don't touch each other
  compose(cSrc, cV) == cE    # EQUATION ON Ce
  compose(cTgt, cV) == cE    # EQUATION ON Ce
  compose(dSrc, dV) == dE    # EQUATION ON De
  compose(dTgt, dV) == dE    # EQUATION ON De

  # Root of each diagram is the right vertex
  compose(root, dV) == id(V)  # EQUATION ON V

  # Homomorphism properties
  compose(legEdge, src) == compose(legCone, apex) # EQUATION ON CONE LEGS
  compose(legEdge, tgt) == compose(legTgt, cvMap) # EQUATION ON CONE LEGS
  compose(deMap, src) == compose(dSrc, dvMap) # EQUATION ON De
  compose(deMap, tgt) == compose(dTgt, dvMap) # EQUATION ON De
  compose(ceMap, src) == compose(cSrc, cvMap) # EQUATION ON Ce
  compose(ceMap, tgt) == compose(cTgt, cvMap) # EQUATION ON Ce
end;

"""Append either _src or _tgt to a symbol"""
function add_srctgt(fk::Symbol, src::Bool)::Symbol
  return Symbol(string(fk) * "_" * (src ? "src" : "tgt"))
end
"""Append both _src and _tgt to a symbol"""
function add_srctgt(fk::Symbol)::Pair{Symbol, Symbol}
  return add_srctgt(fk, true) => add_srctgt(fk, false)
end

if !isdefined(Main, :Fls) # because we are currently running this as a script
const Fls = CSetType(TheoryFLSketch, index=[
  :src, :tgt, :dSrc, :dV, :dE, :cV, :cE, :apex, :legCone]);
end

"""Edges and vertices labeled by symbols"""
@present TheoryLabeledGraph <: TheoryGraph begin
  Label::Data
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;
# we don't want unique_index=[:vlabel, :elabel] because we want to use
# labels to specify homomorphisms which may not be injective
const LabeledGraph = ACSetType(TheoryLabeledGraph, index=[:src,:tgt]){Symbol};

"""Annotate a FLS CSet with labels"""
struct LabeledFLS
  fls::Fls
  labels::Pair{Vector{Symbol}, Vector{Symbol}} # label nodes and edges
  function LabeledFLS(f::Fls, l::Pair{Vector{Symbol}, Vector{Symbol}})
    for labs in l
        length(labs)==length(Set(labs)) || error("labels must be unique: $labs")
    end
    length(l[1]) == nparts(f, :V) || error("incorrect # of vlabels $(l[1])")
    length(l[2]) == nparts(f, :E) || error("incorrect # of elabels $(l[2])")
    return new(f, l)
  end
end

"""Access vertex labels of graph underlying FLS"""
function vi(fls::LabeledFLS, v::Symbol)::Int
  return findfirst(==(v), fls.labels[1])
end

"""Access edge labels of graph underlying FLS"""
function ei(fls::LabeledFLS, v::Symbol)::Int
  return findfirst(==(v), fls.labels[2])
end

"""No cones, trivial diagrams"""
function FLSinit(g::LabeledGraph)::LabeledFLS
  fls = Fls()
  add_parts!(fls, :V, nv(g))
  add_parts!(fls, :Dv, nv(g), dV=1:nv(g), dvMap=1:nv(g))
  add_parts!(fls, :E, ne(g))
  set_subpart!(fls, :src, g[:src])
  set_subpart!(fls, :tgt, g[:tgt])
  set_subpart!(fls, :root, 1:nv(g))
  return LabeledFLS(fls, g[:vlabel] => g[:elabel])
end

"""Get the commutivity diagram of a FLS"""
function get_diagram(fls::LabeledFLS, root::Symbol)::LabeledGraph
  res = LabeledGraph()
  f = fls.fls
  rooti = vi(fls, root)
  nodes = f.indices[:dV][rooti]
  edges = f.indices[:dE][rooti]
  nodedict = Dict([i=>e for (e, i) in enumerate(nodes)])
  vlab = [fls.labels[1][f[:dvMap][i]] for i in nodes]
  add_parts!(res, :V, length(nodes), vlabel=vlab)
  edata = [(e, f[:dSrc][e], f[:dTgt][e]) for e in edges]
  for (e, s, t) in edata
    elab = fls.labels[2][f[:deMap][e]]
    add_part!(res, :E, src=nodedict[s], tgt=nodedict[t], elabel=elab)
  end
  return res
end

"""Get whole cone (apex last index), or just the base of of the cone"""
function get_cone(fls::LabeledFLS, apex::Symbol, base::Bool=false
         )::Union{Nothing, LabeledGraph}
  f = fls.fls
  apexes = fls.labels[1][f[:apex]]
  cone_ind = findfirst(==(apex), apexes)
  if cone_ind === nothing
    return nothing
  end
  res = LabeledGraph()
  cv, ce = [f.indices[x][cone_ind] for x in [:cV, :cE]]
  reind = [findfirst(==(i), cv) for i in 1:(isempty(cv) ? 0 : maximum(cv))]
  vlab = fls.labels[1][f[:cvMap][cv]]
  add_parts!(res, :V, length(cv), vlabel=vlab)

  elab = fls.labels[2][f[:ceMap][ce]]
  es = reind[f[:cSrc][ce]]
  et = reind[f[:cTgt][ce]]
  add_parts!(res, :E, length(ce), elabel=elab, src=es, tgt=et)
  if !base
    pex = add_part!(res, :V, vlabel=fls.labels[1][f[:apex][cone_ind]])
    legs = f.indices[:legCone][cone_ind]
    el = fls.labels[2][f[:legEdge][legs]]
    tg = reind[f[:legTgt][legs]]
    add_parts!(res, :E, length(legs), elabel=el, src=pex, tgt=tg)
  end
  return res
end

"""Extract the underlying graph (no diagrams/cones)"""
function get_schema(fls::LabeledFLS)::LabeledGraph
  res = LabeledGraph()
  add_parts!(res, :V, length(fls.labels[1]), vlabel=fls.labels[1])
  add_parts!(res, :E, length(fls.labels[2]), src=fls.fls[:src], tgt=fls.fls[:tgt], elabel=fls.labels[2])
  return res
end

"""Get all commuting paths starting at a particular node"""
function all_paths(fls, root::Symbol)::OrderedDict{Vector{Symbol}, Int}
  res = OrderedDict{Vector{Symbol}, Int}()
  rooti = vi(fls, root)
  f = fls.fls
  rootind = f[:root][rooti]
  stack = Tuple{Int,Vector{Symbol}}[(rootind, [])]
  seen = Set()
  while !isempty(stack)
    currnode, currpath = pop!(stack)
    res[currpath] = currnode
    if !(currnode in seen)
      push!(seen, currnode)
      for e in f.indices[:dSrc][currnode]
        orig_e = f[:deMap][e]
        e_symbol = fls.labels[2][orig_e]
        nextnode = f[:dTgt][e]
        push!(stack, (nextnode, vcat(currpath, [e_symbol])))
      end
    end
  end

  return res
end

"""
Add a diagram where the first node is the root. Labels indicate homomorphism.
"""
function add_diagram!(fls::LabeledFLS, d::LabeledGraph)::Nothing
  rootless = LabeledGraph()
  add_parts!(rootless, :V, nv(d), vlabel=d[:vlabel])
  for (e, (ss, tt)) in enumerate(zip(d[:src], d[:tgt]))
    if tt != 1
      add_part!(rootless, :E, elabel=d[:elabel][e], src=ss, tgt=tt)
    end
  end
  topological_sort(rootless)  # must be acyclic, after removing loops to root
  root = d[:vlabel][1]
  rooti = vi(fls, root)
  # paths that already exist in the FLS
  location = all_paths(fls, root)
  f = fls.fls
  seen = Dict{Int, Int}() # index in d => index in FLS diagram
  # (index in d, index in FLS diagram, path in d)
  stack = Tuple{Int,Int,Vector{Symbol}}[(1, f[:root][rooti], Symbol[])]
  while !isempty(stack)
    dnode, currnode, currpath = pop!(stack)
    seen[dnode] = currnode
    vlabel = d[:vlabel][dnode]
    nextedges = d.indices[:src][dnode]
    for e in nextedges
      elab = d[:elabel][e]
      orig_edge = ei(fls, elab)
      nextpath = vcat(currpath, [elab])
      seenflag = false
      if haskey(location, nextpath)
        nextnode = location[nextpath]
      else
        next_d = d[:tgt][e]
        next_orig = vi(fls, d[:vlabel][next_d])
        if haskey(seen, next_d)
          nextnode = seen[next_d]
          seenflag=true
        else
          nextnode = add_part!(f, :Dv, dV=rooti, dvMap=next_orig)
        end
        add_part!(f, :De, dSrc=currnode, dTgt=nextnode,
        dE=rooti, deMap=orig_edge)
      end
      if !seenflag
        push!(stack, (d[:tgt][e], nextnode, nextpath))
      end
    end
  end
end
"""
Add a cone, assuming the last vertex of the graph is the apex
"""
function add_cone!(fls::LabeledFLS, c::LabeledGraph)::Nothing
  f = fls.fls
  conetgt = vi(fls, c[:vlabel][end])
  prevcones = vcat(f.indices[:apex]...)
  @assert !(conetgt in prevcones) "No more than one cone on a given vertex"
  cone_id = add_part!(f, :Cone)
  vert_ids = add_parts!(f, :Cv, nv(c)-1, cV=cone_id,
              cvMap=[vi(fls, l) for l in c[:vlabel][1:end-1]])
  nonlegs = [i for (i, t) in enumerate(c[:src]) if t!=nv(c)]
  legs  = [i for (i, t) in enumerate(c[:src]) if t==nv(c)]
  emap, lemap = [[ei(fls, l) for l in c[:elabel][x]]
           for x in [nonlegs, legs]]
  esrc = vert_ids[c[:src][nonlegs]]
  etgt, letgt = [vert_ids[c[:tgt][x]] for x in [nonlegs, legs]]
  add_parts!(f, :Ce, length(nonlegs), cE=cone_id, ceMap=emap, cSrc=esrc, cTgt=etgt)
  set_subpart!(f, cone_id, :apex, vi(fls, c[:vlabel][nv(c)]))
  add_parts!(f, :Leg, length(legs), legCone=cone_id,
         legEdge=lemap, legTgt=letgt)
  return nothing
end


"""
Create a linear sketch (no cones) based on a CSet presentation
"""
function catpres_to_linear(pres::Presentation)::LabeledFLS
  obs = pres.generators[:Ob]
  homs = pres.generators[:Hom]
  vlab = [x.args[1] for x in obs]
  odict = Dict([o => i for (i, o) in enumerate(obs)])
  idsymbs = [Symbol("_id_"*string(v)) for v in vlab]
  elab = vcat([x.args[1] for x in homs], idsymbs)
  # Create initial graph
  g = LabeledGraph()
  n, nh = length(vlab), length(homs)
  add_parts!(g, :V, n, vlabel=vlab)
  srcs = vcat([odict[h.type_args[1]] for h in homs], 1:n)
  tgts = vcat([odict[h.type_args[2]] for h in homs], 1:n)
  add_parts!(g, :E, nh+n, src=srcs, tgt=tgts, elabel=elab)
  fls = FLSinit(g)
  # Add diagrams
  for (p1, p2) in pres.equations
    d = paths_to_diagram(p1, p2)
    add_diagram!(fls, d)
  end
  return fls
end

"""Create a diagram from a path equality"""
function paths_to_diagram(p1, p2)::LabeledGraph
  d = LabeledGraph()
  root = p1.type_args[1].args[1]
  add_part!(d, :V, vlabel=root)
  function add_path!(start::Bool, p)::Nothing
    typ = typeof(p).parameters[1]
    if typ == :id
      if start
        tgt = add_part!(d, :V, vlabel=root)
      else
        tgt = nparts(d, :V)
      end
      elab = Symbol("_id_"*string(root))
      add_part!(d, :E, src=1, tgt=tgt, elabel=elab)
    elseif typ == :compose
      homs = p.args
      curr = 1
      if start
        last = length(homs) + 1
      else
        last = nparts(d, :V)
      end
      for (i, hom) in enumerate(homs)
        add_part!(d, :V, vlabel=hom.type_args[2].args[1])
        if i == length(homs)
          tgt = last
        else
          tgt = curr+1
        end
        add_part!(d, :E, src=curr, tgt=tgt, elabel=hom.args[1])
        curr += 1
      end
    elseif typ == :generator
      if start
        last = add_part!(d, :V, vlabel=p.type_args[2].args[1])
      else
        last = nparts(d, :V)
      end
      add_part!(d, :E, src=1, tgt = last, elabel=p.args[1])
    else
      @assert false "Not prepared for type $typ"
    end
    return nothing
  end
  add_path!(true, p1)
  add_path!(false, p2)
  return d
end
