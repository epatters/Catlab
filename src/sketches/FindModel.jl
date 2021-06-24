include(joinpath(@__DIR__, "FLS.jl"))
using Base.Iterators: product as cartprod
using Catlab.CategoricalAlgebra.FinSets: preimage

"""
A key data structure in this file is a partial model. This is replacing a C-Set
with a C-Rel; we allow a morphism to map from one element to multiple targets.
The model is COMPLETE when each element has exactly one arrow per morphism.
It is INCONSISTENT if any element has zero arrows. A model we know nothing about
has a complete digraph for each morphism. Partial models are represented as
CSets with a particular schema (morphisms are replaced with relations, i.e.
objects a pair of morphisms: FK_src and FK_tgt).
"""

"""
For p1=p2, if p1 is completely known but p2 is only known up to penultimate
value, then we learn new info.
"""
function propagate_diagram!(fls::LabeledFLS, cset::CSet)::Nothing
  for sym in fls.labels[1]
    propagate_diagram!(fls, cset, sym)
  end
  return nothing
end

"""
Use diagrams to rule out certain possibilities
"""
function propagate_diagram!(fls::LabeledFLS, cset::CSet, sym::Symbol)::Nothing
  paths = all_paths(fls, sym)
  verts = sort(collect(Set(values(paths))))
  vertsyms = [fls.labels[1][fls.fls[:dvMap][v]] for v in verts]
  to_delete = Dict{Symbol, Set{Int}}([l=>Set{Int}() for l in fls.labels[2]])
  vals = Dict{Vector{Symbol},Vector{Set{Int}}}(
      [Symbol[] => Set{Int}[Set{Int}([i]) for i in 1:nparts(cset, sym)]])
  for (p, _) in filter(x->!isempty(x[1]), paths)
    tail, head = p[1:end-1], p[end]
    head_src, head_tgt = add_srctgt(head)
    valsp = Set{Int}[union([Set{Int}(
      cset[head_tgt][cset.indices[head_src][i]]) for i in iset]...)
           for iset in vals[tail]]
    vals[p] = valsp
  end
  # for each junction, check if any penultimate node is completely determined
  junctions = filter(x-> count(==(x[1]), values(paths)) > 1,
                     collect(zip(verts, vertsyms)))
  for (j, jsym) in junctions
    jpaths = [p for (p, v) in collect(paths) if v == j]
    for i in 1:nparts(cset, jsym)  # consider paths starting at each elem
      alljvals = [vals[jpath][i] for jpath in jpaths]
      jvals = union(Set{Int}(), [jv for jv in alljvals if length(jv)==1]...)
      @assert length(jvals) in [0, 1]
      if !isempty(jvals) # we know what value to set this path equal to
        jval = pop!(jvals)
        # can only use this info if the PENULTIMATE path is unambiguous
        for jpath in filter(!isempty, jpaths)
          tail, head = jpath[1:end-1], jpath[end]
          head_src, head_tgt = add_srctgt(head)
          if length(vals[tail][i])==1
            penult_val = collect(vals[tail][i])[1]
            # keep just the FK that goes to jval
            all_fks = cset.indices[head_src][penult_val]
            bad_fks = [fk for fk in all_fks if cset[head_tgt][fk] != jval]
            union!(to_delete[head], Set(bad_fks))
          end
        end
      end
    end
  end
  rem!(cset, to_delete)
end


"""Get the indices that satisfy equations starting at a particular node"""
function check_diagram(fls::LabeledFLS, cset::CSet, sym::Symbol;
                       cset_is_crel::Bool=false)::Set{Int}
  cset_ = cset_is_crel ? cset : cset_to_crels(fls, cset)
  dia = dia_to_crel(fls, get_diagram(fls, sym))
  hs = homomorphisms(dia, cset_)
  sat_inds = [h.components[sym](1) for h in hs]
  return Set(sat_inds)
end


"""
Coerce a LABELED GRAPH diagram into a C-Rel. The existence of a homomorphism
from this CRel into a partial model CRel indicates that the diagram is
satisfiable for some choice of FKs
"""
function dia_to_crel(fls::LabeledFLS, dia::LabeledGraph)::CSet
  res = crels(fls)()
  ref = Dict{Pair{Symbol, Int}, Int}()
  for (i, lab) in enumerate(dia[:vlabel])
    ind = add_part!(res, lab)
    ref[lab => i]=ind
  end
  for (e, ss, tt) in zip(dia[:elabel], dia[:src], dia[:tgt])
    slab, tlab = dia[:vlabel][[ss,tt]]
    s, t = add_srctgt(e)
    args = Dict([s => ref[slab => ss], t=> ref[tlab => tt]])
    add_part!(res, e; args...)
  end
  return res
end

"""
Take a real CSet and construct CRel with exactly one FK value per PK.
"""
function cset_to_crels(fls::LabeledFLS, cset::CSet)::CSet
  res = crels(fls)()
  for ob in fls.labels[1]
    add_parts!(res, ob, nparts(cset, ob))
  end
  for (i, ss) in enumerate(fls.fls[:src])
    isym = fls.labels[2][i]
    s, t = add_srctgt(isym)
    for src_ind in 1:nparts(cset, fls.labels[1][ss])
      sym = string(isym)
      tval = length(sym)>3 && sym[1:4] == "_id_" ? src_ind : cset[isym][src_ind]
      args = Dict([s=>src_ind, t=>tval])
      add_part!(res, isym; args...)
    end
  end
  return res
end

"""
Cone constraints can allow us to infer things about a partial model
"""
function propagate_cone!(fls::LabeledFLS, cset::CSet)::Nothing
  return nothing # to do
end

"""
Return false if unsat

Demand that every apex has at least one base (# of bases could
potentially decrease as we remove FKs).

If the legs have been finalized, then we demand every apex has
exactly one base

For apexes that have been finalized (have a determinate base)
then we check that these are unique.
"""
function check_cone(fls::LabeledFLS, cset::CSet)::Bool
  for sym in fls.labels[1]
    if !check_cone(fls, cset, sym)
      return false
    end
  end
  return true
end


"""
Check if every edge in a diagram is fully determined in a partial model
"""
function check_base_final(fls::LabeledFLS, crel::CSet, base::LabeledGraph)::Bool
  ns = n_fks(fls, crel)
  for e in Set(base[:elabel])
    for n in ns[e]
      if n != 1
        return false
      end
    end
  end
  return true
end

"""
Return true if a cone is satisfiable by a partial model
"""
function check_cone(fls::LabeledFLS, cset::CSet, apx::Symbol)::Bool
  cone = get_cone(fls, apx, false)
  base = get_cone(fls, apx, true)
  n = nparts(cset, apx)
  if base === nothing
    return true # no cone
  end

  basefinal = check_base_final(fls, cset, base)
  basedia = dia_to_crel(fls, base)
  matches = [h.components for h in homomorphisms(basedia, cset)]
  if basefinal && length(matches) != n
    # println("base is final but $(length(matches)) != # of apexes ($n)")
    return false
  end
  apexes = [get_apexes(cset, apx, cone, h) for h in matches]
  all_apexes = union(Set{Int}(), apexes...)
  cover = length(all_apexes) == n
  if !cover
    return false  # there are elements in the apex component w/ no base
  end
  seen_base = Set()
  for i in 1:n
    known_base = []
    known = true
    for e in cone.indices[:src][nv(cone)]
      esrc, etgt = add_srctgt(cone[:elabel][e])
      leg = cset[etgt][cset.indices[esrc][i]]
      if length(leg) == 1
        push!(known_base, leg[1])
      else
        known = false
        break
      end
    end
    if known
      if known_base in seen_base
        # println("Duplicate base")
        return false
      else
        push!(seen_base, known_base)
      end
    end
  end
  return true
end

"""
Return potential apexes for a given base
"""
function get_apexes(cset::CSet, apx::Symbol, cone::ACSet, morph)::Set{Int}
  poss_apex_inds = Set(1:nparts(cset, apx))
  for e in cone.indices[:src][nv(cone)]
    esrc, etgt = add_srctgt(cone[:elabel][e])
    tgt = cone[:tgt][e]
    tgt_sym = cone[:vlabel][tgt]
    tgt_ind = findfirst(==(tgt), [i for (i,s) in enumerate(cone[:vlabel])
                                  if s == tgt_sym])
    tgt_in_cset = morph[tgt_sym](tgt_ind)
    intersect!(poss_apex_inds, cset[esrc][cset.indices[etgt][tgt_in_cset]])
  end
  return poss_apex_inds
end

"""CSet type of C-Rel"""
function crels(fls::LabeledFLS)::Type
  pres = Presentation(FreeSchema)
  nv = length(fls.labels[1])
  alledge = Symbol[]
  xobs = [Ob(FreeSchema, s) for s in vcat(collect(fls.labels)...)]
  for x in xobs
    add_generator!(pres, x)
  end
  for (i,(src, tgt)) in enumerate(zip(fls.fls[:src], fls.fls[:tgt]))
    s, t = add_srctgt(fls.labels[2][i])
    add_generator!(pres, Hom(s, xobs[nv+i], xobs[src]))
    add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt]))
    append!(alledge, [s,t])
  end
  return CSetType(pres, index=alledge)
end

"""Cset type associated with FLS graph"""
function fls_csettype(fls::LabeledFLS)::Type
  pres = Presentation(FreeSchema)
  xobs = [Ob(FreeSchema, s) for s in fls.labels[1]]
  for x in xobs
    add_generator!(pres, x)
  end
  for (isym,s, t) in zip(fls.labels[2], fls.fls[:src], fls.fls[:tgt])
    add_generator!(pres, Hom(isym, xobs[s], xobs[t]))
  end
  return CSetType(pres, index=fls.labels[2])
end


"""
Convert from CRel to CSet by making an arbitrary choice for each relation.
Result is unique if the partial model is full determined, and it will fail if
the model is inconsistent.
"""
function crels_to_cset(fls::LabeledFLS, crels::CSet)::CSet
  res = fls_csettype(fls)()
  for v in fls.labels[1]
    add_parts!(res, v, nparts(crels, v))
  end
  for e in fls.labels[2]
    esrc, etgt = add_srctgt(e)
    evec = crels[etgt][[x[1] for x in crels.indices[esrc]]]
    set_subpart!(res, e, evec)
  end
  return res
end



"""Yes or no, does a CSet/CRel satisfy the diagrams of the FLS"""
function check_diagrams(fls::LabeledFLS, cset::CSet, error::Bool=true;
            cset_is_crel::Bool=false)::Bool
  for s in fls.labels[1]
    sat_inds = check_diagram(fls, cset, s,
                             cset_is_crel=cset_is_crel)
    if length(sat_inds) != nparts(cset, s)
      bad = sort(collect(setdiff(1:nparts(cset,s), sat_inds)))
      if error
        @assert false "Equations for $s not satisfied by indices $bad"
      else
        return false
      end
    end
  end
  return true
end

"""
Given a CSet from a FreeSchema presentation (e.g. Reflexive Graph) and a CSet
(e.g. an arbitrary instance of Reflexive Graph) throw an error if the CSet
does not conform to the equations in the presentation.

Once equational information is stored in the CatDesc of the CSet, we will no
longer need to pass a presentation as well.
"""
function check_diagrams(p::Presentation, cset::CSet)::Nothing
  fls = catpres_to_linear(p)
  crel = cset_to_crels(fls, cset)
  check_diagrams(fls, crel, true)
  return nothing
end


"""Populate crel with total relations: all possibilities"""
function allposs(fls::LabeledFLS, consts::Vector{Int})::CSet
  crel = crels(fls)()
  for (i, c) in enumerate(consts)
    add_parts!(crel, fls.labels[1][i], c)
  end
  for (i, (s, t)) in enumerate(zip(fls.fls[:src], fls.fls[:tgt]))
    fs, ft = add_srctgt(fls.labels[2][i])
    for j in 1:consts[s]
      for k in 1:consts[t]
        args = Dict([fs => j, ft => k])
        add_part!(crel, fls.labels[2][i]; args...)
      end
    end
  end
  return crel
end

"""
Naive search, needs to be improved.
We propagate info (or fail) based on diagram and cone constraints. Then branch
on an arbitrary choice.
"""
function search(fls::LabeledFLS,
                consts::Vector{Int},
                n::Int=-1,
                guess::Union{Nothing,CSet}=nothing;
               )::Vector{CSet}
  # initialize
  @assert all(x->x>=0, consts)
  @assert length(consts) == length(fls.labels[1])
  seen, res = Set(), Set()
  init = guess===nothing ? allposs(fls, consts) : guess

  function search_rec(crel::CSet, depth::Int)::Nothing
    if length(res) == n
      return nothing
    end

    if !check_diagrams(fls, crel, false; cset_is_crel=true)
      return nothing
    end
    if !check_cone(fls, crel)
      return nothing
    end
    old = deepcopy(crel)
    propagate_diagram!(fls, crel)
    if crel!=old
      hsh = canonical_hash(crel)
      if hsh in seen
        return nothing
      else
        push!(seen, hsh)
        old = deepcopy(crel)
      end
    end
    propagate_cone!(fls, crel)
    if crel!=old
      hsh = canonical_hash(crel)
      if hsh in seen
        return nothing
      else
        push!(seen, hsh)
      end
    end

    lens = filter(x->!isempty(x[2]), n_fks(fls, crel))
    maxes = [k=>findmax(v) for (k, v) in collect(lens)]
    mins = [minimum(v) for (_, v) in collect(lens)]
    nmax = maximum([x[1] for (_, x) in maxes])

    if minimum(mins) < 1
      return nothing
    elseif nmax == 1
      push!(res, crel)
    else
      emax, maxind = [(k, v[2]) for (k, v) in maxes if v[1] == nmax][1]
      for i in 1:nmax # split on the largest FK
        newer_crel = choose(crel, maxind, emax, i)
        newhsh = canonical_hash(newer_crel)
        if !(newhsh in seen)
          push!(seen, newhsh)
          search_rec(newer_crel, depth+1)
        end
      end
    end
  return nothing
  end

  search_rec(init, 0)
  return collect(res)
end

"""
For each PK+FK combo, how many FKs have that source
"""
function n_fks(fls::LabeledFLS, crel::CSet)::Dict{Symbol, Vector{Int}}
  res = Dict{Symbol, Vector{Int}}()
  for edge_sym in fls.labels[2]
    fks = map(length, crel.indices[add_srctgt(edge_sym, true)])
    res[edge_sym] = fks
  end
  return res
end

"""
Remove elements from tables - does not change any fk indices
so is only valid for tables which have no arrows to them
OR removing the LAST indices of a table
"""
function rem!(crel::CSet, rem::Dict{Symbol, Set{Int}})::Nothing
  for (comp, reminds) in collect(rem)
    rem_parts!(crel, comp, sort(collect(reminds)))
  end
  return nothing
end

"""Single table version of `rem`"""
function rem!(crel::CSet, tab::Symbol, rem::Set{Int})::Nothing
  rem_parts!(crel, tab, sort(collect(rem)))
  return nothing
end

"""
Eliminate options from a partial model by choosing a particular
FK combination for a specified PK.
"""
function choose(crel::CSet{CD}, srcind::Int, fk::Symbol, choice::Int
         )::CSet{CD} where {CD}
  fksrc = add_srctgt(fk, true)
  fks = crel.indices[fksrc][srcind]
  @assert 0 < choice <= length(fks)
  chosen = fks[choice]
  delinds = Set([fk for fk in fks if fk != chosen])
  res = deepcopy(crel)
  rem!(res, fk, delinds)
  return res
end

"""
1. Enumerate elements of ℕᵏ for an underlying graph with k nodes.
2. For each of these: (c₁, ..., cₖ) create a term model with that many constants

Do the first enumeration by incrementing n_nonzero and finding partitions so
that ∑(c₁,...) = n_nonzero

In the future, this function will write results to a database
that hashes the FLS as well as the set of constants that generated the model.

Also crucial is to decompose FLS into subparts that can be efficiently solved
and have solutions stitched together.
"""
function enum(fls::FLSketch, n::Int)::Dict{Tuple,Vector{CSet}}
    res = Dict{Tuple,CSet}()
    n_const = 0 # total number of constants across all sets
    n_v = nv(fls.G)
    while length(res) < n
        n_const += 1
        for n_nonzero in 1:n_v
            # values we'll assign to nodes
            c_parts = partitions(n_const, n_nonzero)
            # Which nodes we'll assign them to
            indices = permutations(1:n_v,n_nonzero)

            for c_part in c_parts
                for index_assign in indices
                    n_const = zeros(n_v)
                    n_const[index_assign] = c_part
                    n_c = tuple(n_const...)
                    if !(n_c in res)
                        res[n_c] =  term_models(flv, n_c)
                    end
                end
            end
        end
    end
end