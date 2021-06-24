module Automorphisms
export canonical_hash, canonical_iso, autos, apply_automorphism, color_refine, pseudo_cset, pseudo_cset_inv
using ..CSets
using ...Theories
using ...Theories: adom, attr, data, attr, adom, acodom, AttrDesc
using Catlab.Present

# Color assigned to each elem of each compoennt
CDict = Dict{Symbol, Vector{Int}}

"""
To compute automorphisms of Attributed CSets, we create a pseudo CSet which has
components for each data type.
"""
function pseudo_cset(g::ACSet{CD,AD})::Tuple{CSet, Vector{Vector{Any}}} where {CD, AD}
    tabs, arrs, src, tgt = collect(ob(CD)), collect(hom(CD)), dom(CD), codom(CD)
    dtabs, darrs, dsrc, dtgt = collect(data(AD)), collect(attr(AD)), adom(AD), acodom(AD)
    pres = Presentation(FreeSchema)
    xobs = [Ob(FreeSchema,t) for t in vcat(tabs,dtabs)]
    n = length(tabs)
    for x in xobs add_generator!(pres, x) end
    for (arr, s, t) in zip(map(collect, [arrs, src, tgt])...)
        add_generator!(pres, Hom(arr, xobs[s], xobs[t]))
    end
    attrvals = [Set() for _ in 1:length(dtabs)]
    for (arr, s, t) in zip(darrs, dsrc, dtgt)
        add_generator!(pres, Hom(arr, xobs[s], xobs[t+n]))
        union!(attrvals[t], Set(g[arr]))
    end
    attrvals = Vector{Any}[sort(collect(x)) for x in attrvals]
    ctype =  ACSetType(pres, index=vcat(arrs,darrs))
    res = ctype()
    for t in tabs add_parts!(res, t, nparts(g,t)) end
    for (i,t) in enumerate(dtabs) add_parts!(res, t, length(attrvals[i])) end
    for a in arrs set_subpart!(res, a, g[a]) end
    for (a,t) in zip(darrs, dtgt)
        fks = [findfirst(==(v), attrvals[t]) for v in g[a]]
        set_subpart!(res, a, fks)
    end
    return res, attrvals
end

"""Inverse of pseudo_cset"""
function pseudo_cset_inv(g::CSet, orig::ACSet{CD,AD}, attrvals::Vector{Vector{Any}})::ACSet{CD,AD} where {CD,AD}
    orig = deepcopy(orig)
    arrs = hom(CD)
    darrs, dtgt = attr(AD), acodom(AD)
    for arr in arrs
        set_subpart!(orig, arr, g[arr])
    end
    for (darr,tgt) in zip(darrs, dtgt)
        set_subpart!(orig, darr, attrvals[tgt][g[darr]])
    end
    return orig
end

# The maximum color of an empty color list is 0
function max0(x::Vector{Int})::Int
    return isempty(x) ? 0 : maximum(x)
end

function check_auto(x::CDict)::Nothing
    for perm in values(x)
        @assert length(perm) == length(Set(perm))
    end
end

"""Apply a coloring to a Cset to get an isomorphic cset"""
function apply_automorphism(c::CSet,d::CDict)::CSet
    check_auto(d)
    new = deepcopy(c)
    tabs, arrs, srcs, tgts = (typeof(c).parameters[1]).parameters
    for (arr, srci, tgti) in zip(arrs,srcs,tgts)
        src, tgt =  [tabs[x] for x in [srci, tgti]]
        set_subpart!(new, d[src],arr, d[tgt][c[arr]])
    end
    return new
end

"""Lexicographic minimum of all automorphisms"""
function canonical_iso(g::CSet)::CSet
    isos = sort([apply_automorphism(g, Dict(a)) for a in autos(g)], by=string)
    return isempty(isos) ? g : isos[1]
end

"""
Compute automorphisms for the pseudo-cset, but then substitute in
the actual attribute values before evaluating the lexicographic order
"""
function canonical_iso(g::ACSet)::ACSet
    p, avals = pseudo_cset(g)
    isos = sort([pseudo_cset_inv(apply_automorphism(p, Dict(a)), g, avals)
                 for a in autos(p)], by=string)
    return isempty(isos) ? g : isos[1]
end

function canonical_hash(g::ACSet)::UInt64
    return hash(string(canonical_iso(g)))
end

# Store 1.) how many of each color (for each in arrow) has
# a particular point as its target, 2.) what color (for
# each out arrow) the data point is the src of
CDataPoint = Tuple{Vector{Vector{Int}}, Vector{Int}}
# Data req' to color a CSet (each element of each component)
CData = Dict{Symbol, Vector{CDataPoint}}

"""
This could be extended to add extra automorphism-invariant
properties in the output. Right now, we just compute the
following pair for each element of each component:
- number of incident edges from each arrow (from each color)
- the color pointed to by each outgoing edge

This does not generalize to ACSets. We cannot naively
throw the attributes as raw data into the color data.
It will make indistinguishable elements (e.g. two
elements that map to different data but otherwise can
be permuted) as distinguishable.
"""
function compute_color_data(g::CSet{CD}, color::CDict)::CData where {CD}
    tabs, arrs, srcs, tgts = ob(CD), hom(CD), dom(CD), codom(CD)
    ntab = eachindex(tabs)
    res = CData()
    a_in  = [[a_ind for (a_ind, t_ind) in enumerate(tgts) if t_ind==i] for i in ntab]
    a_out = [[a_ind for (a_ind, s_ind) in enumerate(srcs) if s_ind==i] for i in ntab]

    for (tgt_ind, tgt) in enumerate(tabs)
        subres = Vector{Vector{Int}}[]  # for each table
        for arr_ind in a_in[tgt_ind]
            src = tabs[srcs[arr_ind]]
            color_src = color[src]
            n_color_src = max0(color_src)
            preimg = g.indices[arrs[arr_ind]]
            subsubres = Vector{Int}[]  # for particular elem in tgt
            for tgt_elem in 1:nparts(g, tgt)
                precolor_elem = color_src[preimg[tgt_elem]]
                n_precolor = [count(==(x), precolor_elem) for x in 1:n_color_src]
                push!(subsubres, n_precolor)
            end
            push!(subres, subsubres)
        end

        # Also compute per-element data for table `tgt` (now, think of it as a src)
        outgoing_arrows = a_out[tgt_ind]
        out_subres = Vector{Int}[color[tabs[tgts[oga]]][g[arrs[oga]]]
                                 for oga in outgoing_arrows]

        # Combine the two pieces of data for each elmeent in tgt, store in res
        res[tgt] = [([ssr[i] for ssr in subres],
                     [osr[i] for osr in out_subres])
                    for i in 1:nparts(g,tgt)]
    end
    return res
end

"""
Construct permutation σ⁻¹ such that σσ⁻¹=id
"""
function invert_perm(x::CDict)::CDict
    function invert_comp(xs::Vector{Int})::Vector{Int}
        return [findfirst(==(v), xs) for v in eachindex(xs)]
    end
    return Dict([k=>invert_comp(v) for (k, v) in collect(x)])
end

"""
Compose permutations
"""
function compose_perms(x::CDict, y::CDict)::CDict
    function compose_comp(xs::Vector{Int},ys::Vector{Int})::Vector{Int}
        return [ys[xs[i]] for i in eachindex(xs)]
    end
    return Dict([k=>compose_comp(v1,y[k]) for (k, v1) in collect(x)])
end

# """Apply permutation to color dictionary"""
# function permute_color(σ::CDict, x::CDict)::CDict
#     function permute_comp(perm::Vector{Int}, xs::Vector{Int})::Vector{Int}
#         return [xs[perm[i]] for i in eachindex(xs)]
#     end
#     return Dict([k=>permute_comp(σ[k],v) for (k,v) in collect(x)])
# end

"""
Iterative color refinement based on the number (and identity) of
incoming and outgoing arrows.
"""
function color_refine(g::CSet{CD};
                      init_color::Union{Nothing,CDict}=nothing
                     )::CDict where {CD}
    # Default: uniform coloring
    new_color = (init_color === nothing
                    ? CDict([k => ones(Int, nparts(g, k)) for k in ob(CD)])
                    : init_color)

    prev_n, curr_n, iter = 0, 1, 0
    while prev_n != curr_n
        iter += 1
        prev_color = new_color
        # All that matters about newdata's type is that it is hashable
        newdata = compute_color_data(g, prev_color)
        new_datahash = Dict([k=>map(hash, zip(prev_color[k],v))
                             for (k, v) in collect(newdata)])
        hashes = Dict([k=>sort(collect(Set(v)))
                       for (k, v) in new_datahash])
        new_color = CDict([
            k=>[findfirst(==(new_datahash[k][i]), hashes[k])
                for i in 1:nparts(g, k)]
            for (k, v) in new_datahash])
        prev_n = sum(map(max0, values(prev_color)))
        curr_n = sum(map(max0, values(new_color)))
    end
    return new_color
end

"""
Find index at which two vectors diverge (used in search_tree)
"""
function common(v1::Vector{T}, v2::Vector{T})::Int where {T}
    for (i, (x, y)) in enumerate(zip(v1, v2))
        if x != y
            return i-1
        end
    end
    return i
end

"""
DFS tree of colorings, with edges being choices in how to break symmetry
Goal is to acquire all leaf nodes.

Note, there is another use of automorphisms not yet implemented:
 - "Automorphisms discovered during the search can also be used to prune the search tree in another way. Let d be a node being re-visited by the depth-first search. Let Γ be the group generated by the automorphisms discovered thus far, and let Φ be the subgroup of Γ that fixes d. Suppose that b and c are children of d where some element of Φ maps b to c. If T(G,b) has already been examined, then, as above, there is no need to examine T(G,c). Hence T(G,c) can be pruned from the tree."
"""
function search_tree(g::CSet{CD},
                     coloring::CDict,
                     split_seq::Vector{Int},
                     tree::Dict{Vector{Int},CDict},
                     perms::Set{Vector{Int}},
                     skip::Set{Vector{Int}}
                    )::Vector{CDict} where {CD}

    tree[split_seq] = coloring # add the current color to the tree

    # To reduce branching factor, split on the SMALLEST nontrivial partition
    colors_by_size = []
    for (k, v) in coloring
        for color in 1:max0(v)
            n_c = count(==(color), v)
            if n_c > 1
                # Store which table and which color
                push!(colors_by_size, n_c => (k, color))
            end
        end
    end

    if isempty(colors_by_size) # We found a leaf!
        # Construct automorphisms between leaves
        # to possibly prune the search tree
        # See figure 4
        tau_inv = invert_perm(coloring)
        for p in perms
            pii = tree[p]
            auto = compose_perms(pii,tau_inv)
            i = common(p, split_seq)
            a = tree[p[1:i]]
            if compose_perms(auto, a) == a
                b = tree[p[1:i+1]]
                c_location = split_seq[1:i+1]
                c = tree[c_location]
                if compose_perms(auto, b) == c
                    push!(skip, c_location)
                end
            end
        end
        # Add permutation to the list of results
        push!(perms, split_seq)
    else
        sort!(colors_by_size)
        split_tab, split_color = colors_by_size[1][2]
        colors = coloring[split_tab]
        split_inds = findall(==(split_color), colors)
        for split_ind in split_inds
            if !(split_seq in skip)
                new_coloring = deepcopy(coloring)
                new_seq = vcat(split_seq, [split_ind])
                new_coloring[split_tab][split_ind] = max0(colors) + 1
                refined = color_refine(g; init_color=new_coloring)
                search_tree(g, refined, new_seq, tree, perms, skip)
            end
        end
    end
    return [tree[p] for p in perms]
end

"""
Compute the automorphisms of a CSet
"""
function autos(g::CSet)::Vector{CDict}
    return search_tree(g, color_refine(g), Int[],
                       Dict{Vector{Int},CDict}(),
                       Set{Vector{Int}}(),
                       Set{Vector{Int}}())
end
end