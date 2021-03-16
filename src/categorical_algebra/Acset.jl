module Acset
export is_acset, acset_schema, nparts, parts, has_part, has_subpart, subpart, incident,
  add_part!, add_parts!, set_subpart!, set_subparts!, rem_part!, rem_parts!,
  copy_parts!, copy_parts_only!

using Compat: only
using StaticArrays: StaticArray

using ..Syntax: GATExpr, args

""" Define this function to be true for any type that you
want to define the acset interface on.
"""
is_acset(acs) = error("Not implemented")

""" This should return a Presentation object.

Note: Maybe use AcsetSchema instead?
"""
acset_schema(acs) = error("Not implemented")

""" Number of parts of given type in an acset.
"""
nparts(acs, type) = error("Not implemented")

""" Parts of given type in an acset.
"""
parts(acs, type) = 1:nparts(acs, type)

""" Whether an acset has a part with the given name.
"""
has_part(acs, type) = error("Not implemented")

has_part(acs, type::Symbol, part::Int) = 1 <= part <= nparts(acs, type)
has_part(acs, type::Symbol, part::AbstractVector{Int}) =
  let n=nparts(acs, type); [ 1 <= x <= n for x in part ] end

has_subpart(acs, name) = error("Not implemented")

""" Get subpart of part in acset.

Both single and vectorized access are supported, with a view of the underlying
data being returned in the latter case. Chaining, or composition, of subparts is
also supported. For example, given a vertex-attributed graph `g`,

```
subpart(g, e, [:src, :vattr])
```

returns the vertex attribute of the source vertex of the edge `e`. As a
shorthand, subparts can also be accessed by indexing:

```
g[e, :src] == subpart(g, e, :src)
```

Be warned that indexing with lists of subparts works just like `subpart`:
`g[e,[:src,:vattr]]` is equivalent to `subpart(g, e, [:src,:vattr])`. This
convention differs from DataFrames but note that the alternative interpretation
of `[:src,:vattr]` as two independent columns does not even make sense, since
they have different domains (belong to different tables).
"""
@inline subpart(acs, name::Symbol) = error("Not implemented")
@inline subpart(acs, part, name) = view_or_slice(subpart(acs, name), part)

@inline view_or_slice(x::AbstractVector, i) = view(x, i)
@inline view_or_slice(x::AbstractVector, i::Union{Integer,StaticArray}) = x[i]

subpart(acs, expr::GATExpr{:generator}) = subpart(acs, first(expr))
subpart(acs, expr::GATExpr{:id}) = parts(acs, first(dom(expr)))

function subpart(acs, part, names::AbstractVector{Symbol})
  foldl(names, init=part) do part, name
    subpart(acs, part, name)
  end
end
subpart(acs, part, expr::GATExpr{:compose}) =
  subpart(acs, part, subpart_names(expr))

subpart(acs, names::AbstractVector{Symbol}) =
  subpart(acs, subpart(acs, names[1]), names[2:end])
subpart(acs, expr::GATExpr{:compose}) = subpart(acs, subpart_names(expr))

subpart_names(expr::GATExpr{:generator}) = Symbol[first(expr)]
subpart_names(expr::GATExpr{:id}) = Symbol[]
subpart_names(expr::GATExpr{:compose}) =
  mapreduce(subpart_names, vcat, args(expr))

""" Get superparts incident to part in acset.

If the subpart is indexed, this takes constant time; otherwise, it takes linear
time. As with [`subpart`](@ref), both single and vectorized access, as well as
chained access, are supported. Note that sequences of morphisms are supplied in
the usual left-to-right order, so that

```
incident(g, x, [:src, :vattr])
```

returns the list of all edges whose source vertex has vertex attribute `x`.

Note that when the subpart is indexed, this function returns a view of the
underlying index, which should not be mutated. To ensure that a fresh copy is
returned, regardless of whether indexing is enabled, set the keyword argument
`copy=true`.
"""
@inline incident(acs, part, name) = error("Not implemented")

function incident(acs, part, names::AbstractVector{Symbol};
                  copy::Bool=false)
  # Don't need to pass `copy` because copy will be made regardless.
  foldr(names, init=part) do name, part
    reduce(vcat, incident(acs, part, name), init=Int[])
  end
end
incident(acs, part, expr::GATExpr; kw...) =
  incident(acs, part, subpart_names(expr); kw...)

""" Add part of given type to acset, optionally setting its subparts.

Returns the ID of the added part.

See also: [`add_parts!`](@ref).
"""
function add_part!(acs, type::Symbol, args...; kw...)
  part = only(add_parts!(acs,type,1))
  try
    set_subparts!(acs, part, args...; kw...)
  catch e
    rem_part!(acs, type, part)
    rethrow(e)
  end
  part
end

""" Add parts of given type to acset, optionally setting their subparts.

Returns the range of IDs for the added parts.

See also: [`add_part!`](@ref).
"""
add_parts!(acs, type::Symbol, n::Int) = error("Not implemented")

function add_parts!(acs, type::Symbol, n::Int, args...; kw...)
  parts = add_parts!(acs, type, n)
  try
    set_subparts!(acs, parts, args...; kw...)
  catch e
    rem_parts!(acs, type, parts)
    rethrow(e)
  end
  parts
end


""" Mutate subpart of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subparts!`](@ref).
"""
@inline set_subpart!(acs, part::Int, name::Symbol, subpart) = error("Not implemented")
@inline set_subpart!(acs, name, subpart) = set_subpart!(acs, :, name, subpart)

@inline set_subpart!(acs, ::Colon, name, subpart) =
  set_subpart!(acs, 1:length(subpart(acs,name)), name, subpart)

# Inlined for the same reason as `subpart`.

function set_subpart!(acs, part::AbstractVector{Int}, name, subpart)
  broadcast(part, subpart) do part, subpart
    set_subpart!(acs, part, name, subpart)
  end
end

""" Mutate subparts of a part in a C-set.

Both single and vectorized assignment are supported.

See also: [`set_subpart!`](@ref).
"""
function set_subparts!(acs, part, kw::NamedTuple)
  for name in keys(kw)
    set_subpart!(acs, part, name, kw[name])
  end
end

set_subparts!(acs, part; kw...) = set_subparts!(acs, part, (;kw...))

""" Remove part from a C-set.

The part is removed using the "pop and swap" strategy familiar from
[LightGraphs.jl](https://github.com/JuliaGraphs/LightGraphs.jl), where the
"removed" part is actually replaced by the last part, which is then deleted.
This strategy has important performance benefits since only the last part must
be assigned a new ID, as opposed to assigning new IDs to *every* part following
the removed part.

The removal operation is *not* recursive. When a part is deleted, any superparts
incident to it are retained, but their subparts become undefined (equal to the
integer zero). For example, in a graph, if you call `rem_part!` on a vertex, the
edges incident the `src` and/or `tgt` vertices of the edge become undefined but
the edge itself is not deleted.

Indexing has both positive and negative impacts on performance. On the one hand,
indexing reduces the cost of finding affected superparts from linear time to
constant time. On the other hand, the indices of subparts must be updated when
the part is removed. For example, in a graph, indexing `src` and `tgt` makes
removing vertices faster but removing edges (slightly) slower.

See also: [`rem_parts!`](@ref).
"""
rem_part!(acs, type, part) = error("Not implemented")

""" Remove parts from a C-set.

The parts must be supplied in sorted order, without duplicates.

See also: [`rem_part!`](@ref).
"""
function rem_parts!(acs, type, parts)
  issorted(parts) || error("Parts to be removed must be in sorted order")
  for part in Iterators.reverse(parts)
    rem_part!(acs, type, part)
  end
end

""" Copy parts from a C-set to a C′-set.

The selected parts must belong to both schemas. All subparts common to the
selected parts, including data attributes, are preserved. Thus, if the selected
parts form a sub-C-set, then the whole sub-C-set is preserved. On the other
hand, if the selected parts do *not* form a sub-C-set, then some copied parts
will have undefined subparts.

TODO: handle colons
"""
copy_parts!(to, from, parts::NamedTuple)= error("Not implemented")

copy_parts!(to, from, obs::Tuple) =
  copy_parts!(to, from, NamedTuple{obs}((:) for ob in obs))

copy_parts!(to, from; kw...) = copy_parts!(to, from, (;kw...))

""" Copy parts from a C-set to a C′-set, ignoring all non-data subparts.

The selected parts must belong to both schemas. Attributes common to both
schemas are also copied, but no other subparts are copied.

See also: [`copy_parts!`](@ref).
"""
copy_parts_only!(to, from; kw...) = error("Not implemented")

end
