""" Free diagrams in a category.

A [free diagram](https://ncatlab.org/nlab/show/free+diagram) in a category is a
diagram whose shape is a free category. Examples include the empty diagram,
pairs of objects, discrete diagrams, parallel pairs, composable pairs, and spans
and cospans. Limits and colimits are most commonly taken over free diagrams.
"""
module FreeDiagrams
export AbstractFreeDiagram, FreeDiagram, BipartiteFreeDiagram,
  FixedShapeFreeDiagram, DiscreteDiagram, EmptyDiagram, ObjectPair,
  Span, Cospan, Multispan, Multicospan, SMultispan, SMulticospan,
  ParallelPair, ParallelMorphisms, ComposablePair, ComposableMorphisms,
  ob, hom, dom, codom, apex, legs, feet, left, right, bundle_legs,
  nv, ne, src, tgt, vertices, edges, has_vertex, has_edge,
  add_vertex!, add_vertices!, add_edge!, add_edges!,
  ob₁, ob₂, nv₁, nv₂, vertices₁, vertices₂,
  add_vertex₁!, add_vertex₂!, add_vertices₁!, add_vertices₂!

using AutoHashEquals
using StaticArrays: StaticVector, SVector, @SVector

using ...Present, ...Theories, ...CSetDataStructures, ...Graphs
import ...Theories: ob, hom, dom, codom, left, right
using ...Graphs.BasicGraphs: TheoryGraph
using ...Graphs.BipartiteGraphs: TheoryUndirectedBipartiteGraph

# Diagrams of fixed shape
#########################

""" Abstract type for free diagram of fixed shape.
"""
abstract type FixedShapeFreeDiagram{Ob} end

# Discrete diagrams
#------------------

""" Discrete diagram: a diagram whose only morphisms are identities.
"""
@auto_hash_equals struct DiscreteDiagram{Ob,Objects<:AbstractVector{Ob}} <:
    FixedShapeFreeDiagram{Ob}
  objects::Objects
end

const EmptyDiagram{Ob} = DiscreteDiagram{Ob,<:StaticVector{0,Ob}}
const ObjectPair{Ob} = DiscreteDiagram{Ob,<:StaticVector{2,Ob}}

EmptyDiagram{Ob}() where Ob = DiscreteDiagram(@SVector Ob[])
ObjectPair(first, second) = DiscreteDiagram(SVector(first, second))

ob(d::DiscreteDiagram) = d.objects

Base.iterate(d::DiscreteDiagram, args...) = iterate(d.objects, args...)
Base.eltype(d::DiscreteDiagram) = eltype(d.objects)
Base.length(d::DiscreteDiagram) = length(d.objects)
Base.getindex(d::DiscreteDiagram, i) = d.objects[i]
Base.firstindex(d::DiscreteDiagram) = firstindex(d.objects)
Base.lastindex(d::DiscreteDiagram) = lastindex(d.objects)

# Spans and cospans
#------------------

""" Multispan of morphisms in a category.

A [multispan](https://ncatlab.org/nlab/show/multispan) is like a [`Span`](@ref)
except that it may have a number of legs different than two. A colimit of this
shape is a pushout.
"""
@auto_hash_equals struct Multispan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob}
  apex::Ob
  legs::Legs
end

function Multispan(legs::AbstractVector)
  !isempty(legs) || error("Empty list of legs but no apex given")
  allequal(dom.(legs)) || error("Legs $legs do not have common domain")
  Multispan(dom(first(legs)), legs)
end

const SMultispan{N,Ob,Hom} = Multispan{Ob,Hom,<:StaticVector{N,Hom}}

SMultispan{N}(apex, legs::Vararg{Any,N}) where N =
  Multispan(apex, SVector{N}(legs...))
SMultispan{0}(apex) = Multispan(apex, SVector{0,typeof(id(apex))}())
SMultispan{N}(legs::Vararg{Any,N}) where N = Multispan(SVector{N}(legs...))

""" Span of morphims in a category.

A common special case of [`Multispan`](@ref). See also [`Cospan`](@ref).
"""
const Span{Ob,Hom} = SMultispan{2,Ob,Hom}

"""    apex(span::Multispan)

returns the object at the top of the multispan, which is the domain of all the legs.
"""
apex(span::Multispan) = span.apex

"""    legs(span::Multispan)

returns the collection of legs in the multspan, which are the morphisms sharing a common domain.
"""
legs(span::Multispan) = span.legs

"""    feet(span::Multispan)

returns the collection of feet in the multspan, which are the codomains of the legs.
"""
feet(span::Multispan) = map(codom, span.legs)
left(span::Span) = span.legs[1]
right(span::Span) = span.legs[2]

Base.iterate(span::Multispan, args...) = iterate(span.legs, args...)
Base.eltype(span::Multispan) = eltype(span.legs)
Base.length(span::Multispan) = length(span.legs)

""" Multicospan of morphisms in a category.

A multicospan is like a [`Cospan`](@ref) except that it may have a number of
legs different than two. A limit of this shape is a pullback.
"""
@auto_hash_equals struct Multicospan{Ob,Hom,Legs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob}
  apex::Ob
  legs::Legs
end

function Multicospan(legs::AbstractVector)
  !isempty(legs) || error("Empty list of legs but no apex given")
  allequal(codom.(legs)) || error("Legs $legs do not have common codomain")
  Multicospan(codom(first(legs)), legs)
end

const SMulticospan{N,Ob,Hom} = Multicospan{Ob,Hom,<:StaticVector{N,Hom}}

SMulticospan{N}(apex, legs::Vararg{Any,N}) where N =
  Multicospan(apex, SVector{N}(legs...))
SMulticospan{0}(apex) = Multicospan(apex, SVector{0,typeof(id(apex))}())
SMulticospan{N}(legs::Vararg{Any,N}) where N = Multicospan(SVector{N}(legs...))

""" Cospan of morphisms in a category.

A common special case of [`Multicospan`](@ref). See also [`Span`](@ref).
"""
const Cospan{Ob,Hom} = SMulticospan{2,Ob,Hom}

apex(cospan::Multicospan) = cospan.apex
legs(cospan::Multicospan) = cospan.legs
feet(cospan::Multicospan) = map(dom, cospan.legs)
left(cospan::Cospan) = cospan.legs[1]
right(cospan::Cospan) = cospan.legs[2]

Base.iterate(cospan::Multicospan, args...) = iterate(cospan.legs, args...)
Base.eltype(cospan::Multicospan) = eltype(cospan.legs)
Base.length(cospan::Multicospan) = length(cospan.legs)

""" Bundle together legs of a multi(co)span.

For example, calling `bundle_legs(span, SVector((1,2),(3,4)))` on a multispan
with four legs gives a span whose left leg bundles legs 1 and 2 and whose right
leg bundles legs 3 and 4. Note that in addition to bundling, this function can
also permute legs and discard them.

The bundling is performed using the universal property of (co)products, which
assumes that these (co)limits exist.
"""
bundle_legs(span::Multispan, indices) =
  Multispan(apex(span), map(i -> bundle_leg(span, i), indices))
bundle_legs(cospan::Multicospan, indices) =
  Multicospan(apex(cospan), map(i -> bundle_leg(cospan, i), indices))

bundle_leg(x::Union{Multispan,Multicospan}, i::Int) = legs(x)[i]
bundle_leg(x::Union{Multispan,Multicospan}, i::Tuple) = bundle_leg(x, SVector(i))
bundle_leg(span::Multispan, i::AbstractVector{Int}) = pair(legs(span)[i])
bundle_leg(cospan::Multicospan, i::AbstractVector{Int}) = copair(legs(cospan)[i])

# Parallel morphisms
#-------------------

""" Parallel morphims in a category.

[Parallel morphisms](https://ncatlab.org/nlab/show/parallel+morphisms) are just
morphisms with the same domain and codomain. A (co)limit of this shape is a
(co)equalizer.

For the common special case of two morphisms, see [`ParallelPair`](@ref).
"""
@auto_hash_equals struct ParallelMorphisms{Dom,Codom,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Union{Dom,Codom}}
  dom::Dom
  codom::Codom
  homs::Homs
end

function ParallelMorphisms(homs::AbstractVector)
  @assert !isempty(homs) && allequal(dom.(homs)) && allequal(codom.(homs))
  ParallelMorphisms(dom(first(homs)), codom(first(homs)), homs)
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphisms`](@ref).
"""
const ParallelPair{Dom,Codom,Hom} =
  ParallelMorphisms{Dom,Codom,Hom,<:StaticVector{2,Hom}}

function ParallelPair(first, last)
  dom(first) == dom(last) ||
    error("Domains of parallel pair do not match: $first vs $last")
  codom(first) == codom(last) ||
    error("Codomains of parallel pair do not match: $first vs $last")
  ParallelMorphisms(dom(first), codom(first), SVector(first, last))
end

dom(para::ParallelMorphisms) = para.dom
codom(para::ParallelMorphisms) = para.codom
hom(para::ParallelMorphisms) = para.homs

Base.iterate(para::ParallelMorphisms, args...) = iterate(para.homs, args...)
Base.eltype(para::ParallelMorphisms) = eltype(para.homs)
Base.length(para::ParallelMorphisms) = length(para.homs)
Base.getindex(para::ParallelMorphisms, i) = para.homs[i]
Base.firstindex(para::ParallelMorphisms) = firstindex(para.homs)
Base.lastindex(para::ParallelMorphisms) = lastindex(para.homs)

allequal(xs::AbstractVector) = isempty(xs) || all(==(xs[1]), xs)

# Composable morphisms
#---------------------

""" Composable morphisms in a category.

Composable morphisms are a sequence of morphisms in a category that form a path
in the underlying graph of the category.

For the common special case of two morphisms, see [`ComposablePair`](@ref).
"""
@auto_hash_equals struct ComposableMorphisms{Ob,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob}
  homs::Homs
end

function ComposableMorphisms(homs::Homs) where {Hom, Homs<:AbstractVector{Hom}}
  doms, codoms = dom.(homs), codom.(homs)
  all(c == d for (c,d) in zip(codoms[1:end-1], doms[2:end])) ||
    error("Domain mismatch in composable sequence: $homs")
  ComposableMorphisms{Union{eltype(doms),eltype(codoms)},Hom,Homs}(homs)
end

""" Pair of composable morphisms in a category.

[Composable pairs](https://ncatlab.org/nlab/show/composable+pair) are a common
special case of [`ComposableMorphisms`](@ref).
"""
const ComposablePair{Ob,Hom} = ComposableMorphisms{Ob,Hom,<:StaticVector{2,Hom}}

ComposablePair(first, last) = ComposableMorphisms(SVector(first, last))

dom(comp::ComposableMorphisms) = dom(first(comp))
codom(comp::ComposableMorphisms) = codom(last(comp))
hom(comp::ComposableMorphisms) = comp.homs

Base.iterate(comp::ComposableMorphisms, args...) = iterate(comp.homs, args...)
Base.eltype(comp::ComposableMorphisms) = eltype(comp.homs)
Base.length(comp::ComposableMorphisms) = length(comp.homs)
Base.getindex(comp::ComposableMorphisms, i) = comp.homs[i]
Base.firstindex(comp::ComposableMorphisms) = firstindex(comp.homs)
Base.lastindex(comp::ComposableMorphisms) = lastindex(comp.homs)

# Diagrams of flexible shape
############################

# Bipartite free diagrams
#------------------------

@present TheoryBipartiteFreeDiagram <: TheoryUndirectedBipartiteGraph begin
  Ob::Data
  Hom::Data
  ob₁::Attr(V₁,Ob)
  ob₂::Attr(V₂,Ob)
  hom::Attr(E,Hom)
end

const AbstractBipartiteFreeDiagram =
  AbstractACSetType(TheoryBipartiteFreeDiagram)

""" A free diagram that is bipartite.

Such diagrams include most of the fixed shapes, such as spans, cospans, and
parallel morphisms. They are the generic shape of diagrams for limits and
colimits arising from undirected wiring diagrams. For limits, the boxes
correspond to vertices in ``V₁`` and the junctions to vertics in ``V₂``.
Colimits are dual.
"""
const BipartiteFreeDiagram = ACSetType(TheoryBipartiteFreeDiagram,
                                       index=[:src, :tgt])

ob₁(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :ob₁)
ob₂(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :ob₂)
hom(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :hom)

function BipartiteFreeDiagram(
    obs₁::AbstractVector{Ob₁}, obs₂::AbstractVector{Ob₂},
    homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob₁,Ob₂,Hom}
  @assert all(obs₁[s] == dom(f) && obs₂[t] == codom(f) for (f,s,t) in homs)
  d = BipartiteFreeDiagram{Union{Ob₁,Ob₂},Hom}()
  add_vertices₁!(d, length(obs₁), ob₁=obs₁)
  add_vertices₂!(d, length(obs₂), ob₂=obs₂)
  add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

function BipartiteFreeDiagram(span::Multispan{Ob,Hom}) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₁!(d, ob₁=apex(span))
  vs = add_vertices₂!(d, length(span), ob₂=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function BipartiteFreeDiagram(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₂!(d, ob₂=apex(cospan))
  vs = add_vertices₁!(d, length(cospan), ob₁=feet(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function BipartiteFreeDiagram(para::ParallelMorphisms{Dom,Codom,Hom}) where {Dom,Codom,Hom}
  d = BipartiteFreeDiagram{Union{Dom,Codom},Hom}()
  v₁ = add_vertex₁!(d, ob₁=dom(para))
  v₂ = add_vertex₂!(d, ob₂=codom(para))
  add_edges!(d, fill(v₁,length(para)), fill(v₂,length(para)), hom=hom(para))
  return d
end

# General free diagrams
#----------------------

@present TheoryFreeDiagram <: TheoryGraph begin
  Ob::Data
  Hom::Data
  ob::Attr(V,Ob)
  hom::Attr(E,Hom)
end

const FreeDiagram = ACSetType(TheoryFreeDiagram, index=[:src,:tgt])

# XXX: This is needed because we cannot control the supertype of C-set types.
const _AbstractFreeDiagram = AbstractACSetType(TheoryFreeDiagram)
const AbstractFreeDiagram{Ob} = Union{FixedShapeFreeDiagram{Ob},
  AbstractBipartiteFreeDiagram{Ob}, _AbstractFreeDiagram{Ob}}

ob(d::FreeDiagram, args...) = subpart(d, args..., :ob)
hom(d::FreeDiagram, args...) = subpart(d, args..., :hom)

function FreeDiagram(obs::AbstractVector{Ob},
                     homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob,Hom}
  @assert all(obs[s] == dom(f) && obs[t] == codom(f) for (f,s,t) in homs)
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(obs), ob=obs)
  length(homs) > 0 && add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

function FreeDiagram(discrete::DiscreteDiagram{Ob}) where Ob
  d = FreeDiagram{Ob,Nothing}()
  add_vertices!(d, length(discrete), ob=collect(discrete))
  return d
end

function FreeDiagram(span::Multispan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  v₀ = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, length(span), ob=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function FreeDiagram(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  vs = add_vertices!(d, length(cospan), ob=feet(cospan))
  v₀ = add_vertex!(d, ob=apex(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function FreeDiagram(para::ParallelMorphisms{Dom,Codom,Hom}) where {Dom,Codom,Hom}
  d = FreeDiagram{Union{Dom,Codom},Hom}()
  add_vertices!(d, 2, ob=[dom(para), codom(para)])
  add_edges!(d, fill(1,length(para)), fill(2,length(para)), hom=hom(para))
  return d
end

function FreeDiagram(comp::ComposableMorphisms{Ob,Hom}) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  n = length(comp)
  add_vertices!(d, n+1, ob=[dom.(comp); codom(comp)])
  add_edges!(d, 1:n, 2:(n+1), hom=hom(comp))
  return d
end

function FreeDiagram(diagram::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
  # Should be a pushforward data migration but that is not yet implemented.
  d = FreeDiagram{Ob,Hom}()
  vs₁ = add_vertices!(d, nv₁(diagram), ob=ob₁(diagram))
  vs₂ = add_vertices!(d, nv₂(diagram), ob=ob₂(diagram))
  add_edges!(d, vs₁[src(diagram)], vs₂[tgt(diagram)], hom=hom(diagram))
  return d
end

end
