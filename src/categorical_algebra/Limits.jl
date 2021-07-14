""" Limits and colimits in a category.
"""
module Limits
export AbstractLimit, AbstractColimit, Limit, Colimit,
  LimitAlgorithm, ColimitAlgorithm,
  ob, cone, cocone, apex, legs, limit, colimit, universal,
  Terminal, Initial, terminal, initial, delete, create, factorize,
  BinaryProduct, Product, product, proj1, proj2, pair,
  BinaryPullback, Pullback, pullback,
  BinaryEqualizer, Equalizer, equalizer, incl,
  BinaryCoproduct, Coproduct, coproduct, coproj1, coproj2, copair,
  BinaryPushout, Pushout, pushout, pushout_complement, can_pushout_complement,
  BinaryCoequalizer, Coequalizer, coequalizer, proj,
  @cartesian_monoidal_instance, @cocartesian_monoidal_instance,
  ComposeProductEqualizer, ComposeCoproductCoequalizer

using AutoHashEquals

using ...Theories
import ...Theories: ob, terminal, product, proj1, proj2, equalizer, incl,
  initial, coproduct, coproj1, coproj2, coequalizer, proj,
  delete, create, pair, copair, factorize
using ..FreeDiagrams
import ..FreeDiagrams: apex, legs

# Data types for limits
#######################

""" Abstract type for limit in a category.

The standard concrete subtype is [`Limit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractLimit{Ob,Diagram} end

ob(lim::AbstractLimit) = apex(lim)
cone(lim::AbstractLimit) = lim.cone
apex(lim::AbstractLimit) = apex(cone(lim))
legs(lim::AbstractLimit) = legs(cone(lim))

Base.iterate(lim::AbstractLimit, args...) = iterate(cone(lim), args...)
Base.eltype(lim::AbstractLimit) = eltype(cone(lim))
Base.length(lim::AbstractLimit) = length(cone(lim))

""" Limit in a category.
"""
@auto_hash_equals struct Limit{Ob,Diagram,Cone<:Multispan{Ob}} <:
    AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
end

const Terminal{Ob} = AbstractLimit{Ob,<:EmptyDiagram}
const BinaryProduct{Ob} = AbstractLimit{Ob,<:ObjectPair}
const Product{Ob} = AbstractLimit{Ob,<:DiscreteDiagram}
const BinaryPullback{Ob} = AbstractLimit{Ob,<:Cospan}
const Pullback{Ob} = AbstractLimit{Ob,<:Multicospan}
const BinaryEqualizer{Ob} = AbstractLimit{Ob,<:ParallelPair}
const Equalizer{Ob} = AbstractLimit{Ob,<:ParallelMorphisms}

proj1(lim::Union{BinaryProduct,BinaryPullback}) = first(legs(lim))
proj2(lim::Union{BinaryProduct,BinaryPullback}) = last(legs(lim))
incl(eq::Equalizer) = only(legs(eq))

""" Algorithm for computing limits.
"""
abstract type LimitAlgorithm end

# Data types for colimits
#########################

""" Abstract type for colimit in a category.

The standard concrete subtype is [`Colimit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractColimit{Ob,Diagram} end

ob(colim::AbstractColimit) = apex(colim)
cocone(colim::AbstractColimit) = colim.cocone
apex(colim::AbstractColimit) = apex(cocone(colim))
legs(colim::AbstractColimit) = legs(cocone(colim))

Base.iterate(colim::AbstractColimit, args...) = iterate(cocone(colim), args...)
Base.eltype(colim::AbstractColimit) = eltype(cocone(colim))
Base.length(colim::AbstractColimit) = length(cocone(colim))

""" Colimit in a category.
"""
@auto_hash_equals struct Colimit{Ob,Diagram,Cocone<:Multicospan{Ob}} <:
    AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
end

const Initial{Ob} = AbstractColimit{Ob,<:EmptyDiagram}
const BinaryCoproduct{Ob} = AbstractColimit{Ob,<:ObjectPair}
const Coproduct{Ob} = AbstractColimit{Ob,<:DiscreteDiagram}
const BinaryPushout{Ob} = AbstractColimit{Ob,<:Span}
const Pushout{Ob} = AbstractColimit{Ob,<:Multispan}
const BinaryCoequalizer{Ob} = AbstractColimit{Ob,<:ParallelPair}
const Coequalizer{Ob} = AbstractColimit{Ob,<:ParallelMorphisms}

coproj1(colim::Union{BinaryCoproduct,BinaryPushout}) = first(legs(colim))
coproj2(colim::Union{BinaryCoproduct,BinaryPushout}) = last(legs(colim))
proj(coeq::Coequalizer) = only(legs(coeq))

""" Algorithm for computing colimits.
"""
abstract type ColimitAlgorithm end

# Generic (co)limits
####################

""" Limit of a diagram.

To define limits in a category with objects `Ob`, override the method
`limit(::FreeDiagram{Ob})` for general limits or `limit(::D)` with suitable type
`D <: FixedShapeFreeDiagram{Ob}` for limits of specific shape, such as products
or equalizers.

See also: [`colimit`](@ref)
"""
function limit end

""" Colimit of a diagram.

To define colimits in a category with objects `Ob`, override the method
`colimit(::FreeDiagram{Ob})` for general colimits or `colimit(::D)` with
suitable type `D <: FixedShapeFreeDiagram{Ob}` for colimits of specific shape,
such as coproducts or coequalizers.

See also: [`limit`](@ref)
"""
function colimit end

""" Universal property of (co)limits.

Compute the morphism whose existence and uniqueness is guaranteed by the
universal property of (co)limits.

See also: [`limit`](@ref), [`colimit`](@ref).
"""
function universal end

# Specific (co)limits
#####################

""" Terminal object.

To implement for a type `T`, define the method `limit(::EmptyDiagram{T})`.
"""
terminal(T::Type; kw...) = limit(EmptyDiagram{T}(); kw...)

""" Initial object.

To implement for a type `T`, define the method `colimit(::EmptyDiagram{T})`.
"""
initial(T::Type; kw...) = colimit(EmptyDiagram{T}(); kw...)

""" Unique morphism into a terminal object.

To implement for a type `T`, define the method
`universal(::Terminal{T}, ::SMultispan{0,T})`.
"""
delete(A::T) where T = delete(terminal(T), A)
delete(lim::Terminal, A) = universal(lim, SMultispan{0}(A))

""" Unique morphism out of an initial object.

To implement for a type `T`, define the method
`universal(::Initial{T}, ::SMulticospan{0,T})`.
"""
create(A::T) where T = create(initial(T), A)
create(colim::Initial, A) = universal(colim, SMulticospan{0}(A))

""" Product of objects.

To implement for a type `T`, define the method `limit(::ObjectPair{T})` and/or
`limit(::DiscreteDiagram{T})`.
"""
product(A, B; kw...) = limit(ObjectPair(A, B); kw...)
product(As::AbstractVector; kw...) = limit(DiscreteDiagram(As); kw...)

""" Coproduct of objects.

To implement for a type `T`, define the method `colimit(::ObjectPair{T})` and/or
`colimit(::DiscreteDiagram{T})`.
"""
coproduct(A, B; kw...) = colimit(ObjectPair(A, B); kw...)
coproduct(As::AbstractVector; kw...) = colimit(DiscreteDiagram(As); kw...)

""" Equalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `limit(::ParallelPair{T})` and/or
`limit(::ParallelMorphisms{T})`.
"""
equalizer(f, g; kw...) = limit(ParallelPair(f, g); kw...)
equalizer(fs::AbstractVector; kw...) = limit(ParallelMorphisms(fs); kw...)

""" Coequalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `colimit(::ParallelPair{T})` or
`colimit(::ParallelMorphisms{T})`.
"""
coequalizer(f, g; kw...) = colimit(ParallelPair(f, g); kw...)
coequalizer(fs::AbstractVector; kw...) = colimit(ParallelMorphisms(fs); kw...)

""" Pullback of a pair of morphisms with common codomain.

To implement for a type `T`, define the method `limit(::Cospan{T})` and/or
`limit(::Multicospan{T})` or, if you have already implemented products and
equalizers, rely on the default implementation.
"""
pullback(f, g; kw...) = limit(Cospan(f, g); kw...)
pullback(fs::AbstractVector; kw...) = limit(Multicospan(fs); kw...)

""" Pushout of a pair of morphisms with common domain.

To implement for a type `T`, define the method `colimit(::Span{T})` and/or
`colimit(::Multispan{T})` or, if you have already implemented coproducts and
coequalizers, rely on the default implementation.
"""
pushout(f, g; kw...) = colimit(Span(f, g); kw...)
pushout(fs::AbstractVector; kw...) = colimit(Multispan(fs); kw...)

""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(f, g) = pair(product(codom(f), codom(g)), f, g)
pair(fs::AbstractVector) = pair(product(map(codom, fs)), fs)
pair(lim::Union{BinaryProduct,BinaryPullback}, f, g) =
  universal(lim, Span(f, g))
pair(lim::Union{Product,Pullback}, fs::AbstractVector) =
  universal(lim, Multispan(fs))

""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(f, g) = copair(coproduct(dom(f), dom(g)), f, g)
copair(fs::AbstractVector) = copair(coproduct(map(dom, fs)), fs)
copair(colim::Union{BinaryCoproduct,BinaryPushout}, f, g) =
  universal(colim, Cospan(f, g))
copair(colim::Union{Coproduct,Pushout}, fs::AbstractVector) =
  universal(colim, Multicospan(fs))

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
factorize(lim::Equalizer, h) = universal(lim, SMultispan{1}(h))
factorize(colim::Coequalizer, h) = universal(colim, SMulticospan{1}(h))

""" Pushout complement: extend composable pair to a pushout square.

[Pushout complements](https://ncatlab.org/nlab/show/pushout+complement) are the
essential ingredient for double pushout (DPO) rewriting.
"""
pushout_complement(f, g) = pushout_complement(ComposablePair(f, g))

""" Can a pushout complement be constructed for a composable pair?

Even in nice categories, this is not generally possible.
"""
can_pushout_complement(f, g) = can_pushout_complement(ComposablePair(f, g))

# (Co)cartesian monoidal categories
###################################

""" Define cartesian monoidal structure using limits.

Implements an instance of [`CartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface.
"""
macro cartesian_monoidal_instance(Ob, Hom)
  esc(quote
    import Catlab.Theories: CartesianCategory, otimes, ⊗, munit, braid, σ,
      mcopy, delete, pair, proj1, proj2, Δ, ◊

    @instance CartesianCategory{$Ob, $Hom} begin
      @import dom, codom, compose, ⋅, id, munit, delete, pair

      otimes(A::$Ob, B::$Ob) = ob(product(A, B))

      function otimes(f::$Hom, g::$Hom)
        π1, π2 = product(dom(f), dom(g))
        pair(product(codom(f), codom(g)), π1⋅f, π2⋅g)
      end

      function braid(A::$Ob, B::$Ob)
        AB, BA = product(A, B), product(B, A)
        pair(BA, proj2(AB), proj1(AB))
      end

      mcopy(A::$Ob) = pair(id(A),id(A))
      proj1(A::$Ob, B::$Ob) = proj1(product(A, B))
      proj2(A::$Ob, B::$Ob) = proj2(product(A, B))
    end

    otimes(As::AbstractVector{<:$Ob}) = ob(product(As))

    function otimes(fs::AbstractVector{<:$Hom})
      Π, Π′ = product(map(dom, fs)), product(map(codom, fs))
      pair(Π′, map(compose, legs(Π), fs))
    end

    munit(::Type{T}) where T <: $Ob = ob(terminal(T))
  end)
end

""" Define cocartesian monoidal structure using colimits.

Implements an instance of [`CocartesianCategory`](@ref) assuming that finite
coproducts have been implemented following the colimits interface.
"""
macro cocartesian_monoidal_instance(Ob, Hom)
  esc(quote
    import Catlab.Theories: CocartesianCategory, oplus, ⊕, mzero, swap,
      plus, zero, copair, coproj1, coproj2

    @instance CocartesianCategory{$Ob, $Hom} begin
      @import dom, codom, compose, ⋅, id, mzero, copair

      oplus(A::$Ob, B::$Ob) = ob(coproduct(A, B))

      function oplus(f::$Hom, g::$Hom)
        ι1, ι2 = coproduct(codom(f), codom(g))
        copair(coproduct(dom(f), dom(g)), f⋅ι1, g⋅ι2)
      end

      function swap(A::$Ob, B::$Ob)
        AB, BA = coproduct(A, B), coproduct(B, A)
        copair(AB, coproj2(BA), coproj1(BA))
      end

      plus(A::$Ob) = copair(id(A),id(A))
      zero(A::$Ob) = create(A)
      coproj1(A::$Ob, B::$Ob) = coproj1(coproduct(A, B))
      coproj2(A::$Ob, B::$Ob) = coproj2(coproduct(A, B))
    end

    oplus(As::AbstractVector{<:$Ob}) = ob(coproduct(As))

    function oplus(fs::AbstractVector{<:$Hom})
      ⊔, ⊔′ = coproduct(map(dom, fs)), coproduct(map(codom, fs))
      copair(⊔, map(compose, fs, legs(⊔′)))
    end

    mzero(::Type{T}) where T <: $Ob = ob(initial(T))
  end)
end

# Composite (co)limits
######################

""" Compute pullback by composing a product with an equalizer.

See also: [`ComposeCoproductCoequalizer`](@ref).
"""
struct ComposeProductEqualizer <: LimitAlgorithm end

""" Pullback formed as composite of product and equalizer.

The fields of this struct are an implementation detail; accessing them directly
violates the abstraction. Everything that you can do with a pushout, including
invoking its universal property, should be done through the generic interface
for limits.

See also: [`CompositePushout`](@ref).
"""
struct CompositePullback{Ob, Diagram<:Multicospan, Cone<:Multispan{Ob},
    Prod<:Product, Eq<:Equalizer} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  eq::Eq
end

function limit(cospan::Multicospan, ::ComposeProductEqualizer)
  prod = product(feet(cospan))
  (ι,) = eq = equalizer(map(compose, legs(prod), legs(cospan)))
  cone = Multispan(map(π -> ι⋅π, legs(prod)))
  CompositePullback(cospan, cone, prod, eq)
end

function universal(lim::CompositePullback, cone::Multispan)
  factorize(lim.eq, universal(lim.prod, cone))
end

""" Compute pushout by composing a coproduct with a coequalizer.

See also: [`ComposeProductEqualizer`](@ref).
"""
struct ComposeCoproductCoequalizer <: ColimitAlgorithm end

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout{Ob, Diagram<:Multispan, Cocone<:Multicospan{Ob},
    Coprod<:Coproduct, Coeq<:Coequalizer} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  coeq::Coeq
end

function colimit(span::Multispan, ::ComposeCoproductCoequalizer)
  coprod = coproduct(feet(span))
  (π,) = coeq = coequalizer(map(compose, legs(span), legs(coprod)))
  cocone = Multicospan(map(ι -> ι⋅π, legs(coprod)))
  CompositePushout(span, cocone, coprod, coeq)
end

function universal(lim::CompositePushout, cone::Multicospan)
  factorize(lim.coeq, universal(lim.coprod, cone))
end

end
