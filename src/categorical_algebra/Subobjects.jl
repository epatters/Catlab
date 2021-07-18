""" The algebra of subobjects in a topos.

This module defines the interface for subobjects as well as some generic
algorithm for computing subobjects using limits and colimits. Concrete instances
such as subsets (subobjects in Set or FinSet) and sub-C-sets (subobjects in
C-Set) are defined elsewhere.
"""
module Subobjects
export Subobject, ob, hom, meet, ∧, join, ∨, top, ⊤, bottom, ⊥,
  SubOpAlgorithm, SubOpWithLimits

using AutoHashEquals
using StaticArrays: SVector

using ...GAT, ...Theories, ..Limits
import ...Theories: ob, hom, meet, ∧, join, ∨, top, ⊤, bottom, ⊥

# Theories
##########

""" Theory of lattice of subobjects in a topos.

The axioms are omitted since this theory is the same as the theory
[`Catlab.Theories.AlgebraicLattice`](@ref) except that the lattice elements are
dependent on another type.
"""
@signature SubobjectLattice{Ob,Sub} begin
  Ob::TYPE
  Sub(ob::X)::TYPE

  @op begin
    (∧) := meet
    (∨) := join
    (⊤) := top
    (⊥) := bottom
  end

  meet(A::Sub(X), B::Sub(X))::Sub(X) ⊣ (X::Ob)
  join(A::Sub(X), B::Sub(X))::Sub(X) ⊣ (X::Ob)
  top(X::Ob)::Sub(X)
  bottom(X::Ob)::Sub(X)
end

# Data types
############

""" Subobject in a topos.

A subobject of an object ``X`` is a monomorphism into ``X``.
"""
@auto_hash_equals struct Subobject{Hom}
  hom::Hom
end

hom(sub::Subobject) = sub.hom
ob(sub::Subobject) = codom(hom(sub))

# Algorithms
############

""" Abstract type for algorithm to compute operation(s) on subobjects.
"""
abstract type SubOpAlgorithm end

""" Algorithm to compute subobject operations using limits and/or colimits.
"""
struct SubOpWithLimits <: SubOpAlgorithm end

""" Meet (intersection) of subobjects.
"""
function meet(A::Subobject, B::Subobject, ::SubOpWithLimits)
  meet(SVector(A,B), SubOpWithLimits())
end
function meet(As::AbstractVector{<:Subobject}, ::SubOpWithLimits)
  fs = map(hom, As)
  lim = pullback(fs)
  Subobject(compose(first(legs(lim)), first(fs))) # Arbitrarily use first leg.
end

""" Join (union) of subobjects.
"""
function join(A::Subobject, B::Subobject, ::SubOpWithLimits)
  join(SVector(A,B), SubOpWithLimits())
end
function join(As::AbstractVector{<:Subobject}, ::SubOpWithLimits)
  fs = map(hom, As)
  lim = pullback(fs)
  colim = pushout(legs(lim))
  Subobject(copair(colim, fs))
end

""" Top (full) subobject.
"""
top(X, ::SubOpWithLimits) = Subobject(id(X))

""" Bottom (empty) subobject.
"""
bottom(X::T, ::SubOpWithLimits) where T = Subobject(create(initial(T), X))

end
