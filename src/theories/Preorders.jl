export ThinCategory, FreeThinCategory,
  ThinSymmetricMonoidalCategory, FreeThinSymmetricMonoidalCategory,
  Preorder, Poset, FreePreorder, El, Leq, ≤, lhs, rhs, reflexive, transitive,
  Lattice, AlgebraicLattice, meet, ∧, join, ∨, top, ⊤, bottom, ⊥

import Base: join

# Thin category
###############

""" Theory of *thin categories*

Thin categories have at most one morphism between any two objects and are
isomorphic to preorders.
"""
@theory ThinCategory{Ob,Hom} <: Category{Ob,Hom} begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeThinCategory{ObExpr,HomExpr} ThinCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

""" Theory of *thin symmetric monoidal category*

Thin SMCs are isomorphic to commutative monoidal prosets.
"""
@theory ThinSymmetricMonoidalCategory{Ob,Hom} <: SymmetricMonoidalCategory{Ob,Hom} begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeThinSymmetricMonoidalCategory{ObExpr,HomExpr} ThinSymmetricMonoidalCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
end

# Preorder
##########

""" Theory of *preorders*

The generalized algebraic theory of preorders encodes inequalities ``A≤B`` as
dependent types ```Leq(A,B)`` and the axioms of reflexivity and transitivity as
term constructors.
"""
@theory Preorder{El,Leq} begin
  El::TYPE
  Leq(lhs::El, rhs::El)::TYPE
  @op (≤) := Leq

  reflexive(A::El)::(A≤A)
  transitive(f::(A≤B), g::(B≤C))::(A≤C) ⊣ (A::El, B::El, C::El)

  f == g ⊣ (A::El, B::El, f::(A≤B), g::(A≤B))
end

@syntax FreePreorder{ObExpr,HomExpr} Preorder begin
  transitive(f::Leq, g::Leq) = associate(new(f,g; strict=true))
end

# TODO: There should be an isomorphism in the category GAT between the theories
# of preorders and thin categories.
#
# @functor F(Preorder(El, Leq))::ThinCategory(Ob, Hom) begin
#   El ↦ Ob
#   Leq ↦ Hom
#   reflexive ↦ id
#   transitive ↦ compose
# end

""" Theory of *partial orders* (posets)
"""
@theory Poset{El,Leq} <: Preorder{El,Leq} begin
  A == B ⊣ (A::El, B::El, f::(A≤B), g::(B≤A))
end

# Lattice
#########

""" Theory of *lattices* as posets

A (bounded) lattice is a poset with all finite meets and joins. Viewed as a thin
category, this means that the category has all finite products and coproducts,
hence the names for the inequality constructors in the theory. Compare with
[`CartesianCategory`](@ref) and [`CocartesianCategory`](@ref).

This is one of two standard axiomatizations of a lattice, the other being
[`AlgebraicLattice`](@ref).
"""
@theory Lattice{El,Leq} <: Poset{El,Leq} begin
  @op begin
    (∧) := meet
    (⊤) := top
    (∨) := join
    (⊥) := bottom
  end

  # Meet = greatest lower bound.
  meet(A::El, B::El)::El
  proj1(A::El, B::El)::((A ∧ B) ≤ A)
  proj2(A::El, B::El)::((A ∧ B) ≤ B)
  pair(f::(C ≤ A), g::(C ≤ B))::(C ≤ (A ∧ B)) ⊣ (A::El, B::El, C::El)

  # Top = maximum.
  top()::El
  delete(A::El)::(A ≤ ⊤())

  # Join = least upper bound.
  join(A::El, B::El)::El
  coproj1(A::El, B::El)::(A ≤ (A ∨ B))
  coproj2(A::El, B::El)::(B ≤ (A ∨ B))
  copair(f::(A ≤ C), g::(B ≤ C))::((A ∨ B) ≤ C) ⊣ (A::El, B::El, C::El)

  # Bottom = minimum.
  bottom()::El
  create(A::El)::(⊥() ≤ A)
end

""" Theory of *lattices* as algebraic structures

This is one of two standard axiomatizations of a lattice, the other being
[`Lattice`](@ref). Because the partial order is not present, this theory is
merely an algebraic theory (no dependent types).

The partial order is recovered as ``A ≤ B`` iff ``A ∧ B = A`` iff ``A ∨ B = B``.
This definition could be reintroduced into a generalized algebraic theory using
an equality type `Eq(lhs::El, rhs::El)::TYPE` combined with term constructors
``meet_leq(eq::Eq(A∧B, A))::(A ≤ B)` and `join_leq(eq::Eq(A∨B, B))::(A ≤ B)`. We
do not employ that trick here because at that point it is more convenient to
just start with the poset structure, as in [`Lattice`](@ref).
"""
@theory AlgebraicLattice{El} begin
  @op begin
    (∧) := meet
    (⊤) := top
    (∨) := join
    (⊥) := bottom
  end

  # Meet/top as idempotent, commutative, associative, unital operation.
  meet(A::El, B::El)::El
  top()::El
  (A ∧ B) ∧ C == A ∧ (B ∧ C) ⊣ (A::El, B::El, C::El)
  A ∧ ⊤() == A ⊣ (A::El)
  ⊤() ∧ A == A ⊣ (A::El)
  A ∧ B == B ∧ A ⊣ (A::El, B::El)
  A ∧ A == A ⊣ (A::El)

  # Join/bottom as idempotent, commutative, associative, unital operation.
  join(A::El, B::El)::El
  bottom()::El
  (A ∨ B) ∨ C == A ∨ (B ∨ C) ⊣ (A::El, B::El, C::El)
  A ∨ ⊥() == A ⊣ (A::El)
  ⊥() ∨ A == A ⊣ (A::El)
  A ∨ B == B ∨ A ⊣ (A::El, B::El)
  A ∨ A == A ⊣ (A::El)

  # Absorption laws.
  A ∨ (A ∧ B) == A ⊣ (A::El, B::El)
  A ∧ (A ∨ B) == A ⊣ (A::El, B::El)
end
