export MonoidalCategory, otimes, munit, ⊗, collect, ndims,
  SymmetricMonoidalCategory, FreeSymmetricMonoidalCategory, braid, σ,
  AbstractSymmetricMonoidalFunctor, DictSymmetricMonoidalFunctor,
  MonoidalCategoryWithDiagonals, CartesianCategory, FreeCartesianCategory,
  mcopy, delete, pair, proj1, proj2, Δ, ◊,
  mmerge, create, copair, coproj1, coproj2, ∇, □,
  MonoidalCategoryWithBidiagonals, BiproductCategory, FreeBiproductCategory,
  ClosedMonoidalCategory, FreeClosedMonoidalCategory, hom, ev, curry,
  CartesianClosedCategory, FreeCartesianClosedCategory,
  CompactClosedCategory, FreeCompactClosedCategory, dual, dunit, dcounit, mate,
  DaggerCategory, FreeDaggerCategory, dagger,
  DaggerSymmetricMonoidalCategory, FreeDaggerSymmetricMonoidalCategory,
  DaggerCompactCategory, FreeDaggerCompactCategory,
  TracedMonoidalCategory, FreeTracedMonoidalCategory, trace,
  HypergraphCategory, FreeHypergraphCategory

import Base: collect, ndims

# Monoidal category
###################

""" Theory of *monoidal categories*

To avoid associators and unitors, we assume the monoidal category is *strict*.
By the coherence theorem there is no loss of generality, but we may add a
theory for weak monoidal categories later.
"""
@theory MonoidalCategory{Ob,Hom} <: Category{Ob,Hom} begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  @op (⊗) := otimes
  munit()::Ob

  # Monoid axioms.
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ (A::Ob, B::Ob, C::Ob)
  A ⊗ munit() == A ⊣ (A::Ob)
  munit() ⊗ A == A ⊣ (A::Ob)
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                f::(A → X), g::(B → Y), h::(C → Z))

  # Functorality axioms.
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)))
  id(A ⊗ B) == id(A) ⊗ id(B) ⊣ (A::Ob, B::Ob)
end

# Convenience constructors
otimes(xs::Vector{T}) where T = isempty(xs) ? munit(T) : foldl(otimes, xs)
otimes(x, y, z, xs...) = otimes([x, y, z, xs...])

""" Collect generators of object in monoidal category as a vector.
"""
collect(expr::ObExpr) = [ expr ]
collect(expr::ObExpr{:otimes}) = vcat(map(collect, args(expr))...)
collect(expr::ObExpr{:munit}) = roottypeof(expr)[]

# XXX: We shouldn't have to do this.
roottype(T) = T isa UnionAll ? T : T.name.wrapper
roottypeof(x) = roottype(typeof(x))

""" Number of "dimensions" of object in monoidal category.
"""
ndims(expr::ObExpr) = 1
ndims(expr::ObExpr{:otimes}) = sum(map(ndims, args(expr)))
ndims(expr::ObExpr{:munit}) = 0

function show_unicode(io::IO, expr::Union{ObExpr{:otimes},HomExpr{:otimes}}; kw...)
  Syntax.show_unicode_infix(io, expr, "⊗"; kw...)
end
show_unicode(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

function show_latex(io::IO, expr::Union{ObExpr{:otimes},HomExpr{:otimes}}; kw...)
  Syntax.show_latex_infix(io, expr, "\\otimes"; kw...)
end
show_latex(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

# Symmetric monoidal category
#############################

""" Theory of (strict) *symmetric monoidal categories*
"""
@theory SymmetricMonoidalCategory{Ob,Hom} <: MonoidalCategory{Ob,Hom} begin
  braid(A::Ob, B::Ob)::((A ⊗ B) → (B ⊗ A))
  @op (σ) := braid

  # Involutivity axiom.
  σ(A,B) ⋅ σ(B,A) == id(A ⊗ B) ⊣ (A::Ob, B::Ob)

  # Coherence axioms.
  σ(A,B⊗C) == (σ(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ σ(A,C)) ⊣ (A::Ob, B::Ob, C::Ob)
  σ(A⊗B,C) == (id(A) ⊗ σ(B,C)) ⋅ (σ(A,C) ⊗ id(B)) ⊣ (A::Ob, B::Ob, C::Ob)

  # Naturality axiom.
  (f ⊗ g) ⋅ σ(B,D) == σ(A,C) ⋅ (g ⊗ f) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                          f::(A → B), g::(C → D))
end

@syntax FreeSymmetricMonoidalCategory{ObExpr,HomExpr} SymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

@theory_map AbstractSymmetricMonoidalFunctor(SymmetricMonoidalCategory(ObExpr,HomExpr)),
  dict_impl => DictSymmetricMonoidalFunctor

function show_latex(io::IO, expr::HomExpr{:braid}; kw...)
  Syntax.show_latex_script(io, expr, "\\sigma")
end

# Cartesian category
####################

""" Theory of *monoidal categories with diagonals*

A monoidal category with diagonals is a symmetric monoidal category equipped
with coherent operations of copying and deleting, also known as a supply of
commutative comonoids. Unlike in a cartesian category, the naturality axioms
need not be satisfied.

References:

- Fong & Spivak, 2019, "Supplying bells and whistles in symmetric monoidal
  categories" ([arxiv:1908.02633](https://arxiv.org/abs/1908.02633))
- Selinger, 2010, "A survey of graphical languages for monoidal categories",
  Section 6.6: "Cartesian center"
- Selinger, 1999, "Categorical structure of asynchrony"
"""
@theory MonoidalCategoryWithDiagonals{Ob,Hom} <: SymmetricMonoidalCategory{Ob,Hom} begin
  mcopy(A::Ob)::(A → (A ⊗ A))
  @op (Δ) := mcopy
  delete(A::Ob)::(A → munit())
  @op (◊) := delete

  # Commutative comonoid axioms.
  Δ(A) ⋅ (Δ(A) ⊗ id(A)) == Δ(A) ⋅ (id(A) ⊗ Δ(A)) ⊣ (A::Ob)
  Δ(A) ⋅ (◊(A) ⊗ id(A)) == id(A) ⊣ (A::Ob)
  Δ(A) ⋅ (id(A) ⊗ ◊(A)) == id(A) ⊣ (A::Ob)
  Δ(A) ⋅ σ(A,A) == Δ(A) ⊣ (A::Ob)

  # Coherence axioms.
  Δ(A⊗B) == (Δ(A) ⊗ Δ(B)) ⋅ (id(A) ⊗ σ(A,B) ⊗ id(B)) ⊣ (A::Ob, B::Ob)
  ◊(A⊗B) == ◊(A) ⊗ ◊(B) ⊣ (A::Ob, B::Ob)
  Δ(munit()) == id(munit())
  ◊(munit()) == id(munit())
end

""" Theory of *cartesian (monoidal) categories*

For the traditional axiomatization of products, see
[`CategoryWithProducts`](@ref).
"""
@theory CartesianCategory{Ob,Hom} <: MonoidalCategoryWithDiagonals{Ob,Hom} begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)

  # Definitions of pairing and projections.
  pair(f,g) == Δ(C)⋅(f⊗g) ⊣ (A::Ob, B::Ob, C::Ob, f::(C → A), g::(C → B))
  proj1(A,B) == id(A)⊗◊(B) ⊣ (A::Ob, B::Ob)
  proj2(A,B) == ◊(A)⊗id(B) ⊣ (A::Ob, B::Ob)
  
  # Naturality axioms.
  f⋅Δ(B) == Δ(A)⋅(f⊗f) ⊣ (A::Ob, B::Ob, f::(A → B))
  f⋅◊(B) == ◊(A) ⊣ (A::Ob, B::Ob, f::(A → B))
end

""" Syntax for a free cartesian category.

In this syntax, the pairing and projection operations are defined using
duplication and deletion, and do not have their own syntactic elements.
This convention could be dropped or reversed.
"""
@syntax FreeCartesianCategory{ObExpr,HomExpr} CartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:mcopy}; kw...)
  Syntax.show_latex_script(io, expr, "\\Delta")
end
function show_latex(io::IO, expr::HomExpr{:delete}; kw...)
  Syntax.show_latex_script(io, expr, "\\lozenge")
end

# Biproduct category
####################

""" Theory of *monoidal categories with bidiagonals*

The terminology is nonstandard (is there any standard terminology?) but is
supposed to mean a monoidal category with coherent diagonals and codiagonals.
Unlike in a biproduct category, the naturality axioms need not be satisfied.
"""
@signature MonoidalCategoryWithBidiagonals{Ob,Hom} <:
    MonoidalCategoryWithDiagonals{Ob,Hom} begin
  mmerge(A::Ob)::((A ⊗ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(munit() → A)
  @op (□) := create
end

""" Theory of *biproduct categories*

Mathematically the same as [`SemiadditiveCategory`](@ref) but written
multiplicatively, instead of additively.
"""
@theory BiproductCategory{Ob,Hom} <: MonoidalCategoryWithBidiagonals{Ob,Hom} begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  copair(f::(A → C), g::(B → C))::((A ⊗ B) → C) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)
  coproj1(A::Ob, B::Ob)::(A → (A ⊗ B))
  coproj2(A::Ob, B::Ob)::(B → (A ⊗ B))
  
  # Naturality axioms.
  f⋅Δ(B) == Δ(A)⋅(f⊗f) ⊣ (A::Ob, B::Ob, f::(A → B))
  f⋅◊(B) == ◊(A) ⊣ (A::Ob, B::Ob, f::(A → B))
  ∇(A)⋅f == (f⊗f)⋅∇(B) ⊣ (A::Ob, B::Ob, f::(A → B))
  □(A)⋅f == □(B) ⊣ (A::Ob, B::Ob, f::(A → B))
  
  # Bimonoid axioms. (These follow from naturality + coherence axioms.)
  ∇(A)⋅Δ(A) == (Δ(A)⊗Δ(A)) ⋅ (id(A)⊗σ(A,A)⊗id(A)) ⋅ (∇(A)⊗∇(A)) ⊣ (A::Ob)
  ∇(A)⋅◊(A) == ◊(A) ⊗ ◊(A) ⊣ (A::Ob)
  □(A)⋅Δ(A) == □(A) ⊗ □(A) ⊣ (A::Ob)
  □(A)⋅◊(A) == id(munit()) ⊣ (A::Ob)
end

@syntax FreeBiproductCategory{ObExpr,HomExpr} BiproductCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

  pair(f::Hom, g::Hom) = Δ(dom(f)) ⋅ (f ⊗ g)
  copair(f::Hom, g::Hom) = (f ⊗ g) ⋅ ∇(codom(f))
  proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
  proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
  coproj1(A::Ob, B::Ob) = id(A) ⊗ □(B)
  coproj2(A::Ob, B::Ob) = □(A) ⊗ id(B)
end

function show_latex(io::IO, expr::HomExpr{:mmerge}; kw...)
  Syntax.show_latex_script(io, expr, "\\nabla")
end
function show_latex(io::IO, expr::HomExpr{:create}; kw...)
  Syntax.show_latex_script(io, expr, "\\square")
end

# Closed monoidal category
##########################

""" Theory of (symmetric) *closed monoidal categories*
"""
@signature ClosedMonoidalCategory{Ob,Hom} <: SymmetricMonoidalCategory{Ob,Hom} begin
  # Internal hom of A and B, an object representing Hom(A,B)
  hom(A::Ob, B::Ob)::Ob

  # Evaluation map
  ev(A::Ob, B::Ob)::((hom(A,B) ⊗ A) → B)

  # Currying (aka, lambda abstraction)
  curry(A::Ob, B::Ob, f::((A ⊗ B) → C))::(A → hom(B,C)) ⊣ (C::Ob)
end

""" Syntax for a free closed monoidal category.
"""
@syntax FreeClosedMonoidalCategory{ObExpr,HomExpr} ClosedMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

function show_latex(io::IO, expr::ObExpr{:hom}; kw...)
  print(io, "{")
  show_latex(io, last(expr), paren=true)
  print(io, "}^{")
  show_latex(io, first(expr))
  print(io, "}")
end
function show_latex(io::IO, expr::HomExpr{:ev}; kw...)
  Syntax.show_latex_script(io, expr, "\\mathrm{eval}")
end
function show_latex(io::IO, expr::HomExpr{:curry}; kw...)
  print(io, "\\lambda ")
  show_latex(io, last(expr))
end

# Cartesian closed category
###########################

""" Theory of *cartesian closed categories*, aka CCCs

A CCC is a cartesian category with internal homs (aka, exponential objects).

FIXME: This theory should also extend `ClosedMonoidalCategory`, but multiple
inheritance is not yet supported.
"""
@signature CartesianClosedCategory{Ob,Hom} <: CartesianCategory{Ob,Hom} begin
  hom(A::Ob, B::Ob)::Ob
  ev(A::Ob, B::Ob)::((hom(A,B) ⊗ A) → B)
  curry(A::Ob, B::Ob, f::((A ⊗ B) → C))::(A → hom(B,C)) ⊣ (C::Ob)
end

""" Syntax for a free cartesian closed category.

See also `FreeCartesianCategory`.
"""
@syntax FreeCartesianClosedCategory{ObExpr,HomExpr} CartesianClosedCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

  pair(f::Hom, g::Hom) = Δ(dom(f)) ⋅ (f ⊗ g)
  proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
  proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
end

# Compact closed category
#########################

""" Theory of *compact closed categories*
"""
@theory CompactClosedCategory{Ob,Hom} <: ClosedMonoidalCategory{Ob,Hom} begin
  # Dual A^* of object A
  dual(A::Ob)::Ob

  # Unit of duality, aka the coevaluation map
  dunit(A::Ob)::(munit() → (dual(A) ⊗ A))

  # Counit of duality, aka the evaluation map
  dcounit(A::Ob)::((A ⊗ dual(A)) → munit())

  # Adjoint mate of morphism f.
  mate(f::(A → B))::(dual(B) → dual(A)) ⊣ (A::Ob, B::Ob)
  
  # Axioms for closed monoidal structure.
  hom(A, B) == B ⊗ dual(A) ⊣ (A::Ob, B::Ob)
  ev(A, B) == id(B) ⊗ (σ(dual(A), A) ⋅ dcounit(A)) ⊣ (A::Ob, B::Ob)
  (curry(A, B, f) == (id(A) ⊗ (dunit(B) ⋅ σ(dual(B), B))) ⋅ (f ⊗ id(dual(B)))
   ⊣ (A::Ob, B::Ob, C::Ob, f::((A ⊗ B) → C)))
end

@syntax FreeCompactClosedCategory{ObExpr,HomExpr} CompactClosedCategory begin
  dual(A::Ob) = distribute_unary(involute(new(A)), dual, otimes,
                                 unit=munit, contravariant=true)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  mate(f::Hom) = distribute_mate(involute(new(f)))
  hom(A::Ob, B::Ob) = B ⊗ dual(A)
  ev(A::Ob, B::Ob) = id(B) ⊗ (σ(dual(A), A) ⋅ dcounit(A))
  curry(A::Ob, B::Ob, f::Hom) =
    (id(A) ⊗ (dunit(B) ⋅ σ(dual(B), B))) ⋅ (f ⊗ id(dual(B)))
end

""" Distribute adjoint mates over composition and products.
"""
function distribute_mate(f::HomExpr)
  distribute_unary(
    distribute_unary(f, mate, compose, contravariant=true),
    mate, otimes, contravariant=true)
end

function show_latex(io::IO, expr::ObExpr{:dual}; kw...)
  Syntax.show_latex_postfix(io, expr, "^*")
end
function show_latex(io::IO, expr::HomExpr{:dunit}; kw...)
  Syntax.show_latex_script(io, expr, "\\eta")
end
function show_latex(io::IO, expr::HomExpr{:dcounit}; kw...)
  Syntax.show_latex_script(io, expr, "\\varepsilon")
end
function show_latex(io::IO, expr::HomExpr{:mate}; kw...)
  Syntax.show_latex_postfix(io, expr, "^*")
end

# Dagger category
#################

""" Theory of *dagger categories*
"""
@signature DaggerCategory{Ob,Hom} <: Category{Ob,Hom} begin
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
end

@syntax FreeDaggerCategory{ObExpr,HomExpr} DaggerCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_dagger(involute(new(f)))
end

""" Distribute dagger over composition.
"""
function distribute_dagger(f::HomExpr)
  distribute_unary(f, dagger, compose, unit=id, contravariant=true)
end

""" Theory of *dagger symmetric monoidal categories*

Also known as a [symmetric monoidal dagger
category](https://ncatlab.org/nlab/show/symmetric+monoidal+dagger-category).

FIXME: This theory should also extend `DaggerCategory`, but multiple inheritance
is not yet supported.
"""
@signature DaggerSymmetricMonoidalCategory{Ob,Hom} <: SymmetricMonoidalCategory{Ob,Hom} begin
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
end

@syntax FreeDaggerSymmetricMonoidalCategory{ObExpr,HomExpr} DaggerSymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
end

""" Theory of *dagger compact categories*

In a dagger compact category, there are two kinds of adjoints of a morphism
`f::Hom(A,B)`, the adjoint mate `mate(f)::Hom(dual(B),dual(A))` and the dagger
adjoint `dagger(f)::Hom(B,A)`. In the category of Hilbert spaces, these are
respectively the Banach space adjoint and the Hilbert space adjoint (Reed-Simon,
Vol I, Sec VI.2). In Julia, they would correspond to `transpose` and `adjoint`
in the official `LinearAlegbra` module. For the general relationship between
mates and daggers, see Selinger's survey of graphical languages for monoidal
categories.

FIXME: This theory should also extend `DaggerCategory`, but multiple inheritance
is not yet supported.
"""
@signature DaggerCompactCategory{Ob,Hom} <: CompactClosedCategory{Ob,Hom} begin
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
end

@syntax FreeDaggerCompactCategory{ObExpr,HomExpr} DaggerCompactCategory begin
  dual(A::Ob) = distribute_unary(involute(new(A)), dual, otimes,
                                 unit=munit, contravariant=true)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
  mate(f::Hom) = distribute_mate(involute(new(f)))
end

function show_latex(io::IO, expr::HomExpr{:dagger}; kw...)
  Syntax.show_latex_postfix(io, expr, "^\\dagger")
end

# Traced monoidal category
##########################

""" Theory of *traced monoidal categories*
"""
@signature TracedMonoidalCategory{Ob,Hom} <: SymmetricMonoidalCategory{Ob,Hom} begin
  trace(X::Ob, A::Ob, B::Ob, f::((X ⊗ A) → (X ⊗ B)))::(A → B)
end

@syntax FreeTracedMonoidalCategory{ObExpr,HomExpr} TracedMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  # FIXME: `GAT.equations` fails to identify the implicit equation.
  #trace(X::Ob, A::Ob, B::Ob, f::Hom) = new(X,A,B,f; strict=true)
end

function show_latex(io::IO, expr::HomExpr{:trace}; kw...)
  X, A, B, f = args(expr)
  print(io, "\\operatorname{Tr}_{$A,$B}^{$X} \\left($f\\right)")
end

# Hypergraph category
#####################

""" Theory of *hypergraph categories*

Hypergraph categories are also known as "well-supported compact closed
categories" and "spidered/dungeon categories", among other things.

FIXME: Should also inherit `ClosedMonoidalCategory` and `DaggerCategory`, but
multiple inheritance is not yet supported.
"""
@theory HypergraphCategory{Ob,Hom} <: MonoidalCategoryWithBidiagonals{Ob,Hom} begin
  # Self-dual compact closed category.
  dunit(A::Ob)::(munit() → (A ⊗ A))
  dcounit(A::Ob)::((A ⊗ A) → munit())
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  dunit(A) == create(A) ⋅ mcopy(A) ⊣ (A::Ob)
  dcounit(A) == mmerge(A) ⋅ delete(A) ⊣ (A::Ob)
  (dagger(f) == (id(Y) ⊗ dunit(X)) ⋅ (id(Y) ⊗ f ⊗ id(X)) ⋅ (dcounit(Y) ⊗ id(X))
   ⊣ (A::Ob, B::Ob, f::(A → B)))
end

@syntax FreeHypergraphCategory{ObExpr,HomExpr} HypergraphCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
end
