module TestGATMatch

import Test: @test, @test_throws
import LinearAlgebra: I

using Catlab.GAT
import Catlab.Syntax: @syntax, GATExpr, head, gat_typeof, to_json_sexpr, parse_json_sexpr

using Catlab.Theories
import Catlab.Theories: id, compose, composeH, composeV, HomVExpr, HomHExpr, Hom2Expr, Ob, Hom, Hom2, HomH, HomV
import Catlab.Present: @present
using Catlab.GATmatch

@syntax FreeCategory{ObExpr,HomExpr} Category begin

end

@present Ex1(FreeCategory) begin
    (A,B,C)::Ob
    f::Hom(A,B)
    g::Hom(B,C)
    h::Hom(A,A)
    finv::Hom(B,A)

    compose(f, finv) == id(A)
end

function idreduce(homexpr)
    @gatmatch homexpr begin
    compose(F,id(β)) ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => F
    compose(id(α),F) ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => F
    F => F
    end
end

function idreduce_pure(homexpr)
  @gatmatch_pure homexpr begin
    compose(F,id(β)) ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => F
    compose(id(α),F) ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => F
    F => F
  end
end

f,g,h,A,B,C = Ex1[:f],Ex1[:g],Ex1[:h],Ex1[:A],Ex1[:B],Ex1[:C]

@test idreduce(compose(f,id(B))) == f
@test idreduce(compose(id(B),g)) == g
@test idreduce_pure(compose(id(B),g)) == g

function left_idexpand(homexpr)
    @gatmatch homexpr begin
        F ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => compose(id(α),F)
        F => F
    end
end

@test left_idexpand(g) == compose(id(B),g)
@test left_idexpand(id(A)) == compose(id(A),id(A))

"""
Example of a trivial expression pattern match but nontrivial type context
"""
function double_endomorphism(homexpr)
    @gatmatch homexpr begin
        F ⊣ (α::Ob,F::Hom(α,α)) => compose(F,F)
        F => F
    end
end

@test double_endomorphism(f) == f
@test double_endomorphism(h)==compose(h,h)


"""
Interpret the category of 2D matrices with matrix multiplication
"""
lookup = Dict(
    A => 2,
    B => 1,
    C => 3,
    f => reshape([1, 2], 2, 1),
    g => reshape([10, 100, 1000], 1, 3),
    h => [1 0; 0 -1])


"""
Base case: look up value of look up ground term
If we could match for "literal" values then we could
scrap the dictionary and put its data in the gatmatch expression

This doesn't work for composing 3 things if associate_strict=true.
Need to match variadic arguments in that case, e.g.
  compose(x,y,z) => interpret(x) * interpret(compose(y,z)
"""
function interpret(homexpr)
  @gatmatch homexpr begin
      compose(x,y) ⊣ (α::Ob,β::Ob,γ::Ob, x::Hom(α,β), y::Hom(β,γ)) => interpret(x) * interpret(y)
      id(ob) ⊣ (ob::Ob) => Matrix(1I, interpret(ob), interpret(ob))
      f => lookup[f]
  end
end

@test interpret(compose(f,compose(g, id(C)))) == [10 100 1000;
                                                  20 200 2000]

@theory Groupoid{Ob, Hom} <: Category{Ob, Hom} begin
  inv(f::Hom(A,B))::Hom(B,A) ⊣ (A::Ob,B::Ob)
  compose(inv(f), f) == id(B) ⊣ (A::Ob, B::Ob, f::Hom(A,B))
  compose(f, inv(f)) == id(A) ⊣ (A::Ob, B::Ob, f::Hom(A,B))
  inv(id(A)) == id(A) ⊣ (A::Ob)
end

@syntax FreeGroupoid{ObExpr, HomExpr} Groupoid begin end


@present Ex2(FreeGroupoid) begin
  (α,β,γ)::Ob
  ϕ::Hom(α,β)
  ψ::Hom(β,γ)
end

function invreduce(homexpr)
  @gatmatch homexpr begin
      compose(f,inv(f)) ⊣ (A::Ob,B::Ob,f::Hom(A,B)) => id(A)
      compose(inv(f),f) ⊣ (A::Ob,B::Ob,f::Hom(A,B)) => id(B)
      F => F
  end
end

@test invreduce(compose(Ex2[:ϕ],inv(Ex2[:ϕ]))) == id(Ex2[:α])

# Test the "otherwise" condition
for bad in [compose(Ex2[:ϕ],inv(Ex2[:ψ])), Ex2[:α]]
  @test invreduce(bad) == bad
end

"""
Test error raised when we fail to match
"""
function invreduce_no_otherwise(homexpr)
  @gatmatch homexpr begin
      compose(f,inv(f)) ⊣ (A::Ob,B::Ob,f::Hom(A,B)) => id(A)
      compose(inv(f),f) ⊣ (A::Ob,B::Ob,f::Hom(A,B)) => id(B)
  end
end

@test_throws ErrorException("No match found for ϕ") invreduce_no_otherwise(Ex2[:ϕ])

@syntax FreeDoubleCategory{ObExpr,HomVExpr, HomHExpr,Hom2Expr} DoubleCategory begin
end

"""

A -- t --> X -- t′ --> C -- t′′ --> M
|          |           |            |
l          r           r′          r′′
|          |           |            |
v          v           v            v
B -- b --> Y -- b′-->  D -- b′′ --> N
|          |
l′        br
|          |
v          v
P -- b′--> Q
|          |
l′′        br′
|          |
v          v
R -- b′′-->S

"""

@present Ex3(FreeDoubleCategory) begin
  (A,B,C,D,M,N,P,Q,R,S,X,Y)::Ob
  t  ::HomH(A,X)
  b  ::HomH(B,Y)
  l  ::HomV(A,B)
  r  ::HomV(X,Y)
  t′ ::HomH(X,C)
  b′ ::HomH(Y,D)
  r′ ::HomV(C,D)
  t′′::HomH(C,N)
  b′′::HomH(R,S)
  r′′::HomV(M,N)
  l′ ::HomV(B,P)
  l′′::HomV(P,R)
  br ::HomV(Y,Q)
  br′::HomV(Q,S)

  abxy::Hom2(t,b,l,r)
  xcyd::Hom2(t′,b′,r,r′)
  cmdn::Hom2(t′′,b′′,r′,r′′)
  bypq::Hom2(b,b′,l′,br)
  pqrs::Hom2(b′,b′′,l′′,br′)

  # Condensing A and B to a triangle
  aal::HomV(A,A)
  aab::HomH(A,Y)
  axy::Hom2(t,aab,aal,r)

end


function asc_homH(homexpr)
  @gatmatch homexpr begin
    composeH(square1,composeH(square2,square3)) ⊣ (square1::Hom2(top,bot,left,right),left::HomV(same,same)) => composeH(composeH(square1,square2), square3)
      F => F
  end
end

# When the first square is a triangle, it gets reassociated
doublehom_aa = composeH(Ex3[:axy], composeH(Ex3[:xcyd],Ex3[:cmdn]))
@test asc_homH(doublehom_aa) == composeH(composeH(Ex3[:axy], Ex3[:xcyd]),Ex3[:cmdn])

# Normal square one doesn't
doublehom = composeH(Ex3[:abxy], composeH(Ex3[:xcyd],Ex3[:cmdn]))
@test asc_homH(doublehom) == doublehom

# For this last one, GATMatch_pure throws error:
# - no method matching (::Catlab.Syntax.var"#parse_impl#46"{typeof(identity),Module,Dict{Symbol,Int64},Catlab.Syntax.var"#43#48",typeof(identity),Bool})(::Expr, ::Type{Val{:expr}})

end