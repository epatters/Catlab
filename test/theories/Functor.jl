using Test
using MLStyle
import Catlab.Theories: dom, codom
import Catlab.Syntax: gatmap

@present C1(FreeCategory) begin
  A::Ob
  B::Ob
  C::Ob
  f::Hom(A,B)
  g::Hom(A,B)
  h::Hom(B,C)
end

A,B,C = generators(C1,:Ob)
f,g,h = generators(C1,:Hom)

struct TypeF1 <: AbstractFunctor
end

dom(F::TypeF1) = C1
codom(F::TypeF1) = C1

(F::TypeF1)(x::ObExpr) = x

function Syntax.gatmap(F::TypeF1, morph::HomExpr{:generator})
  @match morph.args[1] begin
    :f => f
    :g => f
    :h => h
  end
end

F1 = TypeF1()

@test gatmap(F1,compose(g,h)) == compose(f,h)

@present C2(FreeSymmetricMonoidalCategory) begin
  A::Ob
  B::Ob
  C::Ob
  f::Hom(A,B)
  g::Hom(A,B)
  h::Hom(B,C)
end

A,B,C = generators(C2,:Ob)
f,g,h = generators(C2,:Hom)

F2 = DictSymmetricMonoidalFunctor(C2,C2,
                                  Dict(:A => A, :B => B, :C => C),
                                  Dict(:f => f, :g => f, :h => h))

@test gatmap(F2,compose(g,h)) == compose(f,h)
@test gatmap(F2,otimes(f,g)) == otimes(f,f)
