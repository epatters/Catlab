using Test

using Catlab.Present
using Catlab.Theories: CatDescType, AttrDescType

# Schema
########

A, B = Ob(FreeSchema, :A), Ob(FreeSchema, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

C = AttrType(FreeSchema.AttrType, :C)
x, y = Attr(:x, A, C), Attr(:y, B, C)

@test dom(x) == A
@test codom(x) == C
@test dom(compose(f,y)) == A
@test dom(compose(g,x)) == B

# CatDesc and AttrDesc
######################

@present TheoryDecGraph(FreeSchema) begin
  V::Ob
  E::Ob

  src::Hom(E,V)
  tgt::Hom(E,V)

  X::AttrType

  vdec::Attr(V,X)
  edec::Attr(E,X)
end

CD = CatDescType(TheoryDecGraph)
AD = AttrDescType(TheoryDecGraph)

@test dom(CD,:src) == :E
@test codom(CD,:tgt) == :V

@test dom(AD,:vdec) == :V
@test codom(AD,:edec) == :X
