using MLStyle: @match

@theory ProductSchema{Ob,Hom,Data,Attr} <: MonoidalCategory{Ob,Hom} begin
  Data::TYPE
  Attr(dom::Ob,codom::Data)::TYPE

  """ Composition is given by the action of the profunctor on C.
  """
  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::Data)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Data, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::Ob, a::Attr(A,X))
end

@syntax FreeSchema{ObExpr,HomExpr,DataExpr,AttrExpr} ProductSchema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
end

