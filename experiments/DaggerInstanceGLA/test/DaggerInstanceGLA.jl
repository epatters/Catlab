using Catlab.LinearAlgebra.GraphicalLinearAlgebra, 
      DaggerInstanceGLA, Catlab, Catlab.Doctrines
using Test

V, W = Ob(FreeLinearFunctions, :V, :W)
f, g, h = Hom(:f, V, W), Hom(:g, V, W), Hom(:h, W, W)

fmap = LinearMap([1 1 1 1; 2 2 2 3; 3 3 3 3.0])
gmap = LinearMap([3 1 1 1; -1 -1 -1 -1; 0 2 0 0.0])
hmap = LinearMap([1 4 -1; -1 1 0; 1 1 -1.0])

fop = MatrixThunk(fmap)
gop = MatrixThunk(gmap)
hop = MatrixThunk(hmap)

d = Dict(f=>fop, g=>gop, h => hop, V => DagDom(4), W=>DagDom(3))
F(ex) = functor((DagDom, MatrixThunk), ex, generators=d)

dmap = Dict(f=>fmap, g=>gmap, h => hmap, V => LinearMapDom(4), W=>LinearMapDom(3))
Fmap(ex) = functor((LinearMapDom, LinearMap), ex, generators=dmap)

M = plus(f,g)⋅h
N = adjoint(g)⋅f⋅mcopy(W)+h⋅mcopy(W)
O = (adjoint(g)⊕f)+(h⊕(g⋅adjoint(f)))

expressions = [M,N,O]

for expression in expressions
  @test Matrix(collect(F(expression).thunk)) == 
          Matrix(Fmap(expression))
end
