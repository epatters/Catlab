module TestStructAcsets

using Test

using Catlab.CategoricalAlgebra.StructAcsets

@acset_type WeightedGraph{T} begin
  V
  E(@idx(src::V),@idx(tgt::V),weight::T)
end

g = WeightedGraph{String}()

@test add_parts!(g,:V,4) == 1:4
@test add_parts!(g,:E,4) == 1:4
set_subpart!(g,[1,2,3,4],:src,[1,2,3,4])
set_subpart!(g,[1,2,3,4],:tgt,[2,3,4,1])
set_subpart!(g,[1,2,3,4],:weight,["a","b","c","d"])

@test g(:V) == 4
@test g(:E) == 4
@test g(:src)[2] == 2
@test g(:weight)[3] == "c"
@test g.hom_indices.src[1] == [1]
@test g.hom_indices.tgt[1] == [4]

end
