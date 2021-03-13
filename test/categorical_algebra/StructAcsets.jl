module TestStructAcsets

using Test

using Catlab.StructAcsets
using Catlab.Theories

@declare_schema ThGr begin
  V
  E(src::V,tgt::V)
end

@declare_schema ThWGr{T} <: ThGr begin
  weight::Attr(V,T)
end

@acset_type WGr(ThWGr, index=[:src,:tgt])

g = WGr{String}()

@test add_parts!(g,:V,4) == 1:4
@test add_parts!(g,:E,4) == 1:4
set_subpart!(g,[1,2,3,4],:src,[1,2,3,4])
set_subpart!(g,[1,2,3,4],:tgt,[2,3,4,1])
set_subpart!(g,[1,2,3,4],:weight,["a","b","c","d"])

@test g.obs.V[] == 4
@test g.obs.E[] == 4
@test g.homs.src[2] == 2
@test g.attrs.weight[3] == "c"
@test g.hom_indices.src[1] == [1]
@test g.hom_indices.tgt[1] == [4]

end
