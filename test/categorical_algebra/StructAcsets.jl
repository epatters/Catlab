module TestStructAcsets

using Test

using Catlab.Acset
using Catlab.StructAcsets
using Catlab.Theories

# Weighted Graphs
#################

@declare_schema ThGr begin
  V
  E(src::V,tgt::V)
end

@declare_schema ThWGr{T} <: ThGr begin
  weight::Attr(V,T)
end

@abstract_acset_type Gr

@acset_type WGr(ThWGr, index=[:src,:tgt]) <: Gr

src(g::Gr,e::Int) = subpart(g,e,:src)

g = WGr{String}()

@test add_parts!(g,:V,4) == 1:4
@test add_parts!(g,:E,4) == 1:4
set_subpart!(g,[1,2,3,4],:src,[1,2,3,4])
set_subpart!(g,[1,2,3,4],:tgt,[2,3,4,1])
set_subpart!(g,[1,2,3,4],:weight,["a","b","c","d"])
@test src(g,1) == 1

@test g.obs.V[] == 4
@test g.obs.E[] == 4
@test g.homs.src[2] == 2
@test g.attrs.weight[3] == "c"
@test g.hom_indices.src[1] == [1]
@test g.hom_indices.tgt[1] == [4]

# Discrete dynamical systems
############################

@declare_schema TheoryDDS begin
  X(Φ::X)
end

@abstract_acset_type AbstractDDS

@acset_type DDS(TheoryDDS, index=[:Φ]) <: AbstractDDS

@test DDS <: AbstractDDS
@test DDS <: AbstractStructAcset

dds = DDS()
@test nparts(dds, :X) == 0
@test add_part!(dds, :X) == 1
@test nparts(dds, :X) == 1
@test incident(dds, 1, :Φ) == []

set_subpart!(dds, 1, :Φ, 1)
@test subpart(dds, 1, :Φ) == 1
@test incident(dds, 1, :Φ) == [1]

@test add_part!(dds, :X, Φ=1) == 2
@test add_part!(dds, :X, Φ=1) == 3
@test subpart(dds, :Φ) == [1,1,1]
@test subpart(dds, [2,3], :Φ) == [1,1]
@test incident(dds, 1, :Φ) == [1,2,3]

@test has_part(dds, :X)
@test !has_part(dds, :nonpart)
@test has_part(dds, :X, 3)
@test !has_part(dds, :X, 4)
@test has_part(dds, :X, 1:5) == [true, true, true, false, false]

@test has_subpart(dds, :Φ)
@test !has_subpart(dds, :nonsubpart)
@test_throws ArgumentError subpart(dds, 1, :nonsubpart)
@test_throws ArgumentError incident(dds, 1, :nonsuppart)
@test_throws ArgumentError set_subpart!(dds, 1, :nonsubpart, 1)

# Deletion.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,3])
rem_part!(dds, :X, 2)
@test nparts(dds, :X) == 2
@test subpart(dds, :Φ) == [0,2]
@test incident(dds, 1, :Φ) == []
@test incident(dds, 2, :Φ) == [2]
rem_part!(dds, :X, 2)
@test nparts(dds, :X) == 1
@test subpart(dds, :Φ) == [0]
rem_part!(dds, :X, 1)
@test nparts(dds, :X) == 0

dds = DDS()
add_parts!(dds, :X, 4, Φ=[2,3,3,4])
@test_throws ErrorException rem_parts!(dds, :X, [4,1])
rem_parts!(dds, :X, [1,4])
@test subpart(dds, :Φ) == [1,1]
@test incident(dds, 1, :Φ) == [1,2]
@test incident(dds, 2, :Φ) == []

# Error handling when adding parts.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[1,1,1])
@test_throws AssertionError add_part!(dds, :X, Φ=5)
@test nparts(dds, :X) == 3
@test subpart(dds, :Φ) == [1,1,1]
@test_throws AssertionError add_parts!(dds, :X, 2, Φ=[3,6])
@test nparts(dds, :X) == 3
@test incident(dds, 3, :Φ) == []

# Incidence without indexing.
@acset_type UnindexedDDS(TheoryDDS)
dds = UnindexedDDS()
add_parts!(dds, :X, 4, Φ=[3,3,4,4])
@test isempty(keys(dds.hom_indices))
@test incident(dds, 3, :Φ) == [1,2]
@test incident(dds, 4, :Φ) == [3,4]

# Pretty printing
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,3])
s = sprint(show, dds)
@test startswith(s, "ACSet")
@test occursin("X = 1:3", s)
@test occursin("Φ : X → X = ", s)

end
