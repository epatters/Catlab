# module TestCatElements
using Test
using Catlab, Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra,
  Catlab.CategoricalAlgebra.FinSets, Catlab.CategoricalAlgebra.CatElements


@testset "Elements" begin
arr = @acset Graph begin
    V = 2
    E = 1
    src=1
    tgt=2
end

elarr = elements(arr)
@testset "Arrow Elements" begin
    @test nparts(elarr, :El)  == 3
    @test nparts(elarr, :Arr) == 2
    @test nparts(elarr, :Ob)  == 2
    @test nparts(elarr, :Hom) == 2
    @test elarr[:, :πₑ]    == [1,1,2]
    @test elarr[:, :πₐ]    == [1,2]
    @test elarr[:, :src]   == [3,3]
    @test elarr[:, :tgt]   == [1,2]
    @test elarr[:, :nameo] == [:V, :E]
    @test elarr[:, :nameh] == [:src, :tgt]
    @test elarr[:, :dom]   == [2, 2]
    @test elarr[:, :cod]   == [1, 1]
end


p₀ = @acset Graph begin
    V = 2
    E = 2
    src=[1,2]
    tgt=[2,1]
end

ThPetri, obmap, hommap = Presentation(elements(p₀))
Petri = ACSetType(ThPetri)

sir_eltsch = @acset Petri begin
    V_1 = 3
    V_2 = 2
    E_1 = 3
    E_2 = 3

    src_E_1 = [1,2,2]
    tgt_E_1 = [1,1,2]

    src_E_2 = [1,1,2]
    tgt_E_2 = [2,2,3]
end

@testset "DiBipartite Elements" begin
    @test length(generators(ThPetri)) == 8
    @test nparts(sir_eltsch, :V_1) == 3 
    @test nparts(sir_eltsch, :V_2) == 2
    @test nparts(sir_eltsch, :E_1) == 3
    @test nparts(sir_eltsch, :E_2) == 3
    @test sir_eltsch[:, :src_E_2] == [1,1,2]
end
end
