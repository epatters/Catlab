module TestCategoricalAlgebra

using Test

@testset "FreeDiagrams" begin
  include("FreeDiagrams.jl")
end

@testset "CommutativeDiagrams" begin
  include("CommutativeDiagrams.jl")
end

@testset "Limits" begin
  include("Limits.jl")
end

@testset "Matrices" begin
  include("Matrices.jl")
end

@testset "Sets" begin
  include("Sets.jl")
  include("FinSets.jl")
end

@testset "Relations" begin
  include("FinRelations.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

@testset "CSets" begin
  include("CSetDataStructures.jl")
  include("CSets.jl")
  include("ACSetViews.jl")
end

@testset "StructuredCospans" begin
  include("StructuredCospans.jl")
end

@testset "CatElements" begin
  include("CatElements.jl")
end

end
