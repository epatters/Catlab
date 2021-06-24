using Test

@testset "GATs" begin
  include("Meta.jl")
  include("GAT.jl")
end

@testset "Syntax" begin
  include("Syntax.jl")
end

@testset "Presentations" begin
  include("Present.jl")
end

@testset "GATmatch" begin
  include("GATmatch.jl")
end
