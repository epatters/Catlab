module CategoricalAlgebra

using Reexport

include("FreeDiagrams.jl")
include("Limits.jl")
include("Sets.jl")
include("FinSets.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("CSets.jl")
include("ACSetViews.jl")
include("GraphCategories.jl")
include("StructuredCospans.jl")
include("CommutativeDiagrams.jl")
include("Automorphisms.jl")
include("DataMigration.jl")
include("DPO.jl")

@reexport using .FreeDiagrams
@reexport using .CommutativeDiagrams
@reexport using .Limits
@reexport using .CSets
@reexport using .ACSetViews
@reexport using .StructuredCospans
@reexport using .DataMigration
@reexport using .Automorphisms
@reexport using .DPO

end
