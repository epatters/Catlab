module CategoricalAlgebra

using Reexport

include("FreeDiagrams.jl")
include("Limits.jl")
include("Sets.jl")
include("FinSets.jl")
include("Matrices.jl")
include("FinRelations.jl")
include("StructAcsets.jl")
include("CSets.jl")
include("ACSetViews.jl")
include("GraphCategories.jl")
include("StructuredCospans.jl")
include("CommutativeDiagrams.jl")

@reexport using .FreeDiagrams
@reexport using .CommutativeDiagrams
@reexport using .Limits
@reexport using .CSets
@reexport using .ACSetViews
@reexport using .StructuredCospans

end
