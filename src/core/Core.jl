using Reexport

include("Meta.jl")
include("GAT.jl")
include("Syntax.jl")
include("Rewrite.jl")
include("Present.jl")
include("GATmatch.jl")

@reexport using .GAT
@reexport using .Syntax
@reexport using .Rewrite
@reexport using .Present
@reexport using .GATmatch
