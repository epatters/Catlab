module TestTheories

using Test
using Catlab.Theories
using Catlab.Syntax
using Catlab.Present

sexpr(expr::GATExpr) = sprint(show_sexpr, expr)
unicode(expr::GATExpr) = sprint(show_unicode, expr)
latex(expr::GATExpr) = sprint(show_latex, expr)

@testset "Categories" begin
  include("Category.jl")
end

@testset "MonoidalCategories" begin
  include("Monoidal.jl")
  include("MonoidalAdditive.jl")
end

@testset "Preorders" begin
  include("Preorders.jl")
end

@testset "Schemas" begin
  include("Schema.jl")
end

@testset "Functors" begin
  include("Functor.jl")
end

end
