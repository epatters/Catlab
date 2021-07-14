module MultiExperimentRegression

using Catlab
using Catlab.CategoricalAlgebra.FreeDiagrams
using Turing

const MESpec = Multicospan{FinSet{Int,Int},FinFunction{Int,Int}}

const MEData = Vector{Tuple{Array{Float64,2},Vector{Float64}}}

@model function me_lin_model(a::Float64,b::Float64,spec::MESpec,data::MEData)
  v ~ InverseGamma(a,b)
  σ = sqrt(v)
  M = length(apex(spec))
  β = Vector{Float64}(undef, M)
  for i in 1:M
    β[i] ~ Normal(0,σ)
  end
  N = length(legs(spec))
  for i in 1:N
    f = legs(spec)[i]
    (X,y) = data[i]
    for j in 1:length(y)
      y[j] ~ Normal(sum(β[f(k)] * X[j,k] for k in dom(f)),σ)
    end
  end
end

end # module
