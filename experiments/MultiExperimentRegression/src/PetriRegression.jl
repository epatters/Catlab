module PetriRegression

using Turing, Distributions, DifferentialEquations

using MCMCChains, Plots, StatsPlots

using AlgebraicPetri

using Catlab.CategoricalAlgebra.CSets

struct ReactionData
  dt :: Float64
  # Measurements of concentrations of each species at each time
  measurements :: Array{Float64,2}
  # Uniform priors over the rates
  priors :: Vector{Tuple{Float64,Float64}}
end

Turing.setadbackend(:forwarddiff)

@model function fit_rates(measurements, prob1)
  σ ~ InverseGamma(2,3)

  p ~ product_distribution([Uniform(0,10) for i in 1:3])

  prob = remake(prob1,p=p)
  predicted = solve(prob,Tsit5(),saveat=0.1)

  for i = 1:length(predicted)
    measurements[:,i] ~ MvNormal(predicted[i], σ)
  end
end
  
lv = PetriNet(2,(1,(1,1)),((1,2),(2,2)),(2,()))

u0 = [1.,1.]
p = [1.,2.,3.]
prob = ODEProblem(vectorfield(lv),u0,(0.,10.),p)
sol = solve(prob,Tsit5(),saveat=0.1)

plot(sol)

σ = 0.2
dt = 0.1
measurements = Array(sol) + σ * randn(size(Array(sol)))
plot(sol, alpha=0.5, legend = false); scatter!(sol.t, measurements')
priors = [(0.,5.),(0.,5.),(0.,5.)]

model = fit_rates(measurements, prob)
sample(model,HMC(0.1,5),1000)

end
