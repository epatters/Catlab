module LVRegression

using Turing, Distributions, DifferentialEquations

using MCMCChains, Plots, StatsPlots

using Random

Random.seed!(14);

function lotka_volterra(du,u,p,t)
  x, y = u
  α, β, γ, δ  = p
  du[1] = (α - β*y)x
  du[2] = (δ*x - γ)y
end

p = [1.5, 1.0, 3.0, 1.0]
u0 = [1.0,1.0]
prob1 = ODEProblem(lotka_volterra,u0,(0.0,10.0),p)
sol = solve(prob1,Tsit5())
plot(sol)

sol1 = solve(prob1,Tsit5(),saveat=0.1)
odedata = Array(sol1) + 0.8 * randn(size(Array(sol1)))
plot(sol1, alpha = 0.3, legend = false); scatter!(sol1.t, odedata')

Turing.setadbackend(:forwarddiff)

@model function fitlv(data, prob1)
  σ ~ InverseGamma(2, 3) # ~ is the tilde character

  p ~ product_distribution([Uniform(0,5) for i in 1:4])
  
  prob = remake(prob1, p=p)
  predicted = solve(prob,Tsit5(),saveat=0.1)

  for i = 1:length(predicted)
    data[:,i] ~ MvNormal(predicted[i], σ)
  end
end

model = fitlv(odedata, prob1)

# This next command runs 3 independent chains without using multithreading. 
chain = mapreduce(c -> sample(model, NUTS(.65),1000), chainscat, 1:3)


@model function gdemo(x)
  s ~ InverseGamma(2,3)
  m ~ Normal(0, sqrt(s))

  for i in eachindex(x)
    x[i] ~ Normal(m, sqrt(s))
  end
end

model = gdemo([missing, missing])
c = sample(model, HMC(0.01, 5), 500)
