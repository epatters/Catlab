module DaggerAMC

import Base: +
using AutoHashEquals

export DagDom, ThunkArr, copy,
       dom, codom, compose, id, oplus, mzero,
       zero, ⊕, braid
       # To implement
       # mcopy, delete, plus, zero,
       
using Dagger
using LinearAlgebra
#using Catlab.Doctrines.AdditiveMonoidal
using Catlab, Catlab.Doctrines, Catlab.Programs
import Catlab.Doctrines:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, braid,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, zero, coplus, cozero, meet, top, join, bottom


@auto_hash_equals struct DagDom
  N::Int
end

# This structure was created to keep track of dom and codom information.
# This information can be updated efficiently, and keeping it here keeps
# LinearFunctions from having to think the thunk each time the dom or codom
# is queried

struct ThunkArr 
  input::Array{Tuple{Int64,Int64},1}
  output::Array{Int64,1}
  thunks::Array{Thunk,1}
end

input_nodes(f::ThunkArr) = begin
  input_n = Set{Int64}()
  for port in f.input
    push!(input_n,port[1])
  end
  return input_n
end

copy(A::ThunkArr) = begin
  n_thunks = [Thunk(x.f, x.inputs...) for x in A.thunks]
  n_input = A.input
  n_output = A.output
  ThunkArr(n_input, n_output, n_thunks)
end

ThunkArr(A::AbstractArray) = begin
  id_thunks = [delayed(identity)(A[x]) for x in 1:length(A)[1]]
  id_input = []
  id_output = Array(1:length(A))
  ThunkArr(id_input, id_output, id_thunks) 
end

ThunkArr(A) = begin
  ThunkArr([A])
end

@instance AdditiveSymmetricMonoidalCategory(DagDom, ThunkArr) begin
  zero(V::DagDom)   = DagDom(0) 
  mzero(::Type{DagDom}) = DagDom(0)
  dom(f::ThunkArr)    = size(f.input)[1]
  codom(f::ThunkArr)  = size(f.output)[1]
  
  compose(f::ThunkArr,g::ThunkArr) = begin
    add_ind   = (x,n) -> x+n
    cf = f
    cg = g
    n_output  = add_ind.(cf.output,size(cg.thunks)[1])
    n_input   = cg.input
    # f_inputs stores what thunks will be passed in from g
    f_inputs  = Dict(x => Array{Thunk}(undef, length(cf.thunks[x].inputs)) for x in input_nodes(cf))
    # Fill out the values that will be passed in from g
    for port_num in 1:length(cf.input)
      port = cf.input[port_num]
      g_node = cg.thunks[cg.output[port_num]]
      f_inputs[port[1]][port[2]] = g_node
    end
    for (key,g_in) in f_inputs
      cf.thunks[key].inputs = Tuple(g_in)
    end

    n_thunks = vcat(cg.thunks,cf.thunks)
    ThunkArr(n_input, n_output, n_thunks)
  end

  oplus(V::DagDom, W::DagDom) = DagDom(V.N + W.N)

  # Make copies of thunks to keep from variable interference
  oplus(f::ThunkArr, g::ThunkArr) = begin
    add_tup = (x,n) -> (x[1]+n,x[2])
    add_ind = (x,n) -> x+n
    cf = f
    cg = g
    n_thunks  = vcat(cf.thunks, cg.thunks)
    n_input   = vcat(cf.input, add_tup.(cg.input,size(cf.thunks)[1]))
    n_output  = vcat(cf.output, add_ind.(cg.output,size(cf.thunks)[1]))
    ThunkArr(n_input, n_output, n_thunks)
  end
  
  id(V::DagDom) = begin
    add_port = x -> (x,1)
    id_thunks = [delayed(identity)(1) for x in 1:V.N]
    id_input = add_port.(Array(1:V.N))
    id_output = Array(1:V.N)
    ThunkArr(id_input, id_output, id_thunks)
  end

  braid(V::DagDom, W::DagDom) = begin
    vw_id = id(V.N + W.N)
    vw_id.output = vcat(vw_id.output[V.N+1:end],vw_id.output[1:V.N])
    return vw_id
  end

  #adjoint(f::MatrixThunk) = MatrixThunk(delayed(adjoint)(f.thunk), f.codom, f.dom)
  #+(f::MatrixThunk, g::MatrixThunk) = MatrixThunk(delayed(+)(f.thunk, g.thunk), f.dom, f.codom)

  #compose(f::MatrixThunk, g::MatrixThunk) = 
  #  MatrixThunk(delayed(*)(g.thunk,f.thunk), g.dom, f.codom)
  #id(V::DagDom) = MatrixThunk(LMs.UniformScalingMap(1, V.N))

  #oplus(V::DagDom, W::DagDom) = DagDom(V.N + W.N)
  #oplus(f::MatrixThunk, g::MatrixThunk) = 
  #  MatrixThunk(delayed((f,g)->LMs.BlockDiagonalMap(f,g))(f.thunk, g.thunk), 
  #              f.dom+g.dom, f.codom+g.codom)
  #
  #mzero(::Type{DagDom}) = DagDom(0)
  #braid(V::DagDom, W::DagDom) =
  #MatrixThunk(LinearMap(braid_lm(V.N), braid_lm(W.N), W.N+V.N, V.N+W.N))

  #mcopy(V::DagDom)  = MatrixThunk(LinearMap(mcopy_lm, plus_lm, 2*V.N, V.N))
  #delete(V::DagDom) = MatrixThunk(LinearMap(delete_lm, zero_lm(V.N), 0, V.N))
  #plus(V::DagDom)   = MatrixThunk(LinearMap(plus_lm, mcopy_lm, V.N, 2*V.N))

  #plus(f::MatrixThunk, g::MatrixThunk) = f+g
  #scalar(V::DagDom, c::Number) = MatrixThunk(LMs.UniformScalingMap(c, V.N))
  #antipode(V::DagDom) = scalar(V, -1)
end

#braid_lm(n::Int) = x::AbstractVector -> vcat(x[n+1:end], x[1:n])
#mcopy_lm(x::AbstractVector) = vcat(x, x)
#delete_lm(x::AbstractVector) = eltype(x)[]
#plus_lm(x::AbstractVector) = begin
#  n = length(x) ÷ 2
#  x[1:n] + x[n+1:end]
#end
#zero_lm(n::Int) = x::AbstractVector -> zeros(eltype(x), n)

end
