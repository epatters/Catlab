module StructAcsets
export @acset_type, add_parts!, set_subpart!, schema, Arrow, ParsedSchema

using MLStyle

using ...Theories, ...Present, ...Syntax
using ...Meta: strip_lines

# Interface for StructAcsets
############################

abstract type AbstractStructAcset end

""" Primitive operation for adding parts (without subparts).

Override this function in generated code.
"""
function _add_parts!() end

""" A non-generated convenience wrapper around _add_parts!
"""
add_parts!(acs::AbstractStructAcset, ob::Symbol, n::Int) = _add_parts!(acs, Val{ob}, n)

""" Primitive operation for setting subparts, including setting indexes

Override this function in generated code
"""
function _set_subpart!() end

""" A non-generated convenience wrapper around _set_subpart!
"""
set_subpart!(acs::AbstractStructAcset, part::Int, f::Symbol, subpart) =
  _set_subpart!(acs, part, Val{f}, subpart)

function set_subpart!(acs::AbstractStructAcset, parts::Vector{Int}, f::Symbol, subparts::Vector)
  for (x,y) in zip(parts,subparts)
    set_subpart!(acs, x, f, y)
  end
end

""" Returns the number of parts for an object. Doesn't need to be generated.
"""
nparts(acs::AbstractStructAcset, ob::Symbol) = acs.obs[ob][]

""" Override this function in generated code
"""
function _apply_acset() end

""" This is "functor syntax" for acsets.
"""
(acs::AbstractStructAcset)(x::Symbol) = _apply_acset(acs, Val{x})

""" Parse a Presentation{Schema} from the specialized syntax for it

See also [`@acset_type`](@ref).
"""
function parse_schema(head, body)
  pres = Presentation(FreeSchema)
  name, Ts = @match head begin
    Expr(:curly, name::Symbol, Ts...) => (name, Ts)
    name::Symbol => (name, [])
  end
  lines = @match strip_lines(body) begin
    Expr(:block, lines...) => lines
    _ => error("unsupported body format")
  end
  ps = ParsedSchema(name)
  add_generators!(pres, datas)
  for line in lines
    eval_schema_line(ps, line)
  end
  ps
end

function eval_schema_line(ps,line)
  @match line begin
    name::Symbol => push!(ps.obs,name)
    Expr(:call, name::Symbol, args...) => begin
      push!(ps.obs, name)
      eval_object_args(ps,name,args)
    end
    _ => error("unsupported line in schema")
  end
end

function eval_object_args(ps,name,args)
  for arg in args
    hom, codom, idxed = @match strip_lines(arg) begin
      Expr(:macrocall, m, Expr(:(::), hom, codom)) && if string(m) == "@idx" end =>
        (hom, codom, true)
      Expr(:(::), hom, codom) => (hom, codom, false)
      _ => error("invalid hom expr")
    end
    if codom ∈ ps.datas
      push!(ps.attrs,Arrow(hom,name,codom,idxed))
    else
      push!(ps.homs,Arrow(hom,name,codom,idxed))
    end
  end
end

# StructAcset Code Generation
#############################

name(s::Symbol) = s
name(a::Arrow) = a.name

q(s::Symbol) = Expr(:quote,s)
q(a::Arrow) = q(a.name)

""" Creates a quoted named tuple used for `StructAcset`s
"""
function pi_type(dom::Vector, F::Function)
  :(NamedTuple{($(q.(dom)...),),Tuple{$(F.(dom)...)}})
end

""" Creates a quoted element of a named tuple used for `StructAcset`s
"""
function pi_type_elt(dom::Vector, f::Function)
  Expr(:tuple, Expr(:parameters, [Expr(:kw, name(d), f(d)) for d in dom]...))
end

""" Create the struct declaration for a `StructAcset` from a ParsedSchema
"""
function struct_acset(ps::ParsedSchema)
  indexed_homs = filter(f -> f.idxed, ps.homs)
  indexed_attrs = filter(a -> a.idxed, ps.attrs)
  quote
    struct $(esc(ps.name)){$(ps.datas...)} <: $(GlobalRef(StructAcsets, :AbstractStructAcset))
      obs::$(pi_type(ps.obs, _ -> :(Ref{Int})))
      homs::$(pi_type(ps.homs, _ -> :(Vector{Int})))
      attrs::$(pi_type(ps.attrs, a -> :(Vector{$(a.codom)})))
      hom_indices::$(pi_type(indexed_homs, _ -> :(Vector{Vector{Int}})))
      attr_indices::$(pi_type(indexed_attrs, a -> :(Dict{$(a.codom),Vector{Int}})))
      function $(esc(ps.name)){$(ps.datas...)}() where {$(ps.datas...)}
        new{$(ps.datas...)}(
          $(pi_type_elt(ps.obs, _ -> :(Ref(0)))),
          $(pi_type_elt(ps.homs, _ -> :(Int[]))),
          $(pi_type_elt(ps.attrs, a -> :($(a.codom)[]))),
          $(pi_type_elt(indexed_homs, _ -> :(Vector{Int}[]))),
          $(pi_type_elt(indexed_attrs, a -> :(Dict{$(a.codom),Vector{Int}}())))
        )
      end
    end
    $(GlobalRef(StructAcsets, :schema))(::Type{<:$(esc(ps.name))}) = $ps
    $(Expr(:block, [generate_add_parts(ps,ob) for ob in ps.obs]...))
    $(Expr(:block, [generate_set_subparts(ps,hom,true) for hom in ps.homs]...))
    $(Expr(:block, [generate_set_subparts(ps,attr,false) for attr in ps.attrs]...))
    $(generate_applications(ps))
  end
end

macro acset_type(head, body)
  ps = parse_schema(head, body)
  struct_acset(ps)
end

""" This generates the _add_parts! methods for a specific object of a `StructAcset`.
"""
function generate_add_parts(ps::ParsedSchema, ob::Symbol)
  function update_hom(hom)
    code = Expr(:block)
    hn = name(hom) 
    if hom.dom == ob
      push!(code.args, quote
            resize!(acs.homs.$hn, nparts)
            acs.homs.$hn[newparts] .= 0
            end)
    end
    if hom.codom == ob && hom.idxed
      push!(code.args, quote
            resize!(acs.hom_indices.$hn, nparts)
            for i in newparts
            acs.hom_indices.$hn[i] = Int[]
            end
            end)
    end
    code
  end
  function update_attr(attr)
    if attr.dom == ob
      :(resize!(acs.attrs.$(name(attr)), nparts))
    else
      Expr(:block)
    end
  end
  quote
    function $(GlobalRef(StructAcsets, :_add_parts!))(acs::$(esc(ps.name)), ::Type{Val{$(q(ob))}}, n::Int)
      m = acs.obs.$ob[]
      nparts = m + n
      newparts = (m+1):m+n
      acs.obs.$ob[] = nparts
      $(Expr(:block, update_hom.(ps.homs)...))
      $(Expr(:block, update_attr.(ps.attrs)...))
      newparts
    end
  end
end

""" Insert into sorted vector, preserving the sorting.
"""
function insertsorted!(a::AbstractVector, x)
  insert!(a, searchsortedfirst(a, x), x)
end

""" Delete one occurrence of value from sorted vector, if present.

Returns whether an occurence was found and deleted.
"""
function deletesorted!(a::AbstractVector, x)
  i = searchsortedfirst(a, x)
  found = i <= length(a) && a[i] == x
  if found; deleteat!(a, i) end
  found
end

""" Set key and value for C-set data index.
"""
function set_data_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                         k::K, v::Int) where K
  insertsorted!(get!(d, k) do; Int[] end, v)
end

""" Unset key and value from C-set data index, if it is set.
"""
function unset_data_index!(d::AbstractDict{K,<:AbstractVector{Int}},
                           k::K, v::Int) where K
  if haskey(d, k)
    vs = d[k]
    if deletesorted!(vs, v) && isempty(vs)
      delete!(d, k)
    end
  end
end

""" This generates the `_set_subparts!` method for a specific arrow (hom/attr) of a StructAcset
"""
function generate_set_subparts(ps::ParsedSchema, f::Arrow, is_hom::Bool)
  subpart_type, loc = if is_hom
    (:(Int),:homs)
  else
    (:($(f.codom)),:attrs)
  end
  fn = name(f)
  body = if is_hom
    if f.idxed
      quote
        @assert 0 <= subpart <= acs.obs.$(f.codom)[]
        old = acs.homs.$fn[part]
        acs.homs.$fn[part] = subpart
        if old > 0
          @assert deletesorted!(acs.hom_indices.$fn, part)
        end
        if subpart > 0
          insertsorted!(acs.hom_indices.$fn[subpart], part)
        end
      end
    else
      quote
        @assert 0 <= subpart <= acs.obs.$(f.codom)[]
        acs.homs.$fn[part] = subpart
      end
    end
  else
    if f.idxed
      quote
        if isassigned(acs.attrs.$fn, part)
          old = acs.attrs.$fn[part]
          unset_data_index!(acs.attr_indices.$fn, old, part)
        end
        acs.attrs.$fn[part] = subpart
        set_data_index!(acs.attr_indices.$fn, subpart, part)
      end
    else
      :(acs.attrs.$fn[part] = subpart)
    end
  end
  
  quote
    function $(GlobalRef(StructAcsets, :_set_subpart!))(
      acs::$(esc(ps.name)){$(ps.datas...)}, part::Int,
      ::Type{Val{$(q(f))}}, subpart::$subpart_type) where {$(ps.datas...)}
      $body
    end
  end
end

""" This creates the `_apply_acset` methods used for functor-style application
"""
function generate_applications(ps::ParsedSchema)
  function create_app(loc,x,deref=false)
    body = :(acs.$loc.$x)
    if deref
      body = Expr(:ref, body)
    end
    quote
      function $(GlobalRef(StructAcsets, :_apply_acset))(acs::$(esc(ps.name)), ::Type{Val{$(q(x))}})
        $body
      end
    end
  end
  quote
    $(Expr(:block, map(ob -> create_app(:obs,ob,true), ps.obs)...))
    $(Expr(:block, map(hom -> create_app(:homs,hom,false), name.(ps.homs))...))
    $(Expr(:block, map(attr -> create_app(:attrs,attr,false), name.(ps.attrs))...))
  end
end

end
