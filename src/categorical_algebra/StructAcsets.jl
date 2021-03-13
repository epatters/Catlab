module StructAcsets
export @acset_type, @declare_schema, add_parts!, set_subpart!, schema, idxed, AbstractStructAcset

using MLStyle

using ...Theories, ...Present, ...Syntax
using ...Theories: SchemaDesc, SchemaDescType, SchemaDescTypeType
using ...Meta: strip_lines

# Interface for StructAcsets
############################

abstract type AbstractStructAcset{Schema<:SchemaDescType,Idxed,Ts<:Tuple} end

# StructAcset Code Generation
#############################

q(s) = Expr(:quote,nameof(s))

""" Creates a quoted named tuple used for `StructAcset`s
"""
function pi_type(dom::Vector, F::Function)
  :(NamedTuple{($(q.(dom)...),),Tuple{$(F.(dom)...)}})
end

""" Creates a quoted element of a named tuple used for `StructAcset`s
"""
function pi_type_elt(dom::Vector, f::Function)
  Expr(:tuple, Expr(:parameters, [Expr(:kw, nameof(d), f(d)) for d in dom]...))
end

""" Create the struct declaration for a `StructAcset` from a Presentation
"""
function struct_acset(name::Symbol, parent, p::Presentation{Schema}, idxed=[])
  obs = p.generators[:Ob]
  homs = p.generators[:Hom]
  attr_types = p.generators[:AttrType]
  Ts = nameof.(attr_types)
  attrs = p.generators[:Attr]
  idxed = NamedTuple(x => x ∈ idxed for x in [nameof.(homs);nameof.(attrs)])
  indexed_homs = filter(f -> idxed[nameof(f)], homs)
  indexed_attrs = filter(a -> idxed[nameof(a)], attrs)
  param_type, new_call = if length(attr_types) > 0
    (:($name{$(nameof.(attr_types)...)}), :(new{$(nameof.(attr_types)...)}))
  else
    name, :new
  end
  schema_type = SchemaDescTypeType(p)
  quote
    struct $param_type <: $parent{$schema_type, $idxed, Tuple{$(Ts...)}}
      obs::$(pi_type(obs, _ -> :(Ref{Int})))
      homs::$(pi_type(homs, _ -> :(Vector{Int})))
      attrs::$(pi_type(attrs, a -> :(Vector{$(nameof(codom(a)))})))
      hom_indices::$(pi_type(indexed_homs, _ -> :(Vector{Vector{Int}})))
      attr_indices::$(pi_type(indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Vector{Int}})))
      function $param_type() where {$(nameof.(attr_types)...)}
        $new_call(
          $(pi_type_elt(obs, _ -> :(Ref(0)))),
          $(pi_type_elt(homs, _ -> :(Int[]))),
          $(pi_type_elt(attrs, a -> :($(nameof(codom(a)))[]))),
          $(pi_type_elt(indexed_homs, _ -> :(Vector{Int}[]))),
          $(pi_type_elt(indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Vector{Int}}())))
        )
      end
    end
  end
end

macro declare_schema(head, body)
  decl, extend = @match head begin
    Expr(:(<:), decl, extend::Symbol) => (decl, extend)
    _ => (head, Presentation(FreeSchema))
  end
  name, Ts = @match decl begin
    Expr(:curly, name::Symbol, Ts...) => (name, [Ts...])
    name::Symbol => (name, [])
  end
  :($(esc(name)) = $(GlobalRef(Theories, :parse_schema))(
    $Ts, $(Expr(:quote, body)), $(esc(extend))) )
end

unquote(x::QuoteNode) = x.value

macro acset_type(head)
  head, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(StructAcsets, :AbstractStructAcset))
  end
  name, schema, idxed = @match head begin
    Expr(:call, name, schema, Expr(:kw,:index,idxed)) => (name, schema, unquote.(idxed.args))
    Expr(:call, name, schema) => (name, schema, Symbol[])
    _ => error("Unsupported head for @acset_type")
  end
  abstract_name = Symbol("Abstract" * string(name))
  quote
    $(esc(:eval))($(GlobalRef(StructAcsets, :struct_acset))(
      $(Expr(:quote, name)), $(Expr(:quote, parent)), $(esc(schema)), $idxed))
  end
end

# StructAcset Operations
########################

""" A non-generated convenience wrapper around _add_parts!
"""
add_parts!(acs::AbstractStructAcset, ob::Symbol, n::Int) = _add_parts!(acs, Val{ob}, n)

""" The function that does the heavy lifting for generating the _add_parts!
inner body only has to be compiled once!
"""
function add_parts_body(s::SchemaDesc,idxed::Dict{Symbol,Bool},ob::Symbol)
  code = quote
    m = acs.obs.$ob[]
    nparts = m + n
    newparts = (m+1):m+n
    acs.obs.$ob[] = nparts
  end
  for f in s.homs
    if s.doms[f] == ob
      push!(code.args, quote
              resize!(acs.homs.$f, nparts)
              acs.homs.$f[newparts] .= 0
            end)
    end
    if s.codoms[f] == ob && idxed[f]
      push!(code.args, quote
            resize!(acs.hom_indices.$f, nparts)
            for i in newparts
              acs.hom_indices.$f[i] = Int[]
            end
            end)
    end
    code
  end
  for a in s.attrs
    if s.doms[a] == ob
      push!(code.args,:(resize!(acs.attrs.$a, nparts)))
    end
  end
  push!(code.args, :(newparts))
  code
end

Base.Dict(nt::NamedTuple) = Dict(k => nt[k] for k in keys(nt))

""" This generates the _add_parts! methods for a specific object of a `StructAcset`.
"""
@generated function _add_parts!(acs::AbstractStructAcset{schema,idxed},
                                ::Type{Val{ob}}, n::Int) where {ob, schema, idxed}
  add_parts_body(SchemaDesc(schema),Dict(idxed),ob)
end

""" A non-generated convenience wrapper around _set_subpart!
"""
set_subpart!(acs::AbstractStructAcset, part::Int, f::Symbol, subpart) =
  _set_subpart!(acs, part, Val{f}, subpart)

function set_subpart!(acs::AbstractStructAcset, parts::Vector{Int}, f::Symbol, subparts::Vector)
  for (x,y) in zip(parts,subparts)
    set_subpart!(acs, x, f, y)
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

function set_subpart_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, f::Symbol)
  if f ∈ s.homs
    if idxed[f]
      quote
        @assert 0 <= subpart <= acs.obs.$(s.codoms[f])[]
        old = acs.homs.$f[part]
        acs.homs.$f[part] = subpart
        if old > 0
          @assert deletesorted!(acs.hom_indices.$f, part)
        end
        if subpart > 0
          insertsorted!(acs.hom_indices.$f[subpart], part)
        end
      end
    else
      quote
        @assert 0 <= subpart <= acs.obs.$(s.codoms[f])[]
        acs.homs.$fn[part] = subpart
      end
    end
  else
    if idxed[f]
      quote
        if isassigned(acs.attrs.$f, part)
          old = acs.attrs.$f[part]
          unset_data_index!(acs.attr_indices.$f, old, part)
        end
        acs.attrs.$f[part] = subpart
        set_data_index!(acs.attr_indices.$f, subpart, part)
      end
    else
      :(acs.attrs.$f[part] = subpart)
    end
  end
end

""" This generates the `_set_subparts!` method for a specific arrow (hom/attr) of a StructAcset
"""
@generated function _set_subpart!(acs::AbstractStructAcset{schema,idxed},
                                  part, ::Type{Val{fn}}, subpart) where {schema,idxed,fn}
  set_subpart_body(SchemaDesc(schema),Dict(idxed),fn)
end

end
