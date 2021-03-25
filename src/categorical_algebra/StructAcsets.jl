module StructAcsets
export @acset_type, @abstract_acset_type, @declare_schema,
  add_parts!, set_subpart!, subpart, AbstractStructAcset

using MLStyle
using StaticArrays: StaticArray

using ..Acset
using ..IndexUtils
using ...Theories, ...Present, ...Syntax
using ...Theories: SchemaDesc, SchemaDescType, SchemaDescTypeType
using ...Meta: strip_lines


# StructAcset Struct Generation
###############################

abstract type AbstractStructAcset{Schema<:SchemaDescType,Idxed,Ts<:Tuple} end

const ASA = AbstractStructAcset

q(s::Symbol) = Expr(:quote,s)
q(s::GATExpr) = q(nameof(s))

""" Creates a quoted named tuple used for `StructAcset`s
"""
function pi_type(dom::Vector, F::Function)
  :(NamedTuple{($(q.(dom)...),),Tuple{$(F.(dom)...)}})
end

""" Creates a quoted element of a named tuple used for `StructAcset`s
"""
function pi_type_elt(dom::Vector, f::Function)
  if length(dom) > 0
    Expr(:tuple, Expr(:parameters, [Expr(:kw, nameof(d), f(d)) for d in dom]...))
  else # workaround for Julia 1.0
    :(NamedTuple())
  end
end

""" Create the struct declaration for a `StructAcset` from a Presentation
"""
function struct_acset(name::Symbol, parent, p::Presentation{Schema}, idxed=[])
  obs = p.generators[:Ob]
  homs = p.generators[:Hom]
  attr_types = p.generators[:AttrType]
  Ts = nameof.(attr_types)
  attrs = p.generators[:Attr]
  idxed = (;[x => x ∈ idxed for x in [nameof.(homs);nameof.(attrs)]]...)
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
    _ => (head, GlobalRef(StructAcsets, :ASA))
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

macro abstract_acset_type(head)
  type, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(StructAcsets, :ASA))
  end
  quote
    abstract type $type{schema,idxed,Ts} <: $parent{schema,idxed,Ts} end
  end
end


# StructAcset Operations
########################

""" This should really be in base, or at least somewhere other than this module...
"""
Base.Dict(nt::NamedTuple) = Dict(k => nt[k] for k in keys(nt))

# Accessors
###########

Acset.nparts(acs::ASA, ob::Symbol) = acs.obs[ob][]
Acset.has_part(acs::ASA, ob::Symbol) = _has_part(acs, Val{ob})

@generated function _has_part(acs::ASA{schema}, ::Type{Val{ob}}) where
  {obs, schema <: SchemaDescType{obs}, ob}
  ob ∈ obs
end

Acset.has_subpart(acs::ASA, f::Symbol) = _has_subpart(acs, Val{f})

@generated function _has_subpart(acs::ASA{schema}, ::Type{Val{f}}) where
  {f, obs, homs, attrtypes, attrs, schema <: SchemaDescType{obs,homs,attrtypes,attrs}}
  f ∈ homs || f ∈ attrs
end

@inline view_or_slice(x::AbstractVector, i) = view(x, i)
@inline view_or_slice(x::AbstractVector, i::Union{Integer,StaticArray}) = x[i]

Acset.subpart(acs::ASA, part, f::Symbol) = _subpart(acs, part, Val{f})

Acset.subpart(acs::ASA, f::Symbol) = subpart(acs,:,f)

function subpart_body(s::SchemaDesc, f::Symbol)
  if f ∈ s.homs
    :(acs.homs.$f[part])
  elseif f ∈ s.attrs
    :(acs.attrs.$f[part])
  else
    throw(ArgumentError("$(repr(f)) not in $(s.homs) or $(s.attrs)"))
  end
end

@generated function _subpart(acs::ASA{schema},
                             part, ::Type{Val{f}}) where {schema, f}
  subpart_body(SchemaDesc(schema), f)
end

@inline Acset.incident(acs::ASA, part, f::Symbol; copy::Bool=false) =
  _incident(acs, part, Val{f}; copy=copy)

broadcast_findall(xs, array::AbstractArray) =
  broadcast(x -> findall(y -> x == y, array), xs)

function incident_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, f::Symbol)
  if f ∈ s.homs
    if idxed[f]
      quote
        indices = view_or_slice(acs.hom_indices.$f, part)
        copy ? Base.copy.(indices) : indices
      end
    else
      :(broadcast_findall(part, acs.homs.$f))
    end
  elseif f ∈ s.attrs
    if idxed[f]
      quote
        indices = get_attr_index.(Ref(acs.attr_indices.$f), part)
        copy ? Base.copy.(indices) : indices
      end
    else
      :(broadcast_findall(part, acs.attrs.$f))
    end
  else
    throw(ArgumentError("$(repr(f)) not in $(s.homs)"))
  end
end
    
@generated function _incident(acs::ASA{schema,idxed},
                              part, ::Type{Val{f}}; copy::Bool=false) where {schema,idxed,f}
  incident_body(SchemaDesc(schema),Dict(idxed),f)
end

# Mutators
##########

Acset.add_parts!(acs::ASA, ob::Symbol, n::Int) = _add_parts!(acs, Val{ob}, n)

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

""" This generates the _add_parts! methods for a specific object of a `StructAcset`.
"""
@generated function _add_parts!(acs::ASA{schema,idxed},
                                ::Type{Val{ob}}, n::Int) where {ob, schema, idxed}
  add_parts_body(SchemaDesc(schema),Dict(idxed),ob)
end

Acset.set_subpart!(acs::ASA, part::Int, f::Symbol, subpart) =
  _set_subpart!(acs, part, Val{f}, subpart)


function set_subpart_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, f::Symbol)
  if f ∈ s.homs
    if idxed[f]
      quote
        @assert 0 <= subpart <= acs.obs.$(s.codoms[f])[]
        old = acs.homs.$f[part]
        acs.homs.$f[part] = subpart
        if old > 0
          @assert deletesorted!(acs.hom_indices.$f[old], part)
        end
        if subpart > 0
          insertsorted!(acs.hom_indices.$f[subpart], part)
        end
      end
    else
      quote
        @assert 0 <= subpart <= acs.obs.$(s.codoms[f])[]
        acs.homs.$f[part] = subpart
      end
    end
  elseif f ∈ s.attrs
    if idxed[f]
      quote
        if isassigned(acs.attrs.$f, part)
          old = acs.attrs.$f[part]
          unset_attr_index!(acs.attr_indices.$f, old, part)
        end
        acs.attrs.$f[part] = subpart
        set_attr_index!(acs.attr_indices.$f, subpart, part)
      end
    else
      :(acs.attrs.$f[part] = subpart)
    end
  else
    throw(ArgumentError("$(f) not in $(s.homs) or $(s.attrs)"))
  end
end

""" This generates the `_set_subparts!` method for a specific arrow (hom/attr) of a StructAcset
"""
@generated function _set_subpart!(acs::ASA{schema,idxed},
                                  part, ::Type{Val{f}}, subpart) where {schema,idxed,f}
  set_subpart_body(SchemaDesc(schema),Dict(idxed),f)
end

Acset.rem_part!(acs::ASA, type::Symbol, part::Int) = _rem_part!(acs, Val{type}, part)

function getassigned(acs::ASA, arrows, i)
  assigned_subparts = filter(f -> isassigned(subpart(acs,f),i), arrows)
  Dict(f => subpart(acs,i,f) for f in assigned_subparts)
end

function rem_part_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, ob::Symbol)
  in_homs = filter(hom -> s.codoms[hom] == ob, s.homs)
  out_homs = filter(f -> s.doms[f] == ob, s.homs)
  out_attrs = filter(f -> s.doms[f] == ob, s.attrs)
  indexed_out_homs = filter(hom -> s.doms[hom] == ob && idxed[hom], s.homs)
  indexed_attrs = filter(attr -> s.doms[attr] == ob && idxed[attr], s.attrs)
  quote
    last_part = acs.obs.$ob[]
    @assert 1 <= part <= last_part
    # Unassign superparts of the part to be removed and also reassign superparts
    # of the last part to this part.
    for hom in $(Tuple(in_homs))
      set_subpart!(acs, incident(acs, part, hom, copy=true), hom, 0)
      set_subpart!(acs, incident(acs, last_part, hom, copy=true), hom, part)
    end
    last_row = getassigned(acs, $([out_homs;out_attrs]), last_part)

    # Clear any morphism and data attribute indices for last part.
    for hom in $(Tuple(indexed_out_homs))
      set_subpart!(acs, last_part, hom, 0)
    end
    for attr in $(Tuple(indexed_attrs))
      if haskey(last_row, attr)
        unset_attr_index!(acs.attr_indices[attr], last_row[attr], last_part)
      end
    end

    # Finally, delete the last part and update subparts of the removed part.
    for f in $(Tuple(out_homs))
      resize!(acs.homs[f], last_part - 1)
    end
    for a in $(Tuple(out_attrs))
      resize!(acs.attrs[a], last_part - 1)
    end
    acs.obs.$ob[] -= 1
    if part < last_part
      set_subparts!(acs, part, (;last_row...))
    end
  end
end

@generated function _rem_part!(acs::ASA{schema,idxed}, ::Type{Val{ob}},
                               part::Int) where {ob,schema,idxed}
  rem_part_body(SchemaDesc(schema),Dict(idxed),ob)
end

# Printing
##########

function Base.show(io::IO, acs::ASA{schema,idxed,Ts}) where {schema,idxed,Ts}
  s = SchemaDesc(schema)
  print(io, "ACSet")
  println(io, "(")
  join(io, vcat(
    [ "  $ob = 1:$(nparts(acs,ob))" for ob in s.obs ],
    [ "  $attr_type = $(Ts.parameters[i])" for (i, attr_type) in enumerate(s.attrtypes) ],
    [ "  $f : $(s.doms[f]) → $(s.codoms[f]) = $(subpart(acs,f))"
      for f in s.homs ],
    [ "  $a : $(s.doms[a]) → $(s.codoms[a]) = $(subpart(acs,a))"
      for a in s.attrs ],
  ), ",\n")
  print(io, ")")
end

# TODO: implement Tables interface
# function Base.show(io::IO, ::MIME"text/plain", acs::ASA{schema}) where {schema}
#   s = SchemaDesc(schema)
#   print(io, "ACSet")
#   print(io, " with elements ")
#   join(io, ["$ob = 1:$(nparts(acs,ob))" for ob in ], ", ")
#   println(io)
#   pretty_tables(io, acs)
# end

# function Base.show(io::IO, ::MIME"text/html", acs::T) where {T<:AbstractACSet}
#   println(io, "<div class=\"c-set\">")
#   print(io, "<span class=\"c-set-summary\">")
#   print(io, T <: AbstractCSet ? "CSet" : "ACSet")
#   print(io, " with elements ")
#   join(io, ["$ob = 1:$(nparts(acs,ob))" for ob in keys(tables(acs))], ", ")
#   println(io, "</span>")
#   pretty_tables(io, acs, backend=:html, standalone=false)
#   println(io, "</div>")
# end

end
