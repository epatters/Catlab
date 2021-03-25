export Schema, FreeSchema, AttrType, Attr,
  SchemaExpr, AttrTypeExpr, AttrExpr, parse_schema

using MLStyle: @match
using ...Meta: strip_lines

# Schema
########

""" The GAT that parameterizes Attributed C-sets
A schema is comprised of a category C, a discrete category D, and a profunctor
Attr : C^op x D → Set. In GAT form, this is given by extending the theory of
categories with two extra types, AttrType for objects of D, and Attr, for elements
of the sets given by the profunctor.
"""
@theory Schema{Ob,Hom,AttrType,Attr} <: Category{Ob,Hom} begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE

  """ Composition is given by the action of the profunctor on C.
  """
  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::Ob, a::Attr(A,X))
end

abstract type SchemaExpr{T} <: GATExpr{T} end
abstract type AttrTypeExpr{T} <: SchemaExpr{T} end
abstract type AttrExpr{T} <: SchemaExpr{T} end

@syntax FreeSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} Schema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
end

# Type-level representation of Schema
#####################################

""" CatDesc is a type-level description of a category
In order to have Attributed C-sets that are parameterized by schemas, we have to
use the type of this struct as the type parameter to get around Julia's
restrictions on what sort of thing can appear as a type parameter.
We split a Schema up into two types: CatDesc (describing the category) and
AttrDesc (describing the discrete category and the profunctor). This allows us
to have C-sets as Attributed C-sets with an empty AttrDesc.
"""
struct CatDesc{Ob,Hom,Dom,Codom}
  function CatDesc{Ob,Hom,Dom,Codom}() where {Ob,Hom,Dom,Codom}
    new{Ob,Hom,Dom,Codom}()
  end
  function CatDesc(pres::Presentation{Schema})
    obs, homs = generators(pres, :Ob), generators(pres,:Hom)
    ob_syms, hom_syms = nameof.(obs), nameof.(homs)
    ob_num = ob -> findfirst(ob_syms .== ob)::Int
    new{Tuple(ob_syms), Tuple(hom_syms),
        Tuple(@. ob_num(nameof(dom(homs)))), Tuple(@. ob_num(nameof(codom(homs))))}()
  end
end

CatDescType(pres::Presentation{Schema}) = typeof(CatDesc(pres))

ob(::Type{T}) where {Ob,T <: CatDesc{Ob}} = Ob
hom(::Type{T}) where {Ob,Hom, T <: CatDesc{Ob,Hom}} = Hom
dom(::Type{T}) where {Ob,Hom,Dom, T <: CatDesc{Ob,Hom,Dom}} = Dom
codom(::Type{T}) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}} = Codom

function ob_num(CD::Type{T}, ob::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  findfirst(Ob .== ob)::Int
end

function hom_num(CD::Type{T}, hom::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  findfirst(Hom .== hom)::Int
end

function dom_num(CD::Type{T}, hom::Int) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Dom[hom]
end

function dom_num(CD::Type{<:CatDesc}, hom::Symbol)
  dom_num(CD, hom_num(CD,hom))
end

function codom_num(CD::Type{T}, hom::Int) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Codom[hom]
end

function codom_num(CD::Type{<:CatDesc}, hom::Symbol)
  codom_num(CD, hom_num(CD,hom))
end

function dom(CD::Type{T}, hom::Union{Int,Symbol}) where
    {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Ob[dom_num(CD,hom)]
end

function codom(CD::Type{T}, hom::Union{Int,Symbol}) where
    {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Ob[codom_num(CD,hom)]
end

""" AttrDesc is a type-level representation of attributes added
to a category to form a schema
"""
struct AttrDesc{CD,AttrType,Attr,ADom,ACodom}
  function AttrDesc{CD,AttrType,Attr,ADom,ACodom}() where {CD,AttrType,Attr,ADom,ACodom}
    new{CD,AttrType,Attr,ADom,ACodom}()
  end
  function AttrDesc(pres::Presentation{Schema})
    CD = CatDescType(pres)
    attr_types, attrs = generators(pres, :AttrType), generators(pres,:Attr)
    attr_type_syms, attr_syms = nameof.(attr_types), nameof.(attrs)
    ob_num = ob -> findfirst(Theories.ob(CD) .== ob)::Int
    attr_type_num = ob -> findfirst(attr_type_syms .== ob)::Int
    new{CD,Tuple(attr_type_syms), Tuple(attr_syms),
        Tuple(@. ob_num(nameof(dom(attrs)))), Tuple(@. attr_type_num(nameof(codom(attrs))))}()
  end
  function AttrDesc(::CatDesc{Ob,Hom,Dom,Codom}) where {Ob,Hom,Dom,Codom}
    new{CatDesc{Ob,Hom,Dom,Codom},(),(),(),()}
  end
end

AttrDescType(pres::Presentation{Schema}) = typeof(AttrDesc(pres))

attr_type(::Type{T}) where {CD,AttrType, T <: AttrDesc{CD,AttrType}} = AttrType
attr(::Type{T}) where {CD,AttrType,Attr, T <: AttrDesc{CD,AttrType,Attr}} = Attr
adom(::Type{T}) where {CD,AttrType,Attr,ADom,
                       T <: AttrDesc{CD,AttrType,Attr,ADom}} = ADom
acodom(::Type{T}) where {CD,AttrType,Attr,ADom,ACodom,
                         T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}} = ACodom

function attr_type_num(AD::Type{T}, attr_type::Symbol) where
  {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  findfirst(AttrType .== attr_type)::Int
end

function attr_num(AD::Type{T}, attr::Symbol) where
  {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  findfirst(Attr .== attr)::Int
end

function dom_num(AD::Type{T}, attr::Int) where
  {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  ADom[attr]
end

function dom_num(AD::Type{<:AttrDesc}, attr::Symbol)
  dom_num(AD,attr_num(AD,attr))
end

function codom_num(AD::Type{T}, attr::Int) where
  {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  ACodom[attr]
end

function codom_num(AD::Type{<:AttrDesc}, attr::Symbol)
  codom_num(AD,attr_num(AD,attr))
end

function dom(AD::Type{T}, attr::Union{Int,Symbol}) where
    {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  ob(CD)[dom_num(AD,attr)]
end

function codom(AD::Type{T}, attr::Union{Int,Symbol}) where
    {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  AttrType[codom_num(AD,attr)]
end

function attrs_by_codom(AD::Type{T}) where
    {CD,AttrType,Attr,ADom,ACodom,T <: AttrDesc{CD,AttrType,Attr,ADom,ACodom}}
  abc = Dict{Symbol,Array{Symbol}}()
  for i in eachindex(Attr)
    a = Attr[i]
    d = AttrType[ACodom[i]]
    if d ∈ keys(abc)
      push!(abc[d],a)
    else
      abc[d] = [a]
    end
  end
  abc
end

SchemaType(pres::Presentation{Schema}) = (CatDescType(pres),AttrDescType(pres))


""" Parse a Presentation{Schema} from a specialized syntax for it

See also [`@schema`](@ref).
"""
function parse_schema(Ts::Vector, body::Expr, extend=Presentation(FreeSchema))
  p = copy(extend)
  lines = @match strip_lines(body) begin
    Expr(:block, lines...) => lines
    _ => error("unsupported body format")
  end
  add_generators!(p, Ts, :AttrType)
  arrow_decls = []
  # Initial pass to add objects
  for line in lines
    @match line begin
      name::Symbol => add_generator!(p,name,:Ob,[])
      Expr(:call, name::Symbol, args...) => begin
        add_generator!(p,name,:Ob)
        push!(arrow_decls, (name,args))
      end
      _ => Present.eval_stmt!(p,line)
    end
  end
  # Second pass to add homs/attrs
  for (name,args) in arrow_decls
    eval_object_args(p,name,args)
  end
  p
end


function eval_object_args(p::Presentation,name,args)
  for arg in args
    hom, codom = @match strip_lines(arg) begin
      Expr(:(::), hom, codom) => (hom, codom)
      _ => error("invalid hom expr")
    end
    if codom ∈ nameof.(p.generators[:AttrType])
      add_generator!(p, hom, :Attr, [name, codom])
    else
      add_generator!(p, hom, :Hom, [name, codom])
    end
  end
end


function intify(tuple,s)
  findfirst(tuple .== s)
end

function tuplize(xs,f)
  (;[nameof(x) => nameof(f(x)) for x in xs]...)
end

struct SchemaDescType{obs,homs,attrtypes,attrs,hominfo,attrinfo}
end

function SchemaDescTypeType(p::Presentation)
  obs,homs,attrtypes,attrs = map(t -> p.generators[t],[:Ob,:Hom,:AttrType,:Attr])
  ob_syms,hom_syms,attrtype_syms,attr_syms = map(xs -> Tuple(nameof.(xs)),
                                                 [obs,homs,attrtypes,attrs])
  homdoms = map(t -> intify(ob_syms,t),tuplize(homs,dom))
  homcodoms = map(t -> intify(ob_syms,t),tuplize(homs,codom))
  attrdoms = map(t -> intify(ob_syms,t),tuplize(attrs,dom))
  attrcodoms = map(t -> intify(attrtype_syms,t),tuplize(attrs,codom))
  SchemaDescType{
    ob_syms,
    hom_syms,
    attrtype_syms,
    attr_syms,
    (;homdoms...,attrdoms...),
    (;homcodoms...,attrcodoms...)
  }
end

struct SchemaDesc
  obs::Vector{Symbol}
  homs::Vector{Symbol}
  attrtypes::Vector{Symbol}
  attrs::Vector{Symbol}
  doms::Dict{Symbol,Symbol}
  codoms::Dict{Symbol,Symbol}
  function SchemaDesc(::Type{SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
      {obs,homs,attrtypes,attrs,doms,codoms}
    homdoms = [f => obs[doms[f]] for f in homs]
    homcodoms = [f => obs[codoms[f]] for f in homs]
    attrdoms = [a => obs[doms[a]] for a in attrs]
    attrcodoms = [a => attrtypes[codoms[a]] for a in attrs]
    new(
      Symbol[obs...],
      Symbol[homs...],
      Symbol[attrtypes...],
      Symbol[attrs...],
      Dict{Symbol,Symbol}(homdoms...,attrdoms...),
      Dict{Symbol,Symbol}(homcodoms...,attrcodoms...)
    )
  end
end
