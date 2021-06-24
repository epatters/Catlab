module GATmatch

export @gatmatch, @gatmatch_pure, ExprMatch, TypeMatch, matchtype!, matchexpr!, subexpr, subexprpair, sub_s_expr
using MLStyle: @match

using ..GAT: @theory
import ..Meta: Expr0
import ..Syntax: @syntax, GATExpr, head, gat_typeof, to_json_sexpr, parse_json_sexpr


GATType=Pair{Symbol, Vector{GATExpr}}
ExprMatch = Dict{Symbol, Any}
TypeMatch = Dict{Symbol, GATType}


"""
Insert key into dictionary, return nothing if contradiction found

Rather than check equality, might we want to find the most general unifier?
"""
function (safeInsert!(
    key::Symbol,
    val::T,
    dic::Dict{Symbol, T}
    )::Nothing) where T

  if !haskey(dic, key)
      dic[key] = val
  elseif dic[key] != val
      dic[:!] = nothing
  end
  return nothing
end

"""
Compare GATType to syntactic Expr and recursively match subterms
"""
function matchtype!(
    gattype::GATType,
    pattype::Expr0,
    patctx::Dict{Symbol, Expr0},
    exprmatch::ExprMatch,
    typematch::TypeMatch
    )::Nothing

    # Base case
    if pattype isa Symbol
        safeInsert!(pattype, gattype, typematch)
    # Recursive case
    elseif gattype.first == pattype.args[1]
        for (type_arg, patarg) in zip(gattype.second, pattype.args[2:end])
            matchexpr!(type_arg, patarg, patctx, exprmatch, typematch)
            if haskey(exprmatch,:!) || haskey(typematch,:!)
                return nothing
            end
        end
    # mismatch case
    else
        exprmatch[:!] = nothing
    end
    return nothing
end

"""
Compare GATExpr to syntactic Expr and recursively match subterms
"""
function matchexpr!(
  value::GATExpr,
  patarg::Expr0,
  patctx::Dict{Symbol, Expr0},
  exprmatch::ExprMatch,
  typematch::TypeMatch
  )::Nothing

  # Base case
  if patarg isa Symbol
    safeInsert!(patarg, value, exprmatch)
    if !(exprmatch === nothing) && haskey(patctx, patarg)
      matchtype!(gat_typeof(value) => value.type_args,
                 patctx[patarg], patctx,
                exprmatch, typematch)
    end
  # Recursive case
  elseif  all([patarg.head==:call,
               head(value) == patarg.args[1],
               length(patarg.args) == length(value.args) + 1])
    for (parg, varg) in zip(patarg.args[2:end], value.args)
        matchexpr!(varg, parg, patctx, exprmatch, typematch)
        if exprmatch === nothing || typematch === nothing
            return nothing
        end
    end
    # mismatch case
  else
        exprmatch[:!] = nothing
  end
  return nothing
end

function subexpr(expr::Expr0, exprmatch::ExprMatch)::Expr0
    for pair in collect(exprmatch)
        if expr isa Symbol
            return Meta.quot(exprmatch[expr])
        else
        expr = subexprpair(expr, pair)
        end
    end
    return expr
end

walk(x, inner, outer) = outer(x)
walk(x::Expr, inner, outer) = outer(Expr(x.head, map(inner, x.args)...))
postwalk(f, x) = walk(x, x -> postwalk(f, x), f)

function subexprpair(e::Expr0, pair)
    postwalk(e) do s
        s == pair.first && return pair.second
        s
    end
end

"""
Create a SExpr while substituting all symbols with match results
"""
function sub_s_expr(expr::Expr0, exprmatch::ExprMatch)::Vector{Any}
    # println("entering subexpr \n\t$expr ::$(typeof(expr)) \n\twith matches $matches")
    if expr isa Symbol
      return to_json_sexpr(exprmatch[expr])
    elseif expr.head == :call
      return vcat([expr.args[1]], [subexpr(x, exprmatch) for x in expr.args[2:end]])
    else
      throw(ErrorException("$expr --- $(typeof(expr))"))
    end
end

"""
Parse the body of a GATMatch
"""
function match_cases(tbl::Expr)::Vector{Tuple{Expr0, Dict{Symbol, Expr0}, Expr0}}
    cases = Tuple{Expr0, Dict{Symbol, Expr0}, Expr0}[]
    for x in tbl.args[2:2:end]
    push!(cases, @match x begin
        Expr(:call, [:(=>), Expr(:call, [:⊣, pat, ctx]...), res]...) => (
            pat, Dict{Symbol, Expr0}(ctx.head == :(::)
                                    ? [(ctx.args[1], ctx.args[2])]    # just 1 ctx item
                                    : map(a->a.args, ctx.args)), res) # many ctx items
        Expr(:call, [:(=>),pat, res]...) => (
            pat, Dict{Symbol, Expr0}(), res)  # no ctx given
        end )
    end
    return cases
end

"""
Match a GATExpr to a series of cases

To view an example of generated code:
Base.remove_linenums!(@macroexpand @gatmatch homexpr begin
    compose(F,id(β)) ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => F
    compose(id(α),F) ⊣ (α::Ob,β::Ob,F::Hom(α,β)) => F
    F => F
  end)
"""
macro gatmatch(val::Expr0, tbl::Expr)
    cases = match_cases(tbl)
    block = :(throw(ErrorException("No match found for $($val)")))
    for (patarg, patctx, res) in reverse(cases)
        pa = Meta.quot(patarg)
        block = quote
            em, tm = ExprMatch(), TypeMatch()
            matchexpr!($val, $(Meta.quot(patarg)), $(Meta.quot(patctx)), em, tm)
            if !(haskey(em, :!) || haskey(tm, :!))
                result = subexpr($(Meta.quot(res)), em)
                return eval(result)
            else
                $block
            end
        end
    end
  return esc(block)
end

macro gatmatch_pure(val::Expr0, syntax, tbl::Expr)
    cases = match_cases(tbl)

    # Function that will be generated on the fly by substituting val and tbl
    quot = quote
      syntax = $(syntax).syntax
      # Alternative: just pass in theory as argument
      #   theory_names = split(string(typeof($val).name), ".")
      #   theory_name = theory_names[length(theory_names)-1]
      #   syntax = getfield(@__MODULE__, Symbol(theory_name))

      for (patarg, patctx, res) in $cases
        # "otherwise" case
          # try to match
          em, tm = ExprMatch(), TypeMatch()
          matchexpr!($val, patarg, patctx, em, tm)
          if !(haskey(em, :!) || haskey(tm, :!))
            final_answer = sub_s_expr(res, em)
            return parse_json_sexpr(syntax, final_answer)
          end
      end
        throw(ErrorException("No match found for $($val)"))
    end
    return esc(quot)
end

# macro functor(val::Expr0, tbl::Expr)
#     return val
# end

end

