module DPO
export rewrite, rewrite_match, pushout_complement, can_pushout_complement,
  id_condition, dangling_condition

using ...Theories
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
"""
function rewrite_match(L::ACSetTransformation{CD, AD},
                       R::ACSetTransformation{CD, AD},
                       m::ACSetTransformation{CD, AD}
                      )::AbstractACSet{CD, AD} where {CD, AD}
  dom(L) == dom(R) || error("Rewriting where L, R do not share domain")
  codom(L) == dom(m) || error("Rewriting where L does not compose with m")
  (k, _) = pushout_complement(L, m)
  l1, _ = pushout(R, k)
  return codom(l1)
end

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet,
where a match morphism is found automatically. If multiple
matches are found, a particular one can be selected using
`m_index`.
"""
function rewrite(L::ACSetTransformation{CD, AD},
                 R::ACSetTransformation{CD, AD},
                 G::AbstractACSet{CD, AD},
                 monic::Bool=false, m_index::Int=1
                )::Union{Nothing, AbstractACSet} where {CD, AD}
  ms = filter(m->can_pushout_complement(L, m),
              homomorphisms(codom(L), G, monic=monic))
  if 0 < m_index <= length(ms)
    rewrite_match(L, R, ms[m_index])
  else
    nothing
  end
end

end
