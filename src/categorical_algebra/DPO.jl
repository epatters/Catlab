module DPO
export rewrite, rewrite_match, valid_dpo, dangling_condition, id_condition,
  pushout_complement

using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ...Theories
using ...Theories: attr

import ..Limits: pushout_complement
using ..CSets: unpack_diagram

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. It will fail if any of the pointwise identification conditions or
the dangling condition do not hold.
"""
function pushout_complement(pair::ComposablePair{ACS}) where
    {CD, ACS <: AbstractACSet{CD}}
  l, m = pair
  I, G = dom(l), codom(m)
  valid_dpo(l, m) || error("Morphisms l and m do not satisfy gluing conditions")

  # Compute pushout complements pointwise in FinSet.
  components = map(pushout_complement, unpack_diagram(pair))
  k_components, g_components = map(first, components), map(last, components)

  g = subobject(G, g_components)
  k = ACSetTransformation(k_components, I, dom(g))
  return ComposablePair(k, g)
end

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
  ms = filter(m->valid_dpo(L, m), homomorphisms(codom(L), G, monic=monic))
  if 0 < m_index <= length(ms)
    return rewrite_match(L, R, ms[m_index])
  else
    return nothing
  end
end


"""
Condition for existence of a pushout complement
"""
function valid_dpo(L::ACSetTransformation, m::ACSetTransformation)::Bool
  return all(isempty, [collect(id_condition(L, m))...,
                       dangling_condition(L, m)])
end

"""
Check the identification condition: Does not map both a deleted item and a
preserved item in L to the same item in G, or two distinct deleted items to the
same. (Trivially satisfied if mono)

Returns a tuple of lists of violations
  1.) For a given component, a pair of IDs in L that are deleted yet mapped to
      the same index (the last integer of the tuple) in G
  2.) For a given component, a nondeleted index that maps to a deleted index
      in G
"""
function id_condition(L::ACSetTransformation{CD, AD},
                      m::ACSetTransformation{CD, AD}) where {CD, AD}
  res1, res2 = Tuple{Symbol, Int, Int, Int}[], Tuple{Symbol, Int, Int}[]
  for comp in keys(components(L))
    m_comp = x->m[comp](x)
    image = Set(collect(L[comp]))
    image_complement = filter(x->!(x in image), parts(codom(L),comp))
    image_vals = map(m_comp, collect(image))
    orphan_vals = map(m_comp, image_complement)
    orphan_set = Set(orphan_vals)

    for (i, iv) in enumerate(image_complement)
      for j in i+1:length(image_complement)
        if m_comp(iv) == m_comp(image_complement[j])
          push!(res1, (comp, i, j, m_comp(i)))
        end
      end
    end
    for i in image
      if m_comp(i) in orphan_set
        push!(res2, (comp, i, m_comp(i)))
      end
    end
  end

  return (res1, res2)
end

"""
Check the dangling condition: m doesn't map a deleted element d to a element
m(d) ∈ G if m(d) is connected to something outside the image of m.

For example, in the CSet of graphs:
  e1
1 --> 2

if e1 is not matched but either 1 and 2 are deleted, then e1 is dangling
"""
function dangling_condition(L::ACSetTransformation{CD, AD},
                            m::ACSetTransformation{CD, AD}) where {CD, AD}
  orphans, res = Dict(), []
  for comp in keys(components(L))
    image = Set(collect(L[comp]))
    orphans[comp] = Set(
      map(x->m[comp](x),
        filter(x->!(x in image),
          parts(codom(L), comp))))
  end
  # check that for all morphisms in C, we do not map to an orphan
  for (morph, src_ind, tgt_ind) in zip(hom(CD), dom(CD), codom(CD))
    src_obj = ob(CD)[src_ind] # e.g. :E, given morph=:src in graphs
    tgt_obj = ob(CD)[tgt_ind] # e.g. :V, given morph=:src in graphs
    n_src = parts(codom(m), src_obj)
    unmatched_vals = setdiff(n_src, collect(m[src_obj]))
    unmatched_tgt = map(x -> m.codom[morph][x], collect(unmatched_vals))
    for unmatched_val in setdiff(n_src, collect(m[src_obj]))  # G/m(L) src
      unmatched_tgt = m.codom[morph][unmatched_val]
      if unmatched_tgt in orphans[tgt_obj]
        push!(res, (morph, unmatched_val, unmatched_tgt))
      end
    end
  end
  return res
end

end
