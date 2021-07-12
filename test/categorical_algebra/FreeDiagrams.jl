module TestFreeDiagrams
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets: FinSet, FinFunction

A, B, C, D = Ob(FreeCategory, :A, :B, :C, :D)

# Diagrams of flexible shape
############################

# General free diagrams
#----------------------

f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, B)
diagram = FreeDiagram([A,B,C], [(f,1,3),(g,2,3),(h,1,2)])
@test ob(diagram) == [A,B,C]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,1], [3,3,2])
@test_throws Exception FreeDiagram([A,B,C], [(f,1,2),(g,2,3),(h,1,2)])

# Bipartite free diagrams
#------------------------

bd = BipartiteFreeDiagram([A,B], [C], [(f,1,1),(g,2,1)])
@test (ob₁(bd), ob₂(bd)) == ([A,B], [C])
@test hom(bd) == [f,g]
@test (src(bd), tgt(bd)) == ([1,2], [1,1])
@test FreeDiagram(bd) == FreeDiagram([A,B,C], [(f,1,3),(g,2,3)])

# Diagrams of fixed shape
#########################

# Empty diagrams.
@test isempty(EmptyDiagram{FreeCategory.Ob}())

# Object pairs.
pair = ObjectPair(A,B)
@test length(pair) == 2
@test (first(pair), last(pair)) == (A, B)

# Discrete diagrams.
discrete = DiscreteDiagram([A,B,C])
@test length(discrete) == 3
@test ob(discrete) == [A,B,C]

diagram = FreeDiagram(discrete)
@test ob(diagram) == [A,B,C]
@test isempty(hom(diagram))

# Spans.
f, g = Hom(:f, C, A), Hom(:g, C, B)
span = Span(f,g)
@test apex(span) == C
@test legs(span) == [f,g]
@test feet(span) == [A,B]
@test (left(span), right(span)) == (f, g)

f = Hom(:f, A, A)
@test legs(Span(id(A), f)) == [id(A),f]

f = Hom(:f, A, B)
@test_throws ErrorException Span(f,g)

# Multispans.
f, g, h = Hom(:f, C, A), Hom(:g, C, B), Hom(:h, C, A)
span = Multispan([f,g,h])
@test apex(span) == C
@test legs(span) == [f,g,h]
@test feet(span) == [A,B,A]

diagram = BipartiteFreeDiagram(span)
@test (ob₁(diagram), ob₂(diagram)) == ([C], [A,B,A])
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [1,2,3])

diagram = FreeDiagram(span)
@test ob(diagram) == [C,A,B,A]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [2,3,4])

span = Multispan([ id(FinSet(2)) for i in 1:3 ])
span = bundle_legs(span, [1, (2,3)])
@test apex(span) == FinSet(2)
@test codom.(legs(span)) == [FinSet(2), FinSet(4)]

# Cospans.
f, g = Hom(:f, A, C), Hom(:g, B, C)
cospan = Cospan(f,g)
@test apex(cospan) == C
@test legs(cospan) == [f,g]
@test feet(cospan) == [A,B]
@test (left(cospan), right(cospan)) == (f, g)

f = Hom(:f, A, A)
@test legs(Cospan(f, id(A))) == [f,id(A)]

f = Hom(:f, A ,B)
@test_throws ErrorException Cospan(f,g)

# Multicospans.
f, g, h = Hom(:f, A, C), Hom(:g, B, C), Hom(:h, A, C)
cospan = Multicospan([f,g,h])
@test apex(cospan) == C
@test legs(cospan) == [f,g,h]
@test feet(cospan) == [A,B,A]

diagram = BipartiteFreeDiagram(cospan)
@test (ob₁(diagram), ob₂(diagram)) == ([A,B,A], [C])
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,3], [1,1,1])

diagram = FreeDiagram(cospan)
@test ob(diagram) == [A,B,A,C]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,2,3], [4,4,4])

cospan = Multicospan([FinFunction([i],3) for i in 1:3])
cospan = bundle_legs(cospan, [(1,3), 2])
@test apex(cospan) == FinSet(3)
@test legs(cospan) == [FinFunction([1,3], 3), FinFunction([2], 3)]

# Parallel pairs.
f, g = Hom(:f, A, B), Hom(:g, A, B)
pair = ParallelPair(f,g)
@test (dom(pair), codom(pair)) == (A, B)
@test (first(pair), last(pair)) == (f, g)

# Parallel morphisms.
f, g, h = Hom(:f, A, B), Hom(:g, A, B), Hom(:h, A, B)
para = ParallelMorphisms([f,g,h])
@test (dom(para), codom(para)) == (A, B)
@test hom(para) == [f,g,h]

diagram = BipartiteFreeDiagram(para)
@test (ob₁(diagram), ob₂(diagram)) == ([A], [B])
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [1,1,1])

diagram = FreeDiagram(para)
@test ob(diagram) == [A,B]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == ([1,1,1], [2,2,2])

# Composable pairs.
f, g = Hom(:f, A, B), Hom(:g, B, C)
pair = ComposablePair(f,g)
@test (dom(pair), codom(pair)) == (A, C)
@test (first(pair), last(pair)) == (f, g)
@test_throws ErrorException ComposablePair(f,f)

# Composable morphisms.
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, C, D)
comp = ComposableMorphisms([f,g,h])
@test (dom(comp), codom(comp)) == (A, D)
@test hom(comp) == [f,g,h]

diagram = FreeDiagram(comp)
@test ob(diagram) == [A,B,C,D]
@test hom(diagram) == [f,g,h]
@test (src(diagram), tgt(diagram)) == (1:3, 2:4)

end
