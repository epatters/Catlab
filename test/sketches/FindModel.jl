include(joinpath(@__DIR__, "../../src/sketches/FindModel.jl"))
include(joinpath(@__DIR__, "FLS.jl"))  # where the sketches are defined

using Test
using Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: ReflexiveGraph, TheoryReflexiveGraph


met = catpres_to_linear(TheoryReflexiveGraph);
r1, r2 = ReflexiveGraph(2), ReflexiveGraph(2)
set_subpart!(r2,:src,[1,1])
@test length(check_diagram(met, r1, :V)) == 2
@test length(check_diagram(met, r2, :V)) == 1

@test check_diagrams(met, r1)
@test_throws AssertionError("Equations for V not satisfied by indices [2]"
                           ) check_diagrams(met, r2)

#############################
# LEFT INVERSE / INVOLUTION #
#############################


srch_leftinv = c->[catelems_to_cset(leftinv, r) for r in search(leftinv, c)]

for (x, y) in [[2,2]=>2, # inv can be swap or id, f is forced to be an iso
               [2,1]=>0, # injective function to smaller card
               [1,2]=>2, # inv can be swap or id, f's choices are symmetric.
               [2,3]=>4] # see note below
    @test length(search(leftinv, x)) == y
end

# There are 4 nonisomorphic options for A=2,B=3:
# inv can be id OR swap 2 of the three elements in B.
# There is only one automorph where inv is id, and
# if B swaps, then f(1) and f(2) can map to the swapped
# elements, in which case there is just one automorph.
# There are two automorphs in the case where only one out of
# f(1),f(2) is in the swapped pair in B. These are
# distinguished by whether or not the element of g that is
# not mapped to maps to the A whose image in in the swap or not.

######################################################

#############
# EQUALIZER #
#############

srch_equalizer = c->[catelems_to_cset(equalizer, r)
                     for r in search(equalizer, c)]

# The pullback is empty because f=[1,1] and g=[2,2]
@test length(search(equalizer,[2,2,0])) == 1

# There are 4 models.
# f=[1,2], g=[1,2] means the pullback is {(1,1),(2,2)}
# f=[1,2], g=[1,1] means the pullback is {(1,1),(1,2)}
# f=[1,1], g=[1,2] means the pullback is {(1,1),(2,1)}
# f=[2,1], g=[1,2] means the pullback is {(1,2),(2,1)}
@test length(search(equalizer,[2,2,2]))==4

# If f,g map to same element, then pullback is A×A
@test length(search(equalizer,[2,2,4]))==1

#################################
# SET PERMUTATIONS / PARTITIONS #
#################################

srch_perm = c -> [catelems_to_cset(perm, r) for r in search(perm, [c])]

# Isomorphism classes of permutations AKA PARTITIONS
# [1]=id, [2]= adds swap, [3] adds a 3-cycle,
# [4] adds a 4-cycle + having two swaps
iso_perms = [1,2,3,5]
for (i, n_perms) in enumerate(iso_perms)
    @assert length(search(perm, [i])) == n_perms
end

####################
# REFLEXIVE GRAPHS #
####################

srch_reflg = cs -> [catelems_to_cset(reflg, r) for r in search(reflg, cs)]

# Single node with self loop
for (consts, expected) in [
    [1,1]=>1,
    [0,1]=>0,   # arrow needs a vertex
    [1,0]=>0,   # vertex needs an id arrow
    [2,2]=>1,   # both arrows must be id
    [2,3]=>2,   # the non-id arrow can bridge or not
    [2,4]=>(2+  # 2 loops (either same vertex or not),
            2+  # 1 loop (either ↺← or ↺→)
            2)] # 0 loops (either ⇆ or ⇉)
    @test length(search(reflg,consts)) == expected
end

###########################
# CONSTANT (arrow from 1) #
###########################

srch_const2 = cs -> [catelems_to_cset(const2, r) for r in search(const2, cs)]

# Only one option if codomain is singleton
@test length(search(const2, [1,1])) == 1

# with two constants, they can either be the same or different
for i in 2:5
    @test length(search(const2, [1,i])) == 2
end

# Nothing for the terminal object to map to
@test length(search(const2, [1,0])) == 0

# Terminal object must be singleton, no more, no less
for i in 0:5
    @test length(search(const2, [0,i])) == 0
    @test length(search(const2, [2,i])) == 0
end

####################################
# Infinite sequence of a's and b's #
####################################

srch_inflist = cs -> [catelems_to_cset(inflist, r) for r in search(inflist, cs)]
srch_inflist([1,0,0])

for combo in cartprod(0:3,0:3,0:3)
    n1, nd, nl = combo
    # terminal object must have 1
    # 1 must have something to send a,b to
    # no results if either of these don't happen
    if n1 != 1 || nd == 0
        expected = 0
    # |L|=|L|x|D| satisfied trivially when |L|=0
    # just have the number of ways for a,b to map to D
    elseif nl == 0 #
        expected = nd == 1 ? 1 : 2 # either to same elem or diff, if |D| > 1
    elseif nd == 1
        expected = iso_perms[nl]
    else
        expected = 0 # nd > 1, and nl >0, so |L|=|L|x|D| impossible to solve
    end
    length(search(inflist,collect(combo))) == expected
end


srch_trips = cs -> [catelems_to_cset(trips, r) for r in search(trips, cs)]


##############
# SEMIGROUPS #
##############

srch_sg = cs -> [catelems_to_cset(semig, r) for r in search(semig, cs)]
# too big to solve [2,4,8].

##############
# Categories #
##############
"""
this was defined using an old implementation that used graph homomorphisms,
should be redone using LabeledGraphs
#------------------------------------------------
# 10.1.5: Categories

# note composition is defined "backwards", i.e. g∘f
CatG = Graph(4) # ob arr composable_arrows composable_triples
o,a,a²,a³ = 1:4 # shorthand
add_edges!(CatG, [o,a,a,a²,a²,a²,a³,a³,a³,a³, a³, a³, a³, a,    a,   a],
                 [a,o,o,a, a, a, a, a, a, a², a², a², a², a²,   a²,  a])
                # u s t π₁ π₂ c  p₁ p₂ p₃ p₁₂ p₂₃ p₁c cp₃ utid idus, ida
u,s,t,π₁,π₂,c,p₁,p₂,p₃,p₁₂,p₂₃,p₁c,cp₃,utid,idus,ida,v = 1:17
# There's a clear typo in the second diagram in CTCS
CD = T[
    T(OutwardTri,     CatG; V=[a³,a²,a,a],    E=[p₁₂,p₁,p₂,π₁,π₂]),
    T(OutwardTri,     CatG; V=[a³,a²,a,a],    E=[p₂₃,p₂,p₃,π₁,π₂]),
    T(SquareTriangle, CatG; V=[a³,a²,a,a²,a], E=[cp₃,p₃,p₁₂,π₂,π₁,c]),
    T(SquareTriangle, CatG; V=[a³,a²,a,a²,a], E=[p₁c,p₁,p₂₃,π₁,π₂,c]),
    T(SquareTriangle, CatG; V=[a,a²,a,o,a],   E=[utid,ida,t,π₂,π₁,u]),
    T(SquareTriangle, CatG; V=[a,a²,a,o,a],   E=[idus,ida,s,π₁,π₂,u]),
    T(InvertedTri,    CatG; V=[a,a²,a,a],     E=[idus,ida,utid,ida,c]), # unit
    T(Square,         CatG; V=[a³,a²,a²,a],   E=[p₁c,cp₃,c,c]) # associativity
]

CLim1 = T(Square, CatG; V=[a²,a,a,o], E=[π₁,π₂,s,t])
CLim2G = Graph(6)
add_edges!(CLim2G, [1,1,1,2,3,3,4],[2,3,4,5,5,6,6])
CLim2 = T(CLim2G, CatG; V=[a³,a,a,a,o,o], E=[p₁,p₂,p₃,s,t,s,t])

CatSketch= FLSketch(CatG, CD, Pair{Int,T}[1 => CLim1, 1 => CLim2])
"""