include(joinpath(@__DIR__, "../../src/sketches/FindModel.jl"))
using Test

"""Define example FLS"""

#########################
# COMMUTATIVE TRIANGLE  #
#########################

f = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 5
    vlabel = [:A,:B,:C]
    elabel = [:f,:h,:g, :ida, :inv]
    src    = [1,  1, 2,  1,    3]
    tgt    = [2,  3, 3,  1,    3]
end)

# f;g = h
add_diagram!(f, @acset LabeledGraph begin
    V = 3
    E = 3
    vlabel = [:A,:B,:C]
    elabel = [:f,:g,:h]
    src    = [1, 2, 1]
    tgt    = [2, 3, 3]
end)

# "ida" is an identity arrow
add_diagram!(f, @acset LabeledGraph begin
    V = 1
    E = 1
    vlabel = [:A]
    elabel = [:ida]
    src = [1]
    tgt = [1]
end);

# "inv" is an involution on C
add_diagram!(f, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:C, :C]
    elabel = [:inv, :inv]
    src = [1, 2]
    tgt = [2, 1]
end)

#############################
# LEFT INVERSE / INVOLUTION #
#############################

leftinv = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:A,:B]
    elabel = [:f,:g, :ida, :inv]
    src    = [1,  2,  1,   2]
    tgt    = [2,  1,  1,   2]
end);

add_diagram!(leftinv, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:A, :B]
    elabel = [:f, :g]
    src = [1, 2]
    tgt = [2, 1]
end);

add_diagram!(leftinv, @acset LabeledGraph begin
    V = 1
    E = 1
    vlabel = [:A]
    elabel = [:ida]
    src = [1]
    tgt = [1]
end)

add_diagram!(leftinv, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:B, :B]
    elabel = [:inv, :inv]
    src = [1, 2]
    tgt = [2, 1]
end)

#############
# EQUALIZER #
#############

fxb = Symbol("f×ᵦg")

equalizer = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 4
    vlabel = [:A,:B,fxb]
    elabel = [:f,:g, :π1, :π2]
    src = [1,1,3,3]
    tgt = [2,2,1,1]
end)

add_cone!(equalizer, @acset LabeledGraph begin
    V = 4
    E = 4
    vlabel = [:A,:B,:A,fxb]
    elabel = [:f,:g, :π1, :π2]
    src = [1,3,4,4]
    tgt = [2,2,1,3]
end)

#################################
# SET PERMUTATIONS / PARTITIONS #
#################################

perm = FLSinit(@acset LabeledGraph begin
    V = 1
    E = 2
    vlabel = [:X]
    elabel = [:f, :f⁻¹]
    src = [1,1]
    tgt = [1,1]
end );

add_diagram!(perm, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:X, :X]
    elabel = [:f, :f⁻¹]
    src = [1, 2]
    tgt = [2, 1]
end)

####################
# REFLEXIVE GRAPHS #
####################

reflg = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:V, :E]
    elabel = [:id, :refl, :src, :tgt]
    src = [1,1,2,2]
    tgt = [1,2,1,1]
end );

add_diagram!(reflg, @acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:V, :E]
    elabel = [:id, :refl, :src, :tgt]
    src = [1,1,2,2]
    tgt = [1,2,1,1]
end)

###########################
# CONSTANT (arrow from 1) #
###########################
s1 = Symbol("1")
const2 = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [s1, :A]
    elabel = [:f, :g]
    src = [1,1]
    tgt = [2,2]
end);

add_cone!(const2, @acset LabeledGraph begin
    V = 1
    vlabel=[s1]
end)

####################################
# Infinite sequence of a's and b's #
####################################

inflist = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 4
    vlabel = [s1, :d, :l]
    elabel = [:a,:b,:head,:tail]
    src = [1,1,3,3]
    tgt = [2,2,2,3]
end )

add_cone!(inflist, @acset LabeledGraph begin
    V = 1
    vlabel = [s1]
end)

add_cone!(inflist, @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:d, :l, :l]
    elabel = [:head, :tail]
    src = [3,3]
    tgt = [1,2]
end)

#####################
# Cartesian Product #
#####################

pairs = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:s, :s2]
    elabel = [:p1, :p2]
    src = [2,2]
    tgt = [1,1]
end ); # s s²

add_cone!(pairs, @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:s, :s, :s2]
    elabel = [:p1, :p2]
    src = [3,3]
    tgt = [1,2]
end )

srch_pairs = cs -> [catelems_to_cset(pairs, r) for r in search(pairs, cs)]


trips = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 3
    vlabel = [:s, :s3]
    elabel = [:p1, :p2, :p3]
    src = [2,2,2]
    tgt = [1,1,1]
end ); # s s²

add_cone!(trips, @acset LabeledGraph begin
    V = 4
    E = 3
    vlabel = [:s, :s, :s, :s3]
    elabel = [:p1, :p2, :p3]
    src = [4,4,4]
    tgt = [1,2,3]
end )

##############
# SEMIGROUPS #
##############

p1p2, p2p3, idk, kid = Symbol("π₁×π₂"), Symbol("π₂×π₃"), Symbol("id×k"), Symbol("k×id")
semig = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 10
    vlabel = [:s, :s2, :s3]
    elabel = [:k, :π₁, :π₂, :Π₁, :Π₂, :Π₃, p1p2, p2p3, idk, kid]
    src    = [2,  2,   2,   3,    3,   3,   3,   3,    3,   3]
    tgt    = [1,  1,   1,   1,    1,   1,   2,   2,    2,   2]
end );

# Associativity
add_diagram!(semig, @acset LabeledGraph begin
    V = 4
    E = 4
    vlabel = [:s3, :s2, :s2, :s]
    elabel = [kid, idk, :k, :k]
    src = [1,1,2,3]
    tgt = [2,3,4,4]
end)

# Define p1p2
add_diagram!(semig, @acset LabeledGraph begin
    V = 4
    E = 5
    vlabel = [:s3, :s, :s, :s2]
    elabel = [:Π₁, :Π₂, p1p2, :π₁, :π₂]
    src = [1,1,1,4,4]
    tgt = [2,3,4,2,3]
end)

# Define p2p3
add_diagram!(semig, @acset LabeledGraph begin
    V = 4
    E = 5
    vlabel = [:s3, :s, :s, :s2]
    elabel = [:Π₂, :Π₃, p2p3, :π₁, :π₂]
    src    = [1,    1,   1,   4,   4]
    tgt    = [2,    3,   4,   2,   3]
end)

# Define kid
add_diagram!(semig, @acset LabeledGraph begin
    V = 5
    E = 6
    vlabel = [:s3, :s2,  :s2, :s, :s]

    elabel = [p1p2, kid, :Π₃, :π₂, :k, :π₁]
    src    = [1,    1,    1,   3,   2,  3]
    tgt    = [2,    3,    4,   4,   5,  5]
end)


# Define idk
add_diagram!(semig, @acset LabeledGraph begin
    V = 5
    E = 6
    vlabel = [:s3, :s2,  :s2, :s, :s]

    elabel = [p2p3, idk, :Π₁, :π₁, :k, :π₂]
    src    = [1,    1,    1,   3,   2,  3]
    tgt    = [2,    3,    4,   4,   5,  5]
end)

# s2 is pair
add_cone!(semig, @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:s, :s, :s2]
    elabel = [:π₁, :π₂]
    src = [3,3]
    tgt = [1,2]
end )

# s3 is triple
add_cone!(semig, @acset LabeledGraph begin
    V = 4
    E = 3
    vlabel = [:s, :s, :s, :s3]
    elabel = [:Π₁, :Π₂, :Π₃]
    src = [4,4,4]
    tgt = [1,2,3]
end )