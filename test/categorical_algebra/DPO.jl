module TestDPO
using Test
using Catlab.Graphs
using Catlab.Present
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra.FinSets
using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Theories: AttrDesc

# Wiring diagrams
#################

A, B, C, D = [:A], [:B], [:C], [:D];
f,g,h,i = Box(:f, A, B), Box(:g, B, C),Box(:h, C, D), Box(:i, [:D,:B], [:D,:B]);

GWD = WiringDiagram([:A,:A],[:D,:B])
fv, gv, hv, fv2 = add_box!(GWD, f), add_box!(GWD, g), add_box!(GWD, h), add_box!(GWD, f);
add_wires!(GWD, Pair[
  (input_id(GWD),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(GWD),1),
  (input_id(GWD),2) => (fv2,1),
  (fv2,1) => (output_id(GWD),2)]);

RWD = WiringDiagram([], []);
fv, iv, gv = add_box!(RWD, Box(:f,[],B)), add_box!(RWD, i), add_box!(RWD, Box(:g,B,[]));
add_wires!(RWD, Pair[(iv,1) => (iv, 1),
                     (fv, 1) => (iv, 2),
                     (iv, 2)=>(gv,1)]);

LWD = WiringDiagram([], []);
fv, gv = add_box!(LWD, Box(:f,[],B)), add_box!(LWD, Box(:g,B,[]));
add_wires!(LWD, Pair[
  (fv,1) => (gv,1),
]);


IWD = WiringDiagram([], []);
fv, gv = add_box!(IWD, Box(:f,[],[])), add_box!(IWD, Box(:g,[],[]));

XWD = WiringDiagram([:A,:A],[:D,:B])
fv, gv, hv = add_box!(XWD, f), add_box!(XWD, g), add_box!(XWD, h)
fv2, iv = add_box!(XWD, f), add_box!(XWD, i);
add_wires!(XWD, Pair[
  (input_id(XWD),1) => (fv,1),
  (iv,1) => (iv, 1), (fv, 1) => (iv, 2), (iv, 2)=>(gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(XWD),1),
  (input_id(XWD),2) => (fv2,1),
  (fv2,1) => (output_id(XWD),2)]);

L=ACSetTransformation(IWD.diagram, LWD.diagram, Box=[1,2]);
R=ACSetTransformation(IWD.diagram, RWD.diagram, Box=[1,3]);
m=ACSetTransformation(LWD.diagram, GWD.diagram, Box=[1,2],InPort=[2],OutPort=[1],Wire=[1]);
@test is_isomorphic(XWD.diagram, rewrite_match(L,R,m))

# Graphs with attributes
########################

@present TheoryDecGraph(FreeSchema) begin
  E::Ob
  V::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)

  X::Data
  dec::Attr(E,X)
end

@present TheoryLabelledDecGraph <: TheoryDecGraph begin
  label::Attr(V,X)
end

const LabelledDecGraph = ACSetType(TheoryLabelledDecGraph, index=[:src,:tgt])

aI2 = @acset LabelledDecGraph{String} begin
  V = 2
  E = 0
  label = ["a","b"]
end

aarr = @acset LabelledDecGraph{String} begin
  V = 2
  E = 1
  src = [1]
  tgt = [2]
  dec = ["e1"]
  label = ["a","b"]
end

abiarr = @acset LabelledDecGraph{String} begin
  V = 2
  E = 2
  src = [1,2]
  tgt = [2,1]
  dec = ["e1","rev_e1"]
  label = ["a","b"]
end

aspan = @acset LabelledDecGraph{String} begin
  V = 3
  E = 2
  src = [1,1]
  tgt = [2,3]
  dec = ["e1","e2"]
  label = ["a","b","c"]
end

expected = @acset LabelledDecGraph{String} begin
  V = 3
  E = 3
  src = [1,1,2]
  tgt = [2,3,1]
  dec = ["e1","e2","rev_e1"]
  label = ["a","b","c"]
end


L = ACSetTransformation(aI2, aarr, V=[1,2]);
R = ACSetTransformation(aI2, abiarr, V=[1,2]);
m = ACSetTransformation(aarr, aspan, V=[2,1], E=[1]);  # sends 'a'->'b' and 'b'->'a'

@test_throws ErrorException("ACSet colimit does not exist: label attributes a != b") rewrite_match(L,R,m)

m = ACSetTransformation(aarr, aspan, V=[1,2], E=[1]);

@test is_isomorphic(expected, rewrite_match(L, R, m))

# Graphs
########

# Example graphs
I2 = Graph(2)
I3 = Graph(3)
#   e1   e2
# 1 <- 2 -> 3
span = Graph(3)
add_edges!(span, [2,2],[1,3])
# 1 -> 2
arr = path_graph(Graph, 2)
# 1 <-> 2
biarr = Graph(2)
add_edges!(biarr, [1,2],[2,1])
# 1 -> 2 -> 3 -> 1
tri = cycle_graph(Graph, 3)
# 4 <- 1 -> 2 and 2 <- 3 -> 4
dispan = Graph(4)
add_edges!(dispan, [1,1,3,3],[2,4,2,4])

#      e1
#    1 -> 2
# e2 |  / ^
#    vv   | e4
#    4 -> 3
#      e5
squarediag = Graph(4)
add_edges!(squarediag, [1,1,2,3,4],[2,4,4,2,3])

# Add a reverse arrow to span
span_w_arrow = Graph(3)
add_edges!(span_w_arrow,[1,1,2],[2,3,1])

L = CSetTransformation(I2, arr, V=[1,2])
R = CSetTransformation(I2, biarr, V=[1,2])
m = CSetTransformation(arr, span, V=[2,1], E=[1])
@test is_isomorphic(span_w_arrow, rewrite_match(L, R, m))

# Remove apex of a subspan (top left corner of squarediag, leaves the triangle behind)
L = CSetTransformation(I2, span, V=[1,3])
m = CSetTransformation(span, squarediag, V=[2,1,4], E=[1,2])
@test is_isomorphic(tri, rewrite_match(L,id(I2),m))

# Remove self-edge using a *non-monic* match morphism
two_loops = Graph(2)
add_edges!(two_loops,[1,2],[1,2]) # ↻1   2↺
one_loop = Graph(2)
add_edges!(one_loop,[2],[2]) # 1   2↺

L = CSetTransformation(I2, arr, V=[1,2])
m = CSetTransformation(arr, two_loops, V=[1, 1], E=[1])
@test is_isomorphic(one_loop, rewrite_match(L,id(I2),m))

# Simplest non-trivial, non-monic exmaple
@present TheoryFinSet(FreeSchema) begin
  X::Ob
end
const FinSetType = ACSetType(TheoryFinSet)

I, L, G = [FinSetType() for _ in 1:3]
add_parts!(I,:X,2)
add_parts!(L,:X,1)
add_parts!(G,:X,1)
l = CSetTransformation(I,L,X=[1,1])
m = CSetTransformation(L,G,X=[1])
@test can_pushout_complement(l,m)
ik, kg = pushout_complement(l,m)
# There are 3 functions `ik` that make this a valid P.C.
# codom=1 with [1,1], codom=2 with [1,2] or [2,1]
K = codom(ik)
@test nparts(K, :X) == 1 # algorithm currently picks the first option

# Non-discrete interface graph. Non-monic matching
arr_loop= Graph(2)
add_edges!(arr_loop,[1,2],[2,2])  # 1->2↺
arrarr = Graph(2)
add_edges!(arrarr, [1,1],[2,2]) #  1⇉2
arrarr_loop = Graph(2)
add_edges!(arrarr_loop,[1,1,2],[2,2,2]) # 1⇉2↺
arr_looploop = Graph(2)
add_edges!(arr_looploop, [1,2,2],[2,2,2]) # 1-> ↻2↺

L = CSetTransformation(arr, arr, V=[1,2],E=[1]) # identity
R = CSetTransformation(arr, arrarr, V=[1,2], E=[1])
m = CSetTransformation(arr, arr_loop, V=[2,2], E=[2]) # NOT MONIC
@test is_isomorphic(arr_looploop, rewrite_match(L,R,m))

# only one monic match
@test is_isomorphic(arrarr_loop, rewrite(L, R, arr_loop, true))

# two possible morphisms L -> squarediag, but both violate dangling condition
L = CSetTransformation(arr, span, V=[1,2], E=[1]);
m = CSetTransformation(span, squarediag, V=[2,1,4], E=[1,2]);
@test (:src, 5, 4) in dangling_condition(ComposablePair(L,m))

# violate id condition because two orphans map to same point
L = CSetTransformation(I2, biarr, V=[1,2]); # delete both arrows
m = CSetTransformation(biarr, arr_loop, V=[2,2], E=[2,2]);
@test (1, 2) in id_condition(ComposablePair(L[:E],m[:E]))[2]
L = CSetTransformation(arr, biarr, V=[1,2], E=[1]); # delete one arrow
@test 1 in id_condition(ComposablePair(L[:E],m[:E]))[1]

span_triangle = Graph(3); # 2 <- 1 -> 3 (with edge 2->3)
add_edges!(span_triangle,[1,1,2], [2,3,3]);

L = CSetTransformation(arr, tri, V=[1,2], E=[1]);
m = CSetTransformation(tri, squarediag, V=[2,4,3], E=[3,5,4]);
@test is_isomorphic(span_triangle, rewrite_match(L,id(arr),m))

k, g = pushout_complement(L, m); # get PO complement to do further tests

# the graph interface is equal to the final graph b/c we only delete things
@test is_isomorphic(span_triangle, codom(k))

# Check pushout properties 1: apex is the original graph
@test is_isomorphic(squarediag, pushout(L, k).cocone.apex) # recover original graph

# Check pushout properties 2: the diagram commutes
Lm = compose(L,m);
kg = compose(k,g);
for I_node in 1:2
  @test Lm[:V](I_node) == kg[:V](I_node)
end
@test Lm[:E](1) == kg[:E](1)

# Check pushout properties 3: for every pair of unmatched things between K and L, they are NOT equal
for K_node in 1:3
  @test m[:V](3) != g[:V](K_node)
end

for K_edge in 2:3
  @test m[:E](3) != g[:E](K_edge)
end

# Undirected bipartite graphs
#############################

# 1 --- 1
#    /
# 2 --- 2

z_ = UndirectedBipartiteGraph()
add_vertices₁!(z_, 2)
add_vertices₂!(z_, 2)
add_edges!(z_, [1,2,2], [1,1,2])

line = UndirectedBipartiteGraph()
add_vertices₁!(line, 1)
add_vertices₂!(line, 2)
add_edges!(line, [1], [1])

parallel = UndirectedBipartiteGraph()
add_vertices₁!(parallel, 2)
add_vertices₂!(parallel, 2)
add_edges!(parallel, [1,2], [1,2])

merge = UndirectedBipartiteGraph()
add_vertices₁!(merge, 2)
add_vertices₂!(merge, 2)
add_edges!(merge, [1,2], [1,1])

Lspan = UndirectedBipartiteGraph()
add_vertices₁!(Lspan, 1)
add_vertices₂!(Lspan, 2)
add_edges!(Lspan, [1,1],[1,2])

I = UndirectedBipartiteGraph()
add_vertices₁!(I, 1)
add_vertices₂!(I, 2)

L = CSetTransformation(I, Lspan, V₁=[1], V₂=[1,2])
R = CSetTransformation(I, line, V₁=[1], V₂=[1,2])
m1 = CSetTransformation(Lspan, z_, V₁=[1], V₂=[1,2], E=[1, 2])
m2 = CSetTransformation(Lspan, z_, V₁=[1], V₂=[2,1], E=[2, 1])

@test is_isomorphic(parallel, rewrite_match(L, R, m1))
@test is_isomorphic(merge, rewrite_match(L, R, m2))

# Hypergraph homomorphisms
##########################

"""Theory of Acset schemas"""
@present TheoryACSetSchema(FreeSchema) begin
  (Name, AttrType) :: Data
  (HomOb, ObOb, AttrOb, DataOb, AIndex, HIndex) :: Ob
  (hsrc, htgt) :: Hom(HomOb,ObOb)
  asrc  :: Hom(AttrOb, ObOb)
  atgt  :: Hom(AttrOb,DataOb)
  hind  :: Hom(HIndex, HomOb)
  aind  :: Hom(AIndex, AttrOb)
  hname :: Attr(HomOb,Name)
  oname :: Attr(ObOb,Name)
  dname :: Attr(DataOb,Name)
  dtype :: Attr(DataOb,AttrType)
  aname :: Attr(AttrOb,Name)
end

const MetaCatDesc = ACSetType(TheoryACSetSchema, index=[
  :hsrc, :htgt, :asrc, :atgt, :hname, :oname, :dname, :aname]){Symbol, DataType}

"""Theory of Acset instances"""
@present TheoryACSet <: TheoryACSetSchema begin
  AttrVal :: Data
  (Row, FK, Datum) :: Ob
  rowob :: Hom(Row, ObOb)
  (fksrc, fktgt) :: Hom(FK, Row)
  fkhom :: Hom(FK, HomOb)
  drow :: Hom(Datum, Row)
  dattr :: Hom(Datum, AttrOb)
  dval :: Attr(Datum, AttrVal)
end

const MetaACSet = ACSetType(TheoryACSet, index=[
  :hsrc, :htgt, :asrc, :atgt, :hname, :oname, :dname, :aname]
  ){Symbol, DataType, Any}

"""Theory of Acset transformations"""
@present TheoryACSetTrans <: TheoryACSetSchema begin
  AttrVal :: Data

  # Src Data
  (Row1, FK1, Datum1) :: Ob
  rowob1 :: Hom(Row1, ObOb)
  (fksrc1, fktgt1) :: Hom(FK1, Row1)
  fkhom1 :: Hom(FK1, HomOb)
  drow1 :: Hom(Datum1, Row1)
  dattr1 :: Hom(Datum1, AttrOb)
  dval1 :: Attr(Datum1, AttrVal)

  # Tgt data
  (Row2, FK2, Datum2) :: Ob
  rowob2 :: Hom(Row2, ObOb)
  (fksrc2, fktgt2) :: Hom(FK2, Row2)
  fkhom2 :: Hom(FK2, HomOb)
  drow2 :: Hom(Datum2, Row2)
  dattr2 :: Hom(Datum2, AttrOb)
  dval2 :: Attr(Datum2, AttrVal)

  # Components
  comp :: Hom(Row1, Row2)
end

const MetaACSetTransformation = ACSetType(
  TheoryACSetTrans){Symbol, DataType, Any}

"""Convert an Acset description into its Acset representation"""
function to_cset(ad::AttrDesc, datatypes::Vector{Any}, inds::Vector{Symbol})::ACSet
  res = MetaCatDesc()
  catdesc, dtypes, anames, asrc, atgt = typeof(ad).parameters
  obj, homs, src, tgt = catdesc.parameters
  add_parts!(res, :ObOb, length(obj), oname=obj)
  add_parts!(res, :HomOb, length(homs), hname=homs, hsrc=src, htgt=tgt)
  add_parts!(res, :DataOb, length(dtypes), dname=dtypes,dtype=datatypes);
  add_parts!(res, :AttrOb, length(anames), aname=anames, asrc=asrc, atgt=atgt);
  hinds = filter(x-> x in homs, inds)
  ainds = filter(x -> x in anames, inds)
  add_parts!(res, :HIndex, length(hinds), hind=[findfirst(x->x==i, homs) for i in hinds]);
  add_parts!(res, :AIndex, length(ainds), aind=[findfirst(x->x==i, anames) for i in ainds]);
  return res
end

"""
For each Ob in the cset, copy its table into res
(only if the corresponding table in res is empty)
Optionally use a dict to map names from the first schema to the second

Helper function to construct MetaACSetTransformations
"""
function inject_cset(cset::ACSet, res::ACSet, mapping::Dict{Symbol, Symbol}=Dict{Symbol,Symbol}())::ACSet
  for (k, v) in zip(keys(cset.tables), cset.tables)
    k_ = get(mapping, k, k)
    if haskey(res.tables, k_) && isempty(res.tables[k_])
      add_parts!(res, k_, length(v))
    end
  end
  srchom, reshom = [typeof(x).parameters[2].parameters[1].parameters[2] for x in [cset, res]]
  for h in srchom
    h_ = get(mapping, h, h)
    if h_ in reshom
      set_subpart!(res, h_, cset[h])
    end
  end
  srcattr, resattr = [typeof(x).parameters[2].parameters[3] for x in [cset, res]]
  for a in srcattr
    a_ = get(mapping, a, a)
    if a_ in resattr
      set_subpart!(res, a_, cset[a])
    end
  end

  return res
end

"""
Create a CSet to describe the data of a CSet
"""
function to_cset(cset::ACSet)::Pair{ACSet, Dict{Pair{Symbol, Int}, Int}}
  tparams = typeof(cset).parameters;
  catdesc = to_cset(tparams[2](),
                    collect(tparams[3].parameters),
                    Vector{Symbol}(collect(tparams[4])));

  # Copy over info from the catdesc
  res = inject_cset(catdesc, MetaACSet())

  # map table+row pair to unique row index
  rowdict = Dict{Pair{Symbol, Int}, Int}()
  row_counter = 0
  for (k, v) in zip(keys(cset.tables), cset.tables)
    ob = catdesc.indices[:oname][k][1]
    for i in 1:length(v)
      row_counter+=1
      rowdict[k => i] = row_counter
      add_part!(res, :Row, rowob=ob)
    end
  end
  for (k, v) in zip(keys(cset.tables), cset.tables)
    ob = catdesc.indices[:oname][k][1]
    homs = catdesc.indices[:hsrc][ob]
    attrs = catdesc.indices[:asrc][ob]
    for (i, row) in enumerate(v)
      row_id = rowdict[k => i]
      row_counter += 1
      for morph in homs
        morphname = catdesc[:hname][morph]
        tgt_name  = catdesc[:oname][catdesc[:htgt][morph]]
        add_part!(res, :FK, fksrc=row_id, fkhom=morph,
                            fktgt=rowdict[tgt_name => row[morphname]])
      end
      for at in attrs
        attrname = catdesc[:aname][at]
        add_part!(res, :Datum, drow=row_id, dattr=at, dval=row[attrname])
      end
    end
  end

  return res => rowdict
end

"""
Create an ACSet to describe the data of a ACSetTransformation

Helper function to construct HΣrewrite
"""
function to_cset(m::ACSetTransformation)::Tuple{ACSet, Dict{Pair{Symbol, Int}, Int}, Dict{Pair{Symbol, Int}, Int}}
  tparams = typeof(dom(m)).parameters;
  catdesc = to_cset(tparams[2](),
                    collect(tparams[3].parameters),
                    Vector{Symbol}(collect(tparams[4])));

  # Copy over info from the catdesc
  res = inject_cset(catdesc, ACSetType(TheoryACSetTrans){Symbol, DataType, Any}())

  src, srcdict = to_cset(dom(m));
  tgt, tgtdict = to_cset(codom(m));

  allnames = ["Row", "FK", "Datum", "rowob", "fksrc", "fktgt", "fkhom", "drow", "dattr", "dval"]
  d1, d2 = [Dict([Symbol(x)=> Symbol(string(x)*i) for x in allnames]) for i in ["1", "2"]]
  res = inject_cset(src, res, d1)
  res = inject_cset(tgt, res, d2)

  # add components
  comps = repeat([0], nparts(res,:Row1))
  for (k, v) in zip(keys(components(m)), components(m))
    for (i, val) in enumerate(v.func)
      comps[srcdict[k=>i]] = tgtdict[k => val]
    end
  end
  set_subpart!(res, :comp, comps)
  return (res, srcdict, tgtdict)
end


"""
Given morphisms C1->C3<-C2, induce a morphism between the morphisms
via a morphism C1 -> C2

Helper function to construct HΣrewrite
"""
function transformation_of_transformations(m1::ACSetTransformation, m2::ACSetTransformation, msrc::ACSetTransformation)::ACSetTransformation
  (m1_, src1, tgt1), (m2_, src2, tgt2) = to_cset(m1), to_cset(m2)
  comps = Dict{Symbol, Vector{Int}}([comp => collect(1:nparts(m1_,comp))
                for comp in [:HomOb,:ObOb,:AttrOb, :DataOb, :AIndex, :HIndex]])
  r1, fk1, d1 = [repeat([0], nparts(m1_,x)) for x in [:Row1, :FK1, :Datum1]]
  r2, fk2, d2 = [collect(1:nparts(m2_,x)) for x in [:Row2, :FK2, :Datum2]]
  for (k, vs) in zip(keys(components(msrc)), components(msrc))
    for (i, v) in enumerate(vs.func)
      r1[src1[k => i]] = src2[k => v]
      # this will fail if msrc.domain has any FKs / attributes
      # for our example below, this is ok
    end
  end
  for (k, v) in zip([r1, fk1, d1, r2, fk2, d2],
                    [:Row1, :FK1, :Datum1, :Row2, :FK2, :Datum2])
    comps[v] = k
  end
  res = ACSetTransformation(m1_, m2_; comps...)
  return res
end

@present ThHypP(FreeSchema) begin
  (V, E₁₁, E₂₁)::Ob
  Name::Data
  (s, t)::Hom(E₁₁, V)
  (s₁, s₂, t₁)::Hom(E₂₁, V)
  Label₁::Attr(E₁₁, Name)
  Label₂::Attr(E₂₁, Name)
end

HypergraphP = ACSetType(ThHypP)
HΣ = @acset HypergraphP{Symbol} begin
  V = 1
  E₁₁ = 2
  E₂₁ = 1
  s = [1,1]
  t = [1,1]
  s₁ = [1]
  s₂ = [1]
  t₁ = [1]
  Label₁ = [:f, :g]
  Label₂ = [:plus]
end

H = @acset HypergraphP{Symbol} begin
  V = 9
  E₁₁ = 4
  E₂₁ = 2
  s = [1,2,3,6]
  t = [4,5,6,8]
  s₁ = [4,7]
  s₂ = [5,8]
  t₁ = [7,9]
  Label₁ = [:f, :g, :f, :g]
  Label₂ = [:plus,:plus]
end

ϕ = ACSetTransformation(H, HΣ, V=ones(Int, 9), E₁₁ = [1,2,1,2], E₂₁ = ones(Int,2))
(m1_,Hdict, HΣdict) = to_cset(ϕ);

HL = @acset HypergraphP{Symbol} begin
  V = 5
  E₂₁ = 2
  s₁ = [1,3]
  s₂ = [2,4]
  t₁ = [3,5]
  Label₂ = [:plus,:plus]
end

HK = @acset HypergraphP{Symbol} begin
  V = 3
end

HR = @acset HypergraphP{Symbol} begin
  V = 5
  E₂₁ = 2
  s₁ = [2,1]
  s₂ = [3,4]
  t₁ = [4,5]
  Label₂ = [:plus,:plus]
end

L = ACSetTransformation(HK, HL, V=[1,2,4])
R = ACSetTransformation(HK, HR, V=[1,2,3])
m= ACSetTransformation(HL, H, V=[4,5,7,8,9], E₂₁ = [1,2])
Hrewrite = rewrite_match(L,R,m); # WORKS
ϕHrewrite = ACSetTransformation(Hrewrite, HΣ, V=ones(Int,9), E₁₁ = [1,2,1,2], E₂₁ = [1,1])
ϕHrewrite_ = to_cset(ϕHrewrite)[1]; # convert to acset to check isomorphism later


ϕL = ACSetTransformation(HL, HΣ, V=ones(Int, 5),E₂₁ = [1,1]);
ϕK = ACSetTransformation(HK, HΣ, V=ones(Int, 3));
ϕR = ACSetTransformation(HR, HΣ, V=ones(Int, 5), E₂₁ = [1,1]);


(ϕ_,Hdict, HΣdict) = to_cset(ϕ);
(L_,HLdict, HLΣdict) = to_cset(ϕL);
(K_,HKdict, HKΣdict) = to_cset(ϕK);
(R_,HRdict, HRΣdict) = to_cset(ϕR);
l_ = transformation_of_transformations(ϕK, ϕL, L);
r_ = transformation_of_transformations(ϕK, ϕR, R);
m_ = homomorphism(L_, ϕ_); # there is only 1
HΣrewrite = rewrite_match(l_,r_,m_);

@test is_isomorphic(ϕHrewrite_, HΣrewrite)

end
