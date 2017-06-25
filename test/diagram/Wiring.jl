module TestWiring

using Catlab.Doctrine
using Catlab.Diagram.Wiring
using Base.Test

# Low-level graph interface
###########################

A,B,C,D = [ ob(FreeSymmetricMonoidalCategory, sym) for sym in [:A,:B,:C,:D] ]
f = hom(:f, A, B)
g = hom(:g, B, C)

d = WiringDiagram(A, C)
@test nboxes(d) == 0
@test box(d,input_id(d)) == d
@test box(d,output_id(d)) == d

# Operations on boxes
fv = add_box!(d, f)
@test nboxes(d) == 1
@test box(d, fv) == HomBox(f)
rem_box!(d, fv)
@test nboxes(d) == 0

fv = add_box!(d, f)
gv = add_box!(d, g)
@test nboxes(d) == 2
@test boxes(d) == [HomBox(f),HomBox(g)]

# Operations on wires
@test nwires(d) == 0
@test !has_wire(d, fv, gv)
add_wire!(d, (input_id(d),1) => (fv,1))
add_wire!(d, (fv,1) => (gv,1))
add_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d) == 3
@test has_wire(d, fv, gv)
@test wires(d) == map(Wire, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(d),1),
])
@test all_neighbors(d, fv) == [input_id(d),gv]
@test all_neighbors(d, gv) == [fv,output_id(d)]
@test neighbors(d, fv) == [gv]
@test out_neighbors(d, fv) == [gv]
@test in_neighbors(d, gv) == [fv]
@test out_wires(d, Port(fv,Output,1)) == [ Wire((fv,1) => (gv,1)) ]
@test in_wires(d, Port(gv,Input,1)) == [ Wire((fv,1) => (gv,1)) ]
rem_wires!(d, fv, gv)
@test nwires(d) == 2
@test !has_wire(d, fv, gv)

# Substitution
f, g, h = hom(:f,A,B), hom(:g,B,C), hom(:h,C,D)
sub = WiringDiagram(B,D)
gv = add_box!(sub, g)
hv = add_box!(sub, h)
add_wires!(sub, Pair[
  (input_id(sub),1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(sub),1),
])
d = WiringDiagram(A,D)
fv = add_box!(d, f)
subv = add_box!(d, sub)
add_wires!(sub, Pair[
  (input_id(d),1) => (fv,1),
  (fv,1) => (subv,1),
  (subv,1) => (output_id(d),1),
])
@test boxes(d) == [ HomBox(f), sub ]
@test boxes(sub) == [ HomBox(g), HomBox(h) ]
substitute!(d, subv)
@test nboxes(d) == 3
@test Set(boxes(d)) == Set([ HomBox(f), HomBox(g), HomBox(h) ])
box_map = Dict(box(d,v).expr => v for v in box_ids(d))
@test nwires(d) == 4
@test Set(wires(d)) == Set(map(Wire, [
  (input_id(d),1) => (box_map[f],1),
  (box_map[f],1) => (box_map[g],1),
  (box_map[g],1) => (box_map[h],1),
  (box_map[h],1) => (output_id(d),1),
]))

end
