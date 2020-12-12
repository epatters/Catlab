""" Data structure for (directed) wiring diagrams, aka string diagrams.

A (directed) wiring diagram consists of a collection of boxes with input and
output ports connected by wires. A box can be atomic (possessing no internal
structure) or can itself be a wiring diagram. Thus, wiring diagrams can be
nested recursively. Wiring diagrams are closely related to what the CS
literature calls "directed graphs with ports" or more simply "port graphs". The
main difference is that a wiring diagram has an "outer box": a wiring diagram
has its own ports that can be connected to the ports of its boxes.

This module provides a generic data structure for wiring diagrams. Arbitrary
data can be attached to the boxes, ports, and wires of a wiring diagram. The
diagrams are "abstract" in the sense that they cannot be directly rendered as
raster or vector graphics. However, they form a useful intermediate
representation that can be serialized to and from GraphML or translated into
Graphviz or other declarative diagram languages.
"""
module DirectedWiringDiagrams
export AbstractBox, Box, WiringDiagram, Wire, Port, PortKind,
  InputPort, OutputPort, input_ports, output_ports, input_id, output_id,
  outer_ids, boxes, box_ids, nboxes, nwires, box, wires, has_wire, graph,
  add_box!, add_boxes!, add_wire!, add_wires!, rem_box!, rem_boxes!, rem_wire!,
  rem_wires!, port_value, validate_ports, is_permuted_equal,
  all_neighbors, neighbors, outneighbors, inneighbors, in_wires, out_wires,
  singleton_diagram, induced_subdiagram, encapsulated_subdiagram,
  ocompose, substitute, encapsulate

using Compat
using AutoHashEquals

using ...Present, ...CSetDataStructures, ...Graphs.BasicGraphs
using ...Graphs.BasicGraphs: TheoryGraph
import ...Graphs: all_neighbors, neighbors, outneighbors, inneighbors

# Data types
############

""" Kind of port: input or output.
"""
@enum PortKind InputPort OutputPort

""" A port on a box to which wires can be connected.
"""
@auto_hash_equals struct Port
  box::Int
  kind::PortKind
  port::Int
end
set_box(port::Port, box::Int) = Port(box, port.kind, port.port)

function Base.isless(p1::Port, p2::Port)::Bool
  # Lexicographic order.
  p1.box < p2.box ||
    (p1.box == p2.box &&
      (p1.kind < p2.kind || (p1.kind == p2.kind && p1.port < p2.port)))
end

""" A wire connecting one port to another.
"""
@auto_hash_equals struct Wire{Value}
  value::Value
  source::Port
  target::Port
end

Wire(value, src::Tuple{Int,PortKind,Int}, tgt::Tuple{Int,PortKind,Int}) =
  Wire(value, Port(src[1],src[2],src[3]), Port(tgt[1],tgt[2],tgt[3]))
Wire(value, src::Tuple{Int,Int}, tgt::Tuple{Int,Int}) =
  Wire(value, Port(src[1],OutputPort,src[2]), Port(tgt[1],InputPort,tgt[2]))
Wire(value, pair::Pair) = Wire(value, first(pair), last(pair))

Wire(src::Port, tgt::Port) = Wire(nothing, src, tgt)
Wire(src::Tuple, tgt::Tuple) = Wire(nothing, src, tgt)
Wire(pair::Pair) = Wire(nothing, first(pair), last(pair))

function Base.show(io::IO, wire::Wire)
  skip_kind = wire.source.kind == OutputPort && wire.target.kind == InputPort
  show_port = (io::IO, port::Port) -> begin
    if skip_kind
      print(io, "($(port.box),$(port.port))")
    else
      print(io, "($(port.box),$(string(port.kind)),$(port.port)")
    end
  end
  print(io, "Wire(")
  if !isnothing(wire.value)
    show(io, wire.value)
    print(io, ", ")
  end
  show_port(io, wire.source)
  print(io, " => ")
  show_port(io, wire.target)
  print(io, ")")
end

function Base.isless(w1::Wire, w2::Wire)::Bool
  # Lexicographic order.
  isless(w1.source, w2.source) ||
    (w1.source == w2.source && isless(w1.target, w2.target))
end

""" Base type for any box (node) in a wiring diagram.

This type represents an arbitrary black box with inputs and outputs.
"""
abstract type AbstractBox end

""" An atomic box in a wiring diagram.

These boxes have no internal structure.
"""
@auto_hash_equals struct Box{Value} <: AbstractBox
  value::Value
  input_ports::Vector
  output_ports::Vector
end

Box(inputs::Vector, outputs::Vector) = Box(nothing, inputs, outputs)

input_ports(box::Box) = box.input_ports
output_ports(box::Box) = box.output_ports

function Base.show(io::IO, box::Box)
  print(io, "Box(")
  if !isnothing(box.value)
    show(io, box.value)
    print(io, ", ")
  end
  print(io, "[")
  join(io, [sprint(show, port) for port in box.input_ports], ",")
  print(io, "], [")
  join(io, [sprint(show, port) for port in box.output_ports], ",")
  print(io, "])")
end

@present TheoryWiringDiagramGraph <: TheoryGraph begin
  Box::Data
  WireData::Data

  box::Attr(V,Box)
  wire::Attr(E,WireData)
end

const WiringDiagramGraphUnionAll =
  ACSetType(TheoryWiringDiagramGraph, index=[:src, :tgt])

""" Internal datatype for graph underlying a directed wiring diagram.

Boxes and wires are attached to vertices and edges, respectively.
"""
# const WiringDiagramGraph = WiringDiagramGraphUnionAll{
#   Union{AbstractBox,Nothing},WireData}

@present TheoryWiringDiagram(FreeSchema) begin
  Box::Ob
  (InPort, OutPort, OuterInPort, OuterOutPort)::Ob
  (Wire, InWire, OutWire, PassWire)::Ob
  
  src::Hom(Wire, OutPort)
  tgt::Hom(Wire, InPort)
  in_src::Hom(InWire, OuterInPort)
  in_tgt::Hom(InWire, InPort)
  out_src::Hom(OutWire, OutPort)
  out_tgt::Hom(OutWire, OuterOutPort)
  pass_src::Hom(PassWire, OuterInPort)
  pass_tgt::Hom(PassWire, OuterOutPort)

  in_port_box::Hom(InPort, Box)
  out_port_box::Hom(OutPort, Box)
end

const AbstractWiringDiagramACSet = AbstractACSetType(TheoryWiringDiagram)

@present TheoryTypedWiringDiagram <: TheoryWiringDiagram begin
  PortType::Data
  in_port_type::Attr(InPort, PortType)
  out_port_type::Attr(OutPort, PortType)
  outer_in_port_type::Attr(OuterInPort, PortType)
  outer_out_port_type::Attr(OuterOutPort, PortType)
end

@present TheoryAttributedWiringDiagram <: TheoryTypedWiringDiagram begin
  BoxName::Data
  WireValue::Data

  name::Attr(Box, BoxName)
  wire_value::Attr(Wire, WireValue)
  in_wire_value::Attr(InWire, WireValue)
  out_wire_value::Attr(OutWire, WireValue)
  pass_wire_value::Attr(PassWire, WireValue)
end

const WiringDiagramACSet = ACSetType(TheoryAttributedWiringDiagram,
  index=[:src, :tgt, :in_src, :in_tgt, :out_src, :out_tgt, :pass_src, :pass_tgt])

""" A directed wiring diagram, also known as a string diagram.

The wiring diagram is implemented using the following internal data structure.
The "skeleton" of the diagram is an instance of `Catlab.Graphs.AbstractGraph`: a
directed multigraph whose vertices correspond to boxes and whose edges
correspond to wires. There are two special vertices, accessible via `input_id`
and `output_id`, that represent the input and output ports of the outer box.
"""

mutable struct WiringDiagram{Theory, BoxName, PortType, WireValue} <: AbstractBox
  # mutable struct WiringDiagram{Theory} <: AbstractBox
  #   graph::WiringDiagramGraph
  #   value::Any
  #   input_ports::Vector
  #   output_ports::Vector
  diagram::WiringDiagramACSet{PortType,BoxName,WireValue}
  value::Any
  

  # function WiringDiagram{T}(value, inputs::Vector, outputs::Vector) where T
  #   graph = WiringDiagramGraph()
  #   diagram = new{T}(graph, value, inputs, outputs)
  #   add_vertices!(graph, 2, box=nothing)
  #   return diagram
  # end
  function WiringDiagram{T, BoxName, PortType, WireValue}(value, inputs::Vector, outputs::Vector) where {T, BoxName, PortType, WireValue}
    diagram = WiringDiagramACSet{PortType, BoxName, WireValue}()
    f = new{T, BoxName, PortType, WireValue}(diagram, value)
    add_parts!(diagram, :OuterInPort, length(inputs),   outer_in_port_type=inputs)
    add_parts!(diagram, :OuterOutPort, length(outputs), outer_out_port_type=outputs)
    return f
  end
  function WiringDiagram(f::WiringDiagram{T, BoxName, PortType, WireValue}) where {T, BoxName, PortType, WireValue}
    # Copy constructor for shallow copy
    new{T, BoxName, PortType, WireValue}(copy(f.diagram), f.value)
  end
end



function WiringDiagram{T, BoxName, PortType, WireValue}(inputs::Vector, outputs::Vector) where {T, BoxName, PortType, WireValue}
  WiringDiagram{T, BoxName, PortType, WireValue}(nothing, inputs, outputs)
end
WiringDiagram(args...) = WiringDiagram{Any, Any, Any, Any}(args...)

input_id(::WiringDiagram) = -2
output_id(::WiringDiagram) = -1
outer_ids(::WiringDiagram) = (-2,-1)

""" Check equality of wiring diagrams.

Warning: This method checks equality of the underlying graph representation, not
mathematical equality which involves graph isomorphism.

See also: `is_permuted_equal`
"""
function Base.:(==)(d1::WiringDiagram, d2::WiringDiagram)
  (input_ports(d1) == input_ports(d2) &&
   output_ports(d1) == output_ports(d2) && d1.value == d2.value &&
   boxes(d1) == boxes(d2) && sort!(wires(d1)) == sort!(wires(d2)))
end

""" Check equality of wiring diagram under permutation of boxes.

When the boxes in the first diagram `d1` are permuted according to `σ`,
does it become identical to the second diagram `d2`?
"""
function is_permuted_equal(d1::WiringDiagram, d2::WiringDiagram, σ::Vector{Int})
  @assert nboxes(d1) == length(σ) && nboxes(d2) == length(σ)
  d1_ids, d2_ids = box_ids(d1), box_ids(d2)
  box_map = Dict{Int,Int}(d1_ids[σ[i]] => d2_ids[i] for i in eachindex(σ))
  is_induced_equal(d1, d2, box_map)
end
function is_induced_equal(d1::WiringDiagram, d2::WiringDiagram, box_map::Dict{Int,Int})
  box_map[input_id(d1)] = input_id(d2)
  box_map[output_id(d1)] = output_id(d2)
  map_wire = wire::Wire -> Wire(wire.value,
    set_box(wire.source, box_map[wire.source.box]),
    set_box(wire.target, box_map[wire.target.box]))
  (input_ports(d1) == input_ports(d2) && output_ports(d1) == output_ports(d2) &&
   all(box(d1,v) == box(d2,box_map[v]) for v in box_ids(d1)) &&
   sort!(map(map_wire, wires(d1))) == sort!(wires(d2)))
end

Base.copy(diagram::WiringDiagram) = WiringDiagram(diagram)

function Base.show(io::IO, diagram::WiringDiagram{T}) where T
  sshowcompact = x -> sprint(show, x, context=:compact => true)
  print(io, "WiringDiagram")
  if T != Any
    print(io, "{$T}")
  end
  print(io, "(")
  if !isnothing(diagram.value)
    show(io, diagram.value)
    print(io, ", ")
  end
  print(io, "[")
  join(io, map(sshowcompact, input_ports(diagram)), ",")
  print(io, "], [")
  join(io, map(sshowcompact, output_ports(diagram)), ",")
  print(io, "], ")
  if get(io, :compact, false)
    print(io, "{$(nboxes(diagram)) boxes}, {$(nwires(diagram)) wires}")
  else
    print(io, "\n[ $(input_id(diagram)) => {inputs},\n  ")
    print(io, "$(output_id(diagram)) => {outputs},\n  ")
    join(io, [ "$v => $(sshowcompact(box(diagram, v)))"
               for v in box_ids(diagram) ], ",\n  ")
    print(io, " ],\n[ ")
    join(io, map(sshowcompact, wires(diagram)), ",\n  ")
    print(io, " ]")
  end
  print(io, ")")
end

# Imperative interface
######################

# Basic accessors.

function box(f::WiringDiagram, b::Int)
  if b == input_id(f)
    return nothing
  elseif b == output_id(f)
    return nothing
  else
    Box(subpart(f.diagram, b, :name), input_ports(f, b), output_ports(f, b))
  end
end

boxes(f::WiringDiagram) = map(b -> box(f, b), box_ids(f))
nboxes(f::WiringDiagram) = nparts(f.diagram, :Box)
box_ids(f::WiringDiagram) = parts(f.diagram, :Box)
box_id(f::WiringDiagram, b::Int) = b # box_ids(f)[b]

src_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:src, :out_port_box])
tgt_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:tgt, :in_port_box])
src_box_id(f::WiringDiagram, w::Int) = src_box(f,w)#box_ids(f)[src_box(f, w)]
tgt_box_id(f::WiringDiagram, w::Int) = tgt_box(f, w)#box_ids(f)[tgt_box(f, w)]

in_tgt_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:in_tgt, :in_port_box])
in_tgt_box_id(f::WiringDiagram, w::Int) = in_tgt_box(f,w)#box_ids(f)[in_tgt_box(f,w)]

out_src_box(f::WiringDiagram, w::Int) = subpart(f.diagram, w, [:out_src, :out_port_box])
out_src_box_id(f::WiringDiagram, w::Int) = out_src_box(f,w)#box_ids(f)[out_src_box(f,w)]


local_in_port_id(f::WiringDiagram, b::Int, p::Int) = searchsorted(incident(f.diagram, b, :in_port_box), p)[1]
local_out_port_id(f::WiringDiagram, b::Int, p::Int) = searchsorted(incident(f.diagram, b, :out_port_box), p)[1]

in_port_id(f::WiringDiagram, b::Int, p::Int) = incident(f.diagram, b, :in_port_box)[p]
out_port_id(f::WiringDiagram, b::Int, p::Int) = incident(f.diagram, b, :out_port_box)[p]
in_port_id(f::WiringDiagram, p::Port) = in_port_id(f, p.box, p.port)
out_port_id(f::WiringDiagram, p::Port) = out_port_id(f, p.box, p.port)

pass_wire(f::WiringDiagram, w::Int) = Wire(subpart(f.diagram, w, :pass_wire_value),
  (input_id(f), subpart(f.diagram, w, :pass_src)) =>
  (output_id(f), subpart(f.diagram, w, :pass_tgt)))

in_wire(f::WiringDiagram, w::Int) = Wire(subpart(f.diagram, w, :in_wire_value), 
  (input_id(f), subpart(f.diagram, w, :in_src)) => 
  (in_tgt_box_id(f,w), local_in_port_id(f, in_tgt_box(f,w), subpart(f.diagram, w, :in_tgt))))

out_wire(f::WiringDiagram, w::Int) = Wire(subpart(f.diagram, w, :out_wire_value), 
  (out_src_box_id(f,w), local_out_port_id(f, out_src_box(f,w), subpart(f.diagram, w, :out_src))) =>
  (output_id(f), subpart(f.diagram, w, :out_tgt)) )

wire(f::WiringDiagram, w::Int) = Wire( subpart(f.diagram, w, :wire_value),
  (src_box_id(f,w), local_out_port_id(f, src_box(f,w), subpart(f.diagram, w, :src))) =>
  (tgt_box_id(f,w), local_in_port_id(f, tgt_box(f,w), subpart(f.diagram, w, :tgt))))


function wires(f::WiringDiagram, src::Int, tgt::Int)
  if src == input_id(f) && tgt == output_id(f)
    [pass_wire(f, w) for w in parts(f.diagram, :PassWire)]
  elseif src == input_id(f)
    [in_wire(f, w) for w in parts(f.diagram, :InWire) if in_tgt_box_id(f, w) == tgt]
  elseif tgt == output_id(f)
    [out_wire(f, w) for w in parts(f.diagram, :OutWire) if out_src_box_id(f, w) == src]
  else
    [wire(f, w) for w in parts(f.diagram, :Wire) if 
        src_box_id(f,w)==src && tgt_box_id(f,w)==tgt]
  end
end

pass_wires(f::WiringDiagram) = [pass_wire(f, w) for w in parts(f.diagram, :PassWire)]
in_wires(f::WiringDiagram) = [in_wire(f, w) for w in parts(f.diagram, :InWire)]
out_wires(f::WiringDiagram) = [out_wire(f, w) for w in parts(f.diagram, :OutWire)]
internal_wires(f::WiringDiagram) = [wire(f, w) for w in parts(f.diagram, :Wire)]
wires(f::WiringDiagram) = pass_wires(f) ∪ in_wires(f) ∪ out_wires(f) ∪ internal_wires(f)


npass_wires(f::WiringDiagram) = nparts(f.diagram, :PassWire)
nin_wires(f::WiringDiagram) = nparts(f.diagram, :InWire)
nout_wires(f::WiringDiagram) = nparts(f.diagram, :OutWire)
ninternal_wires(f::WiringDiagram) = nparts(f.diagram, :Wire)
nwires(f::WiringDiagram) = npass_wires(f) + nin_wires(f) + nout_wires(f) + ninternal_wires(f)


has_pass_wire(f::WiringDiagram) = !isempty(parts(f.diagram, :PassWire))
has_in_wire(f::WiringDiagram, tgt::Int) = !isempty(incident(f.diagram, tgt, :in_tgt))
has_out_wire(f::WiringDiagram, src::Int) = !isempty(incident(f.diagram, src, :out_src))
has_internal_wire(f::WiringDiagram, src::Int, tgt::Int) = 
  !isempty(incident(f.diagram, src, :src) ∩ incident(f.diagram, tgt, :tgt))

function has_wire(f::WiringDiagram, src::Int, tgt::Int)
  if src == input_id(f) && tgt == output_id(f)
    has_pass_wire(f)
  elseif src == input_id(f)
    has_in_wire(f, tgt)
  elseif tgt == output_id(f)
    has_out_wire(f, src)
  else
    has_internal_wire(f, src, tgt)
  end
end

has_wire(f::WiringDiagram, wire::Wire) = has_wire(f, wire.source.box, wire.target.box)
has_wire(f::WiringDiagram, pair::Pair) = has_wire(f, first(pair)[1], last(pair)[1])





input_ports(f::WiringDiagram) = subpart(f.diagram, :outer_in_port_type)
output_ports(f::WiringDiagram) = subpart(f.diagram, :outer_out_port_type)

function input_ports(f::WiringDiagram, b::Int)
  if b == input_id(f)
    error("Input vertex does not have input ports within wiring diagram")
  elseif b == output_id(f)
    output_ports(f)
  else
    copy(subpart(f.diagram, incident(f.diagram, b, :in_port_box), :in_port_type)) # copy because to use in Box constructor
  end
end

function output_ports(f::WiringDiagram, b::Int)
  if b == input_id(f)
    input_ports(f)
  elseif b == output_id(f)
    error("Output vertex does not have output ports within wiring diagram")
  else
    copy(subpart(f.diagram, incident(f.diagram, b, :out_port_box), :out_port_type))
  end
end

function port_value(f::WiringDiagram, port::Port)
  get_ports = port.kind == InputPort ? input_ports : output_ports
  get_ports(f, port.box)[port.port]
end

# Graph mutation.

function add_box!(f::WiringDiagram, box::AbstractBox)
  b = add_part!(f.diagram, :Box)
  in_ports = add_parts!(f.diagram, :InPort, length(input_ports(box)))
  set_subpart!(f.diagram, in_ports, :in_port_box, b)
  set_subpart!(f.diagram, in_ports, :in_port_type, input_ports(box))
  out_ports = add_parts!(f.diagram, :OutPort, length(output_ports(box)))
  set_subpart!(f.diagram, out_ports, :out_port_box, b)
  set_subpart!(f.diagram, out_ports, :out_port_type, output_ports(box))

  set_subpart!(f.diagram, b, :name, box.value)
  # Set port type??
  return b
end 

function add_boxes!(f::WiringDiagram, boxes)
  map(box -> add_box!(f,box), boxes)
end

function rem_box!(f::WiringDiagram, b::Int)
  @assert b ∉ outer_ids(f)
  rem_part!(f.diagram, :Box, b)
end

function rem_boxes!(f::WiringDiagram, bs)
  @assert all(b ∉ outer_ids(f) for b in bs)
  rem_parts!(f.diagram, :Box, bs)
end


function add_pass_wire!(f::WiringDiagram, wire::Wire)
  w = add_part!(f.diagram, :PassWire)
  set_subpart!(f.diagram, w, :pass_wire_value, wire.value)
  set_subpart!(f.diagram, w, :pass_src, wire.source.port)
  set_subpart!(f.diagram, w, :pass_tgt, wire.target.port)
  return w
end

function add_in_wire!(f::WiringDiagram, wire::Wire)
  w = add_part!(f.diagram, :InWire)
  set_subpart!(f.diagram, w, :in_wire_value, wire.value)
  set_subpart!(f.diagram, w, :in_src, wire.source.port)
  set_subpart!(f.diagram, w, :in_tgt, in_port_id(f, wire.target))
  return w
end

function add_out_wire!(f::WiringDiagram, wire::Wire)
  w = add_part!(f.diagram, :OutWire)
  set_subpart!(f.diagram, w, :out_wire_value, wire.value)
  set_subpart!(f.diagram, w, :out_src, out_port_id(f, wire.source))
  set_subpart!(f.diagram, w, :out_tgt, wire.target.port)
  return w
end


function add_internal_wire!(f::WiringDiagram, wire::Wire)
  w = add_part!(f.diagram, :Wire)
  set_subpart!(f.diagram, w, :wire_value, wire.value)
  set_subpart!(f.diagram, w, :src, out_port_id(f, wire.source))
  set_subpart!(f.diagram, w, :tgt, in_port_id(f, wire.target))
  return w
end


function add_wire!(f::WiringDiagram, wire::Wire)
  validate_ports(port_value(f, wire.source), port_value(f, wire.target))
  if wire.source.box == input_id(f) && wire.target.box == output_id(f)
    add_pass_wire!(f, wire)
  elseif wire.source.box == input_id(f)
    add_in_wire!(f,wire)
  elseif wire.target.box == output_id(f)
    add_out_wire!(f,wire)
  else
    add_internal_wire!(f, wire)
  end
end

add_wire!(f::WiringDiagram, pair::Pair) = add_wire!(f, Wire(pair))

function add_wires!(f::WiringDiagram, wires)
  for wire in wires
    add_wire!(f, wire)
  end
end

function rem_pass_wire!(f::WiringDiagram, wire::Wire)
  for w in parts(f.diagram, :PassWire)
    subpart(f.diagram, w, :pass_wire_value) == wire.value && 
          return rem_part!(f.diagram, :PassWire, w)
  end
end

function rem_in_wire!(f::WiringDiagram, wire::Wire)
  for w in incident(f.diagram, in_port_id(f, wire.target), :in_tgt)
    subpart(f.diagram, w, :in_wire_value) == wire.value && 
          return rem_part!(f.diagram, :InWire, w)
  end
end

function rem_out_wire!(f::WiringDiagram, wire::Wire)
  for w in incident(f.diagram, out_port_id(f, wire.source), :out_src)
    subpart(f.diagram, w, :out_wire_value) == wire.value && 
          return rem_part!(f.diagram, :OutWire, w)
  end
end

function rem_internal_wire!(f::WiringDiagram, wire::Wire)
  for w in incident(f.diagram, out_port_id(f, wire.source), :src)
    subpart(f.diagram, w, :tgt) == in_port_id(f, wire.target) &&
          subpart(f.diagram, w, :wire_value) == wire.value &&
          return rem_part!(f.diagram, :Wire, w)
  end
end

function rem_wire!(f::WiringDiagram, wire::Wire)
  if wire.source.box == input_id(f) && wire.target.box == output_id(f)
    rem_pass_wire!(f, wire)
  elseif wire.source.box == input_id(f)
    rem_in_wire!(f,wire)
  elseif wire.target.box == output_id(f)
    rem_out_wire!(f,wire)
  else
    rem_internal_wire!(f, wire)
  end
  error("Wire $wire does not exist, so cannot be removed")
end
rem_wire!(f::WiringDiagram, pair::Pair) = rem_wire!(f, Wire(pair))

function rem_wires!(f::WiringDiagram, wires)
  for wire in wires
    rem_wire!(f, wire)
  end
end

function rem_wires!(f::WiringDiagram, src::Int, tgt::Int)
  if src == input_id(f) && tgt == output_id(f)
    rem_parts!(f.diagram, :PassWire, parts(f.diagram, :PassWire))
  elseif src == input_id(f) 
    rem_parts!(f.diagram, :InWire, incident(f.diagram, tgt, :in_port_box∘:in_tgt))
  elseif tgt == output_id(f)
    rem_parts!(f.diagram, :OutWire, incident(f.diagram, src, :out_port_box∘:out_src))
  else
    rem_parts!(f.diagram, :Wire, incident(f.diagram, src, :out_port_box∘:src) ∩ 
                                 incident(f.diagram, tgt, :in_port_box∘:tgt) ) #fast way for sorted intersection?
  end
end

""" Check compatibility of source and target ports.

The default implementation is a no-op.
"""
function validate_ports(source_port, target_port) end

# Graph properties.

""" Retrieve the graph underlying the wiring diagram.

The graph is an instance of `Catlab.Graphs.AbstractGraph`. Do not mutate it! All
mutations should use the wiring diagrams API: `add_box!`, `rem_box!`, and so on.
"""
graph(diagram::WiringDiagram) = diagram.graph

# Convenience methods delegated to underlying graph.
all_neighbors(d::WiringDiagram, v::Int) = all_neighbors(graph(d), v)
neighbors(d::WiringDiagram, v::Int) = neighbors(graph(d), v)
outneighbors(d::WiringDiagram, v::Int) = outneighbors(graph(d), v)
inneighbors(d::WiringDiagram, v::Int) = inneighbors(graph(d), v)

""" Get all wires coming into or out of the box.
"""
function wires(d::WiringDiagram, v::Int)
  g = graph(d)
  [ Wire(subpart(g, e, :wire), src(g, e), tgt(g, e))
    for e in unique!(sort!([incident(g, v, :src); incident(g, v, :tgt)])) ]
end

""" Get all wires coming into the box.
"""
function in_wires(d::WiringDiagram, v::Int)
  g = graph(d)
  [ Wire(subpart(g, e, :wire), src(g, e), v) for e in incident(g, v, :tgt) ]
end

""" Get all wires coming into the port.
"""
function in_wires(d::WiringDiagram, port::Port)
  filter(wire -> wire.target == port, in_wires(d, port.box))
end
function in_wires(d::WiringDiagram, v::Int, port::Int)
  in_wires(d, Port(v, InputPort, port))
end

""" Get all wires coming out of the box.
"""
function out_wires(d::WiringDiagram, v::Int)
  g = graph(d)
  [ Wire(subpart(g, e, :wire), v, tgt(g, e)) for e in incident(g, v, :src) ]
end

""" Get all wires coming out of the port.
"""
function out_wires(d::WiringDiagram, port::Port)
  filter(wire -> wire.source == port, out_wires(d, port.box))
end
function out_wires(d::WiringDiagram, v::Int, port::Int)
  out_wires(d, Port(v, OutputPort, port))
end

# Other constructors
#-------------------

""" Wiring diagram with a single box connected to the outer ports.
"""
function singleton_diagram(T::Type, box::AbstractBox)
  inputs, outputs = input_ports(box), output_ports(box)
  d = WiringDiagram{T}(inputs, outputs)
  v = add_box!(d, box)
  add_wires!(d, ((input_id(d),i) => (v,i) for i in eachindex(inputs)))
  add_wires!(d, ((v,i) => (output_id(d),i) for i in eachindex(outputs)))
  return d
end
singleton_diagram(box::AbstractBox) = singleton_diagram(Any, box)

""" The wiring diagram induced by a subset of its boxes.

See also `encapsulated_subdiagram`.
"""
function induced_subdiagram(d::WiringDiagram{T}, vs::Vector{Int}) where T
  sub = WiringDiagram{T}(input_ports(d), output_ports(d))
  vmap = Dict(input_id(d) => input_id(sub), output_id(d) => output_id(sub))
  for v in vs
    vmap[v] = add_box!(sub, box(d, v))
  end
  for wire in wires(d)
    src, tgt = wire.source, wire.target
    if haskey(vmap, src.box) && haskey(vmap, tgt.box)
      add_wire!(sub,
        Wire(set_box(src, vmap[src.box]), set_box(tgt, vmap[tgt.box])))
    end
  end
  return sub
end

# Operadic interface
####################

""" Operadic composition of wiring diagrams.

This generic function has two different signatures, corresponding to the "full"
and "partial" notions of operadic composition (Yau, 2018, *Operads of Wiring
Diagrams*, Definitions 2.3 and 2.10).

This operation is a simple wrapper around [`substitute`](@ref).
"""
function ocompose(f::WiringDiagram, gs::Vector{<:WiringDiagram})
  @assert length(gs) == nboxes(f)
  substitute(f, box_ids(f), gs)
end
function ocompose(f::WiringDiagram, i::Int, g::WiringDiagram)
  @assert 1 <= i <= nboxes(f)
  substitute(f, box_ids(f)[i], g)
end

# Substitution
##############

""" Substitute wiring diagrams for boxes.

Performs one or more substitutions. When performing multiple substitutions, the
substitutions are simultaneous.

This operation implements the operadic composition of wiring diagrams, see also
[`ocompose`](@ref).
"""
function substitute(d::WiringDiagram; kw...)
  substitute(d, filter(v -> box(d,v) isa WiringDiagram, box_ids(d)); kw...)
end
function substitute(d::WiringDiagram, v::Int; kw...)
  substitute(d, v, box(d,v)::WiringDiagram; kw...)
end
function substitute(d::WiringDiagram, vs::AbstractVector{Int}; kw...)
  substitute(d, vs, WiringDiagram[ box(d,v) for v in vs ]; kw...)
end
function substitute(d::WiringDiagram, v::Int, sub::WiringDiagram; kw...)
  substitute(d, [v], [sub]; kw...)
end

function substitute(d::WiringDiagram{T}, vs::AbstractVector{Int},
                    subs::Vector{<:WiringDiagram};
                    merge_wire_values=default_merge_wire_values) where T
  # In outline, the algorithm is:
  #
  # 1. Create an empty wiring diagram.
  # 2. Add *all* boxes of original diagram and the diagrams to be substituted
  #    (in the appropriate order).
  # 3. Add *all* wires of original diagram and the diagrams to be substituted.
  # 4. Remove the boxes that were substituted (hence also removing extraneous
  #    wires from step 3).
  #
  # This may seem convoluted, but it is the simplest way I know to handle the
  # problem of *instantaneous wires*. Some authors ban instantaneous wires, but
  # we need them to represent identities, braidings, etc.
  @assert length(vs) == length(subs)
  result = WiringDiagram{T}(d.value, input_ports(d), output_ports(d))
  
  # Add boxes by interleaving, in the correct order, the non-substituted boxes
  # of the original diagram and the internal boxes of the substituted diagrams.
  # At the very end, add the substituted boxes too.
  vmap = Dict(input_id(d) => input_id(result), output_id(d) => output_id(result))
  sub_maps = Dict(zip(vs, ((sub, Dict{Int,Int}()) for sub in subs)))
  for v in box_ids(d)
    if haskey(sub_maps, v)
      sub, sub_map = sub_maps[v]
      for u in box_ids(sub)
        sub_map[u] = add_box!(result, box(sub, u))
      end
    else
      vmap[v] = add_box!(result, box(d, v))
    end
  end
  for v in vs
    vmap[v] = add_box!(result, box(d, v))
  end
  
  # Add the wires of the original diagram, then add the internal wires of the
  # substituted diagrams.
  for wire in wires(d)
    add_wire!(result, Wire(wire.value,
      set_box(wire.source, vmap[wire.source.box]),
      set_box(wire.target, vmap[wire.target.box])))
  end
  for v in vs
    substitute_wires!(result, vmap[v], sub_maps[v]...;
      merge_wire_values=merge_wire_values)
  end
  
  # Finally, remove the substituted boxes. Because they were added last, this
  # will not change the IDs of the other boxes.
  rem_boxes!(result, (vmap[v] for v in vs))
  result
end

""" Substitute wires of sub-diagram into containing wiring diagram.
"""
function substitute_wires!(d::WiringDiagram, v::Int,
                           sub::WiringDiagram, sub_map::Dict{Int,Int};
                           merge_wire_values=default_merge_wire_values)
  for wire in wires(sub)
    src = get(sub_map, wire.source.box, 0)
    tgt = get(sub_map, wire.target.box, 0)
    # Special case: wire from input port to output port.
    if wire.source.box == input_id(sub) && wire.target.box == output_id(sub)
      for in_wire in in_wires(d, v, wire.source.port)
        for out_wire in out_wires(d, v, wire.target.port)
          add_wire!(d, Wire(
            merge_wire_values(in_wire.value, wire.value, out_wire.value),
            in_wire.source, out_wire.target))
        end
      end
    # Special case: wire from input port to internal box.
    elseif wire.source.box == input_id(sub)
      for in_wire in in_wires(d, v, wire.source.port)
        add_wire!(d, Wire(
          merge_wire_values(in_wire.value, wire.value, nothing),
          in_wire.source, set_box(wire.target, tgt)))
      end
    # Special case: wire from internal box to output port.
    elseif wire.target.box == output_id(sub)
      for out_wire in out_wires(d, v, wire.target.port)
        add_wire!(d, Wire(
          merge_wire_values(nothing, wire.value, out_wire.value),
          set_box(wire.source, src), out_wire.target))
      end
    # Default case: wire between two internal boxes.
    else
      add_wire!(d, Wire(
        merge_wire_values(nothing, wire.value, nothing),
        set_box(wire.source, src), set_box(wire.target, tgt)))
    end
  end
end

default_merge_wire_values(::Any, middle::Any, ::Any) = middle

# Encapsulation
###############

""" Encapsulate multiple boxes within a single sub-diagram.

This operation is a (one-sided) inverse to subsitution, see
[`substitute`](@ref).
"""
function encapsulate(d::WiringDiagram, vs::Vector{Int}; value=nothing, kw...)
  encapsulate(d, [vs]; values=[value], kw...)
end

function encapsulate(d::WiringDiagram{T}, vss::Vector{Vector{Int}};
    discard_boxes::Bool=false, make_box=Box, values=nothing) where T
  if isempty(vss); return d end
  if any(isempty(vs) for vs in vss)
    error("Cannot encapsulate an empty set of boxes")
  end
  if !allunique(reduce(vcat, vss))
    error("Cannot encapsulate overlapping sets of boxes")
  end
  if isnothing(values)
    values = repeat([nothing], length(vss))
  end
  result = WiringDiagram{T}(d.value, input_ports(d), output_ports(d))
  
  # Add boxes, both encapsulated and non-encapsulated, to new wiring diagram.
  encapsulated_representatives = Dict(
    minimum(vs) => (vs, value) for (vs, value) in zip(vss, values))
  all_encapsulated = Set(v for vs in vss for v in vs)
  vmap = Dict(input_id(d) => input_id(result), output_id(d) => output_id(result))
  port_map = Dict{Port,Port}()
  for v in box_ids(d)
    if haskey(encapsulated_representatives, v)
      vs, value = encapsulated_representatives[v]
      sub, sub_map = encapsulated_subdiagram(d, vs;
        discard_boxes=discard_boxes, make_box=make_box, value=value)
      subv = add_box!(result, sub)
      merge!(port_map, Dict(port => Port(data, subv)
                            for (port, data) in sub_map))
    elseif v ∉ all_encapsulated
      vmap[v] = add_box!(result, box(d, v))
    end
  end
  
  # Add wires to new wiring diagram.
  for wire in wires(d)
    src, tgt = wire.source, wire.target
    new_src = if haskey(vmap, src.box); set_box(src, vmap[src.box])
      elseif haskey(port_map, src); port_map[src]
      else; continue end
    new_tgt = if haskey(vmap, tgt.box); set_box(tgt, vmap[tgt.box])
      elseif haskey(port_map, tgt); port_map[tgt]
      else; continue end
    add_wire!(result, Wire(new_src, new_tgt))
  end
  result
end

""" Create an encapsulating box for a set of boxes in a wiring diagram.

To a first approximation, the union of input ports of the given boxes will
become the inputs ports of the encapsulating box and likewise for the output
ports. However, when copies or merges occur, as in a cartesian or cocartesian
category, a simplification procedure may reduce the number of ports on the
encapsulating box.

Specifically:

1. Each input port of an encapsulated box will have at most one incoming wire
from the encapsulating outer box, and each output port of an encapsulated box
will have at most one outgoing wire to the encapsulating outer box.

2. A set of ports connected to the same outside (non-encapsulated) ports will be
simplified into a single port of the encapsulating box.

See also `induced_subdiagram`.
"""
function encapsulated_subdiagram(d::WiringDiagram{T}, vs::Vector{Int};
    discard_boxes::Bool=false, make_box=Box, value=nothing) where T
  # Add encapsulated box to new wiring diagram.
  inputs, outputs = [], []
  result = discard_boxes ? nothing : WiringDiagram{T}(value, inputs, outputs)
  vmap = if discard_boxes
    Dict(v => nothing for v in vs)
  else
    Dict(v => add_box!(result, box(d, v)) for v in vs)
  end
  
  # Process wires into, or out of, encapsulated boxes.
  port_map = Dict{Port,PortData}()
  inner_port_map = Dict{Tuple{Vector{Port},Any},Int}()
  for v in vs
    # Add input ports to encapsulating box and corresponding wire.
    for (port, value) in enumerate(input_ports(d, v))
      tgt = Port(v, InputPort, port)
      srcs = sort!([ wire.source for wire in in_wires(d, tgt)
                     if !haskey(vmap, wire.source.box) ])
      if isempty(srcs) continue end
      src = get!(inner_port_map, (srcs, value)) do
        push!(inputs, value)
        port_data = port_map[tgt] = PortData(InputPort, length(inputs))
        port_data.port
      end
      if discard_boxes; continue end
      add_wire!(result,
        Wire(Port(input_id(result), OutputPort, src), set_box(tgt, vmap[v])))
    end
    
    # Add output ports to encapsulating box and corresponding wire.
    for (port, value) in enumerate(output_ports(d, v))
      src = Port(v, OutputPort, port)
      tgts = sort([ wire.target for wire in out_wires(d, src)
                    if !haskey(vmap, wire.target.box) ])
      if isempty(tgts) continue end
      tgt = get!(inner_port_map, (tgts, value)) do
        push!(outputs, value)
        port_data = port_map[src] = PortData(OutputPort, length(outputs))
        port_data.port
      end
      if discard_boxes; continue end
      add_wire!(result,
        Wire(set_box(src, vmap[v]), Port(output_id(result), InputPort, tgt)))
    end
    
    # Add wires between two encapsulated boxes.
    if discard_boxes; continue end
    for wire in out_wires(d, v)
      src, tgt = wire.source, wire.target
      if haskey(vmap, src.box) && haskey(vmap, tgt.box) # Clause #1 always true.
        add_wire!(result,
          Wire(set_box(src, vmap[src.box]), set_box(tgt, vmap[tgt.box])))
      end
    end
  end
  
  # Yield input and output port lists with the tightest possible types.
  inputs, outputs = [ x for x in inputs ], [ x for x in outputs ]
  if discard_boxes
    result = make_box(value, inputs, outputs)
  else
    result.input_ports, result.output_ports = inputs, outputs
  end
  (result, port_map)
end

end
