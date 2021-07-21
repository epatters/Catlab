""" Lay out and draw wiring diagrams using Graphviz.

This module requires Graphviz v2.42 or higher.
"""
module GraphvizWiringDiagrams
export to_graphviz, graphviz_layout

import JSON
using LinearAlgebra: normalize
using MLStyle: @match
using StaticArrays

import ...Theories: HomExpr
using ...WiringDiagrams, ...WiringDiagrams.WiringDiagramSerialization
using ...CategoricalAlgebra.CSets, ...Graphs, ..GraphvizGraphs
import ...CategoricalAlgebra: migrate!
import ..Graphviz
import ..GraphvizGraphs: to_graphviz
using ..WiringDiagramLayouts: BoxLayout, PortLayout, WirePoint,
  LayoutOrientation, LeftToRight, RightToLeft, TopToBottom, BottomToTop,
  is_horizontal, is_vertical, box_label, wire_label, port_sign, svector

# Default Graphviz font. Reference: http://www.graphviz.org/doc/fontfaq.txt
const default_graphviz_font = "Serif"

# Directed drawing
##################

# Default graph, node, edge, and cell attributes for directed wiring diagrams.
const default_directed_graphviz_attrs = (
  graph = Graphviz.Attributes(
    :fontname => default_graphviz_font,
  ),
  node = Graphviz.Attributes(
    :fontname => default_graphviz_font,
    :shape => "none",
    :width => "0",
    :height => "0",
    :margin => "0",
  ),
  edge = Graphviz.Attributes(
    :arrowsize => "0.5",
    :fontname => default_graphviz_font,
  ),
  cell = Graphviz.Attributes(
    :border => "1",
    :cellpadding => "4",
  )
)

struct GraphvizBox
  stmts::Vector{Graphviz.Statement} # Usually Graphviz.Node
  input_ports::Vector{Graphviz.NodeID}
  output_ports::Vector{Graphviz.NodeID}
end

""" Draw a wiring diagram using Graphviz.

The input can also be a morphism expression, in which case it is first converted
into a wiring diagram. This function requires Graphviz v2.42 or higher.

# Arguments
- `graph_name="G"`: name of Graphviz digraph
- `orientation=TopToBottom`: orientation of layout.
  One of `LeftToRight`, `RightToLeft`, `TopToBottom`, or `BottomToTop`.
- `node_labels=true`: whether to label the nodes
- `labels=false`: whether to label the edges
- `label_attr=:label`: what kind of edge label to use (if `labels` is true).
  One of `:label`, `:xlabel`, `:headlabel`, or `:taillabel`.
- `port_size="24"`: minimum size of ports on box, in points
- `junction_size="0.05"`: size of junction nodes, in inches
- `outer_ports=true`: whether to display the outer box's input and output ports.
  If disabled, no incoming or outgoing wires will be shown either!
- `anchor_outer_ports=true`: whether to enforce ordering of the outer box's
  input and output, i.e., ordering of the incoming and outgoing wires
- `graph_attrs=Dict()`: top-level graph attributes
- `node_attrs=Dict()`: top-level node attributes
- `edge_attrs=Dict()`: top-level edge attributes
- `cell_attrs=Dict()`: main cell attributes in node HTML-like label
"""
function to_graphviz(f::WiringDiagram;
    graph_name::String="G", orientation::LayoutOrientation=TopToBottom,
    node_labels::Bool=true, labels::Bool=false, label_attr::Symbol=:label,
    port_size::String="24", junction_size::String="0.05",
    outer_ports::Bool=true, anchor_outer_ports::Bool=true,
    graph_attrs::AbstractDict=Dict(), node_attrs::AbstractDict=Dict(),
    edge_attrs::AbstractDict=Dict(), cell_attrs::AbstractDict=Dict())::Graphviz.Graph
  @assert label_attr in (:label, :xlabel, :headlabel, :taillabel)

  # State variables.
  stmts = Graphviz.Statement[]
  port_map = Dict{Port,Graphviz.NodeID}()
  update_port_map! = (v::Int, kind::PortKind, node_ids) -> begin
    for (i, node_id) in enumerate(node_ids)
      port_map[Port(v,kind,i)] = node_id
    end
  end

  # Invisible nodes for incoming and outgoing wires.
  if outer_ports
    gv_box = graphviz_outer_box(f;
      anchor=anchor_outer_ports, orientation=orientation)
    append!(stmts, gv_box.stmts)
    update_port_map!(input_id(f), OutputPort, gv_box.input_ports)
    update_port_map!(output_id(f), InputPort, gv_box.output_ports)
  end

  # Visible nodes for boxes.
  default_attrs = default_directed_graphviz_attrs
  cell_attrs = merge(default_attrs.cell, Graphviz.as_attributes(cell_attrs))
  for v in box_ids(f)
    gv_box = graphviz_box(box(f,v), box_id([v]),
      orientation=orientation, labels=node_labels, port_size=port_size,
      junction_size=junction_size, cell_attrs=cell_attrs)
    append!(stmts, gv_box.stmts)
    update_port_map!(v, InputPort, gv_box.input_ports)
    update_port_map!(v, OutputPort, gv_box.output_ports)
  end

  # Edges.
  for (i, wire) in enumerate(wires(f))
    source, target = wire.source, wire.target
    if !(haskey(port_map, source) && haskey(port_map, target))
      continue
    end
    # Use the port value to label the wire. We take the source port.
    # In most wiring diagrams, the source and target ports should yield the
    # same label, but that is not guaranteed. An advantage of choosing the
    # source port over the target port is that it will carry the
    # "more specific" type when implicit conversions are allowed.
    port = port_value(f, source)
    attrs = Graphviz.Attributes(
      :id => wire_id(Int[], i),
      :comment => edge_label(port),
    )
    if labels
      attrs[label_attr] = edge_label(port)
    end
    edge = Graphviz.Edge(port_map[source], port_map[target]; attrs...)
    push!(stmts, edge)
  end

  # Graph.
  Graphviz.Digraph(graph_name, stmts; prog="dot",
    graph_attrs=merge(default_attrs.graph, Graphviz.as_attributes(graph_attrs),
      Graphviz.Attributes(
        :rankdir => rank_dir(orientation)
      )),
    node_attrs=merge(default_attrs.node, Graphviz.as_attributes(node_attrs)),
    edge_attrs=merge(default_attrs.edge, Graphviz.as_attributes(edge_attrs)))
end

function to_graphviz(f::HomExpr; kw...)::Graphviz.Graph
  to_graphviz(to_wiring_diagram(f); kw...)
end

""" Graphviz box for a generic box.
"""
function graphviz_box(box::AbstractBox, node_id;
    orientation::LayoutOrientation=TopToBottom,
    labels::Bool=true, port_size::String="0",
    cell_attrs::AbstractDict=Dict(), kw...)
  # Main node.
  nin, nout = length(input_ports(box)), length(output_ports(box))
  text_label = labels ? node_label(box.value) : ""
  html_label = box_html_label(nin, nout, text_label;
    orientation=orientation, port_size=port_size, attrs=cell_attrs)
  # Note: The `id` attribute is included in the Graphviz output but is not used
  # internally by Graphviz. It is for use by downstream applications.
  # Reference: http://www.graphviz.org/doc/info/attrs.html#d:id
  node = Graphviz.Node(node_id,
    id = node_id,
    comment = node_label(box.value),
    label = html_label,
  )

  # Input and output ports.
  graphviz_port = (kind::PortKind, port::Int) -> begin
    Graphviz.NodeID(node_id, port_name(kind, port),
                    port_anchor(kind, orientation))
  end
  inputs = [ graphviz_port(InputPort, i) for i in 1:nin ]
  outputs = [ graphviz_port(OutputPort, i) for i in 1:nout ]

  GraphvizBox([node], inputs, outputs)
end

""" Graphviz box for a junction.
"""
function graphviz_box(junction::Junction, node_id;
    junction_size::String="0", kw...)
  graphviz_junction(junction, node_id;
    comment = "junction",
    label = "",
    shape = "circle",
    style = "filled",
    fillcolor = "black",
    width = junction_size,
    height = junction_size,
  )
end

function graphviz_junction(junction::Junction, node_id; kw...)
  node = Graphviz.Node(node_id; id=node_id, kw...)
  nin, nout = length(input_ports(junction)), length(output_ports(junction))
  GraphvizBox([node],
    repeat([Graphviz.NodeID(node_id)], nin),
    repeat([Graphviz.NodeID(node_id)], nout))
end

""" Create "HTML-like" node label for a box.
"""
function box_html_label(nin::Int, nout::Int, text_label::String;
    orientation::LayoutOrientation=TopToBottom, port_size::String="0",
    attrs::AbstractDict=Dict())::Graphviz.Html
  if is_vertical(orientation)
    input_label = ports_horizontal_html_label(InputPort, nin, port_size)
    output_label = ports_horizontal_html_label(OutputPort, nout, port_size)
    Graphviz.Html("""
      <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
      <TR><TD>$(orientation == TopToBottom ? input_label : output_label)</TD></TR>
      <TR><TD $(html_attributes(attrs))>$(escape_html(text_label))</TD></TR>
      <TR><TD>$(orientation == BottomToTop ? input_label : output_label)</TD></TR>
      </TABLE>""")
  else
    input_label = ports_vertical_html_label(InputPort, nin, port_size)
    output_label = ports_vertical_html_label(OutputPort, nout, port_size)
    Graphviz.Html("""
      <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">
      <TR>
      <TD>$(orientation == LeftToRight ? input_label : output_label)</TD>
      <TD $(html_attributes(attrs))>$(escape_html(text_label))</TD>
      <TD>$(orientation == RightToLeft ? input_label : output_label)</TD>
      </TR>
      </TABLE>""")
  end
end

""" Create horizontal "HTML-like" label for the input or output ports of a box.
"""
function ports_horizontal_html_label(kind::PortKind, nports::Int,
    port_size::String="0")::Graphviz.Html
  cols = if nports > 0
    join("""<TD HEIGHT="0" WIDTH="$port_size" PORT="$(port_name(kind,i))"></TD>"""
         for i in 1:nports)
  else
    """<TD HEIGHT="0" WIDTH="$port_size"></TD>"""
  end
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0"><TR>$cols</TR></TABLE>""")
end

""" Create vertical "HTML-like" label for the input or output ports of a box.
"""
function ports_vertical_html_label(kind::PortKind, nports::Int,
    port_size::String="0")::Graphviz.Html
  rows = if nports > 0
    join("""<TR><TD HEIGHT="$port_size" WIDTH="0" PORT="$(port_name(kind,i))"></TD></TR>"""
         for i in 1:nports)
  else
    """<TR><TD HEIGHT="$port_size" WIDTH="0"></TD></TR>"""
  end
  Graphviz.Html("""
    <TABLE BORDER="0" CELLPADDING="0" CELLSPACING="0">$rows</TABLE>""")
end

""" Graphviz box for the outer box of a wiring diagram.
"""
function graphviz_outer_box(f::WiringDiagram;
    anchor::Bool=true, orientation::LayoutOrientation=TopToBottom)
  # Subgraphs containing invisible nodes.
  stmts = Graphviz.Statement[]
  ninputs, noutputs = length(input_ports(f)), length(output_ports(f))
  if ninputs > 0
    push!(stmts, graphviz_outer_ports(InputPort, ninputs;
      anchor=anchor, orientation=orientation))
  end
  if noutputs > 0
    push!(stmts, graphviz_outer_ports(OutputPort, noutputs;
      anchor=anchor, orientation=orientation))
  end

  # Input and output ports.
  inputs = map(1:ninputs) do i
    Graphviz.NodeID(port_node_name(InputPort, i),
                    port_anchor(OutputPort, orientation))
  end
  outputs = map(1:noutputs) do i
    Graphviz.NodeID(port_node_name(OutputPort, i),
                    port_anchor(InputPort, orientation))
  end

  GraphvizBox(stmts, inputs, outputs)
end

""" Create invisible nodes for the input or output ports of an outer box.
"""
function graphviz_outer_ports(kind::PortKind, nports::Int;
    anchor::Bool=true, orientation::LayoutOrientation=TopToBottom)::Graphviz.Subgraph
  @assert nports > 0
  port_width = "$(round(24/72,digits=3))" # port width in inches
  nodes = [ port_node_name(kind, i) for i in 1:nports ]
  stmts = Graphviz.Statement[
    Graphviz.Node(nodes[i], id=port_name(kind, i)) for i in 1:nports
  ]
  if anchor && length(nodes) >= 2
    push!(stmts, Graphviz.Edge(nodes))
  end
  Graphviz.Subgraph(
    stmts,
    graph_attrs=Graphviz.Attributes(
      :rank => kind == InputPort ? "source" : "sink",
      :rankdir => is_vertical(orientation) ? "LR" : "TB"
    ),
    node_attrs=Graphviz.Attributes(
      :style => "invis",
      :shape => "none",
      :label => "",
      :width => is_vertical(orientation) ? port_width : "0",
      :height => is_horizontal(orientation) ? port_width : "0",
    ),
    edge_attrs=Graphviz.Attributes(
      :style => "invis",
    ),
  )
end
port_node_name(kind::PortKind, port::Int) =
  string(kind == InputPort ? "n0in" : "n0out", port)

""" Graphviz rank direction (`rankdir`) for layout orientation.

Reference: https://www.graphviz.org/doc/info/attrs.html#k:rankdir
"""
rank_dir(orientation::LayoutOrientation) = @match orientation begin
  &TopToBottom => "TB"
  &BottomToTop => "BT"
  &LeftToRight => "LR"
  &RightToLeft => "RL"
end

""" Graphviz anchor for port.
"""
function port_anchor(kind::PortKind, orientation::LayoutOrientation)
  @match (kind, orientation) begin
    (&InputPort, &TopToBottom) => "n"
    (&OutputPort, &TopToBottom) => "s"
    (&InputPort, &BottomToTop) => "s"
    (&OutputPort, &BottomToTop) => "n"
    (&InputPort, &LeftToRight) => "w"
    (&OutputPort, &LeftToRight) => "e"
    (&InputPort, &RightToLeft) => "e"
    (&OutputPort, &RightToLeft) => "w"
  end
end

# Undirected drawing
####################

const default_undirected_graphviz_attrs = (
  graph = Graphviz.Attributes(
    :fontname => default_graphviz_font,
  ),
  node = Graphviz.Attributes(
    :fontname => default_graphviz_font,
    :shape => "ellipse",
    :margin => "0.05,0.025",
    :width => "0.5",
    :height => "0.5",
  ),
  edge = Graphviz.Attributes(
    :fontname => default_graphviz_font,
    :len => "0.5",
  )
)

""" Draw an undirected wiring diagram using Graphviz.

Creates an undirected, bipartite Graphviz graph, with the boxes and outer ports
of the diagram becoming nodes of one kind and the junctions of the diagram
becoming nodes of the second kind.

# Arguments
- `graph_name="G"`: name of Graphviz graph
- `prog="neato"`: Graphviz program, usually "neato" or "fdp"
- `box_labels=false`: if boolean, whether to label boxes with their number;
   if a symbol, name of data attribute for box label
- `port_labels=false`: whether to label ports with their number
- `junction_labels=false`: if boolean, whether to label junctions with their
  number; if a symbol, name of data attribute for junction label
- `junction_size="0.075"`: size of junction nodes, in inches
- `implicit_junctions=false`: whether to represent a junction implicity as a
  wire when it has exactly two incident ports
- `graph_attrs=Dict()`: top-level graph attributes
- `node_attrs=Dict()`: top-level node attributes
- `edge_attrs=Dict()`: top-level edge attributes
"""
function to_graphviz(d::UndirectedWiringDiagram; kw...)::Graphviz.Graph
  to_graphviz(to_graphviz_property_graph(d; kw...))
end

function to_graphviz_property_graph(d::UndirectedWiringDiagram;
    graph_name::String="G", prog::String="neato",
    box_labels::Union{Bool,Symbol}=false, port_labels::Bool=false,
    junction_labels::Union{Bool,Symbol}=false,
    junction_size::String="0.075", implicit_junctions::Bool=false,
    graph_attrs::AbstractDict=Dict(), node_attrs::AbstractDict=Dict(),
    edge_attrs::AbstractDict=Dict())::SymmetricPropertyGraph
  default_attrs = default_undirected_graphviz_attrs
  graph = SymmetricPropertyGraph{Any}(
    name = graph_name, prog = prog,
    graph = merge(default_attrs.graph, Graphviz.as_attributes(graph_attrs)),
    node = merge(default_attrs.node, Graphviz.as_attributes(node_attrs)),
    edge = merge(default_attrs.edge, Graphviz.as_attributes(edge_attrs)),
  )

  # Create nodes for boxes.
  box_vs = add_vertices!(graph, nboxes(d))
  set_vprop!(graph, box_vs, :id, [ "box$b" for b in boxes(d) ])
  labels = if box_labels isa Symbol
    node_label.(subpart(d, box_vs, box_labels))
  else
    box_labels ? string.(boxes(d)) : ""
  end
  set_vprop!(graph, box_vs, :label, labels)

  # Create nodes for outer ports.
  outer_vs = add_vertices!(graph, length(ports(d, outer=true)))
  set_vprop!(graph, outer_vs, :id, [ "outer$p" for p in ports(d, outer=true) ])
  for v in outer_vs
    set_vprops!(graph, v, style="invis", shape="none", label="",
                width="0", height="0", margin="0")
  end

  # Create nodes and edge for junctions.
  for j in junctions(d)
    # Get all ports, including outer ports, incident to junction.
    incident_ports = [
      map(ports_with_junction(d, j)) do port
        b = box(d, port)
        (b, findfirst(p -> p == port, ports(d, b)))
      end;
      map(ports_with_junction(d, j, outer=true)) do port
        (nboxes(d) + port, port)
      end
    ]

    # Case 1: Create edge for junction with exactly two incident ports.
    if implicit_junctions && length(incident_ports) == 2
      (src, src_port), (tgt, tgt_port) = incident_ports
      e, e_inv = add_edge!(graph, src, tgt)
      if port_labels
        set_eprops!(graph, e, taillabel=string(src_port),
                    headlabel=string(tgt_port))
      end
    # Case 2: Create junction node and add edge for every incident port.
    else
      jv = add_vertex!(graph, id="junction$j", comment="junction",
                       shape="circle", label="",
                       style="filled", fillcolor="black",
                       width=junction_size, height=junction_size)
      if junction_labels isa Symbol
        set_vprop!(graph, jv, :xlabel,
                   node_label(subpart(d, j, junction_labels)))
      elseif junction_labels
        set_vprop!(graph, jv, :xlabel, string(j))
      end
      for (v, port) in incident_ports
        e, e_inv = add_edge!(graph, v, jv)
        if port_labels
          set_eprop!(graph, e, :taillabel, string(port))
        end
      end
    end
  end

  return graph
end

# Graphviz labels
#################

""" Create a label for the main content of a box.
"""
node_label(box_value) = box_label(MIME("text/plain"), box_value)

""" Create a label for an edge.
"""
edge_label(port_value) = wire_label(MIME("text/plain"), port_value)

""" Encode attributes for Graphviz HTML-like labels.
"""
function html_attributes(attrs::AbstractDict)::String
  join([ "$(uppercase(string(k)))=\"$v\""
         for (k,v) in Graphviz.as_attributes(attrs) ], " ")
end

""" Escape special HTML characters: &, <, >, ", '

Adapted from [HttpCommon.jl](https://github.com/JuliaWeb/HttpCommon.jl).
"""
function escape_html(s::AbstractString)
  reduce(replace, [
    "&" => "&amp;",
    "\"" => "&quot;",
    "'" => "&#39;",
    "<" => "&lt;",
    ">" => "&gt;",
  ], init=s)
end

# Directed layout
#################

""" Lay out directed wiring diagram using Graphviz.

Note: At this time, only the positions and sizes of the boxes, and the positions
of the outer ports, are used. The positions of the box ports and the splines for
the wires are ignored.
"""
function graphviz_layout(diagram::WiringDiagram; kw...)
  graph = to_graphviz(diagram; kw...)
  doc = JSON.parse(Graphviz.run_graphviz(graph, format="json0"))
  graphviz_layout(diagram, parse_graphviz(doc))
end

function graphviz_layout(diagram::WiringDiagram, graph::PropertyGraph)
  # Graphviz uses the standard Cartesian coordinate system (with origin in
  # bottom left corner), while our layout system uses a coordinate system with
  # centered origin and positive y-axis pointing downwards.
  orientation = inverse_rank_dir(get_gprop(graph, :rankdir))
  bounds, pad = get_gprop(graph, :bounds), get_gprop(graph, :pad)
  diagram_size = bounds + 2*pad
  transform_point(p) = SVector(1,-1) .* (p - diagram_size/2)

  # Assumes vertices are in same order as created by `to_graphviz`:
  # 1. Input ports of outer box
  nin, nout = length(input_ports(diagram)), length(output_ports(diagram))
  main_dir = svector(orientation, 1.0, 0.0)
  inputs = map(enumerate(input_ports(diagram))) do (i, value)
    attrs = vprops(graph, i)
    pos = transform_point(attrs[:position])
    PortLayout(; value=value, position=pos, normal=-main_dir)
  end

  # 2. Output ports of outer box
  outputs = map(enumerate(output_ports(diagram))) do (i, value)
    attrs = vprops(graph, nin + i)
    pos = transform_point(attrs[:position])
    PortLayout(; value=value, position=pos, normal=main_dir)
  end

  # 3. Inner boxes
  # TODO: Use port positions from Graphviz layout. Obtain these from either
  # the HTML label or, more likely, an incident edge.
  layout = WiringDiagram(BoxLayout(size=diagram_size), inputs, outputs)
  node_map = Dict{Int,Int}()
  for (i, box) in enumerate(boxes(diagram))
    node = nin + nout + i
    attrs = vprops(graph, node)
    shape = Symbol(get(attrs, :shape, :ellipse))
    if shape == :none; shape = :rectangle end # XXX: Assume HTML label.
    @assert shape == :rectangle "Only the rectangle shape is implemented so far"
    pos, size = transform_point(attrs[:position]), attrs[:size]
    node_map[node] = add_box!(layout, Box(
      BoxLayout(; value=box.value, shape=shape, position=pos, size=size),
      layout_linear_ports(InputPort, input_ports(box), size, orientation),
      layout_linear_ports(OutputPort, output_ports(box), size, orientation)
    ))
  end

  # Add wires using spline points from Graphviz edge layout.
  function map_port(node::Int, portname::Union{String,Nothing})
    if node <= nin
      Port(input_id(layout), OutputPort, node)
    elseif node <= nin + nout
      Port(output_id(layout), InputPort, node - nin)
    else
      # XXX: Parsing the port names is hacky. The alternative is parsing the
      # ordered ports in the HTML node label and matching the port names.
      kind = startswith(portname, "out") ? OutputPort : InputPort
      port = parse(Int, portname[findfirst(r"[0-9]+", portname)])
      Port(node_map[node], kind, port)
    end
  end
  for edge in edges(graph)
    attrs = eprops(graph, edge)
    # Chop off start and end points to obtain intermediate points.
    points = attrs[:spline][3:end-2]
    wire_layout = map(Iterators.partition(points, 3)) do (c1, p, c2)
      WirePoint(transform_point(p),
                normalize(transform_point(c2) - transform_point(c1)))
    end
    add_wire!(layout, Wire(wire_layout,
      map_port(src(graph, edge), get(attrs, :tailport, nothing)),
      map_port(tgt(graph, edge), get(attrs, :headport, nothing))
    ))
  end
  layout
end

""" Lay out ports linearly, equispaced along a rectangular box.

FIXME: Should this be in `WiringDiagramLayouts` as an alternative layout method?
"""
function layout_linear_ports(port_kind::PortKind, port_values::Vector,
                             box_size::StaticVector{2}, orientation::LayoutOrientation)
  n = length(port_values)
  sign = port_sign(port_kind, orientation)
  normal = svector(orientation, sign, 0.0)
  map(port_values, range(-1,1,length=n+2)[2:end-1]) do value, coeff
    pos = svector(orientation, sign, coeff) .* box_size/2
    PortLayout(; value=value, position=pos, normal=normal)
  end
end

""" Layout orientation for Graphviz rank direction (`rankdir`).

Reference: https://www.graphviz.org/doc/info/attrs.html#k:rankdir
"""
inverse_rank_dir(rank_dir::String) = @match rank_dir begin
  "TB" => TopToBottom
  "BT" => BottomToTop
  "LR" => LeftToRight
  "RL" => RightToLeft
end

# CPG drawing
#############

""" Draw a circular port graph using Graphviz.

Creates a Graphviz graph. Ports are currently not respected in the image, but
the port index for each box can be displayed to provide clarification.

# Arguments
- `graph_name="G"`: name of Graphviz graph
- `prog="neato"`: Graphviz program, usually "neato" or "fdp"
- `box_labels=false`: whether to label boxes with their number
- `port_labels=false`: whether to label ports with their number
- `graph_attrs=Dict()`: top-level graph attributes
- `node_attrs=Dict()`: top-level node attributes
- `edge_attrs=Dict()`: top-level edge attributes

TODO: The lack of ports might be able to be resolved by introducing an extra
node per port which is connected to its box with an edge of length 0.
"""
function to_graphviz(cp::CPortGraph; kw...)::Graphviz.Graph
  to_graphviz(to_graphviz_property_graph(cp; kw...))
end

function to_graphviz_property_graph(cp::CPortGraph;
    graph_name::String="G", prog::String="neato",
    box_labels::Bool=false, port_labels::Bool=false,
    graph_attrs::AbstractDict=Dict(), node_attrs::AbstractDict=Dict(),
    edge_attrs::AbstractDict=Dict())
  # Generate a map from the global index of a port to the box-specific index
  port2box = Array{Tuple{Int, Int}}(undef, nparts(cp, :Port))
  for (b, p) in enumerate(incident(cp, 1:nparts(cp, :Box), :box))
    port2box[p] .= [(b, i) for i in 1:length(p)]
  end

  g′ = Graphs.Graph()
  migrate!(g′, cp, Dict(:V=>:Box, :E=>:Wire),
                   Dict(:src => [:src, :box], :tgt => [:tgt, :box]))

  node_labeler(v) = box_labels ? Dict(:id => "box$v", :label => string(v)) :
                                 Dict(:id => "box$v")
  edge_labeler(e) =
    port_labels ? Dict(:taillabel => string(port2box[cp[e, :src]][2]),
                       :headlabel => string(port2box[cp[e, :tgt]][2]),
                       :id => "edge$e") :
                  Dict(:id => "edge$e")

  default_attrs = default_undirected_graphviz_attrs
  Graphs.PropertyGraph{Any}(g′, node_labeler, edge_labeler;
    name = graph_name, prog = prog,
    node = merge(default_attrs.node, node_attrs),
    graph = merge(default_attrs.graph, Graphviz.as_attributes(graph_attrs)),
    edge = merge(default_attrs.edge, Graphviz.as_attributes(edge_attrs))
  )
end

end
