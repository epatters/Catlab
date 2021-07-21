""" Graphviz support for Catlab's graph types.
"""
module GraphvizGraphs
export parse_graphviz, to_graphviz

using StaticArrays: StaticVector, SVector

using ...Present, ...Theories
using ...Graphs, ...CategoricalAlgebra.Subobjects
import ..Graphviz

# Property graphs
#################

""" Parse Graphviz output in JSON format.

Returns a property graph with graph layout and other metadata. Each node has a
position and size.

All units are in points. Note that Graphviz has 72 points per inch.
"""
function parse_graphviz(doc::AbstractDict)::AbstractPropertyGraph
  graph = doc["directed"] ? PropertyGraph{Any}() : SymmetricPropertyGraph{Any}()
  nsubgraphs = doc["_subgraph_cnt"] # Subgraphs are ignored.

  # Graph-level layout: bounds and padding.
  # It seems, but is not documented, that the first two numbers in the Graphviz
  # bounding box are always zero.
  set_gprops!(graph,
    bounds = SVector{2}(parse_vector(doc["bb"])[3:4]),
    pad = 72*parse_point(get(doc, "pad", "0,0")),
    rankdir = get(doc, "rankdir", "TB"),
  )

  # Add vertex for each Graphviz node.
  node_keys = ("id", "name", "comment", "label", "shape", "style")
  for node in doc["objects"][nsubgraphs+1:end]
    props = Dict{Symbol,Any}(
      Symbol(k) => node[k] for k in node_keys if haskey(node, k))
    props[:position] = parse_point(node["pos"])
    props[:size] = 72*SVector(parse(Float64, node["width"]),
                              parse(Float64, node["height"]))
    add_vertex!(graph, props)
  end

  # Add edge for each Graphviz edge.
  edge_keys = ("id", "comment", "label", "xlabel", "headlabel", "taillabel",
               "headport", "tailport")
  for edge in doc["edges"]
    if get(edge, "style", nothing) == "invis"
      # Omit invisible edges, which are used to tweak the layout in Graphviz.
      continue
    end
    props = Dict{Symbol,Any}(
      Symbol(k) => edge[k] for k in edge_keys if haskey(edge, k))
    props[:spline] = parse_spline(edge["pos"])
    src = edge["tail"] - nsubgraphs + 1
    tgt = edge["head"] - nsubgraphs + 1
    add_edge!(graph, src, tgt, props)
  end

  graph
end

""" Parse an array of floats in Graphviz's comma-separated format.
"""
parse_vector(s::AbstractString) = [ parse(Float64, x) for x in split(s, ",") ]

""" Parse Graphviz point.

http://www.graphviz.org/doc/info/attrs.html#k:point
"""
parse_point(s::AbstractString) = SVector{2}(parse_vector(s))

""" Parse Graphviz spline.

In Graphviz, a "spline" is a cubic B-spline of overlapping cubic Bezier curves.
It consists of 3n+1 points, where n is the number of Bezier curves.

http://www.graphviz.org/doc/info/attrs.html#k:splineType
https://web.archive.org/web/20170418034924/http://www.graphviz.org/content/how-convert-b-spline-bezier
"""
function parse_spline(spline::AbstractString)
  points = StaticVector{2,Float64}[]
  start, stop = nothing, nothing
  for s in split(spline, " ")
    if startswith(s, "s,"); start = parse_point(s[3:end])
    elseif startswith(s, "e,"); stop = parse_point(s[3:end])
    else push!(points, parse_point(s)) end
  end
  # Prefer explicit start or end points to the spline start and end points.
  # Thus, endpoints may pass into the node shape but should not fall short.
  if !isnothing(start); points[0] = start end
  if !isnothing(stop); points[end] = stop end
  points
end

""" Convert a property graph to a Graphviz graph.

This method is usually more convenient than direct AST manipulation for creating
simple Graphviz graphs. For more advanced features, like nested subgraphs, you
must use the Graphviz AST.
"""
function to_graphviz(g::AbstractPropertyGraph)::Graphviz.Graph
  gv_name(v::Int) = "n$v"
  gv_path(e::Int) = [gv_name(src(g,e)), gv_name(tgt(g,e))]

  # Add Graphviz node for each vertex in property graph.
  stmts = Graphviz.Statement[]
  for v in vertices(g)
    push!(stmts, Graphviz.Node(gv_name(v), vprops(g, v)))
  end

  # Add Graphviz edge for each edge in property graph.
  is_directed = !(g isa SymmetricPropertyGraph)
  for e in edges(g)
    # In undirected case, only include one edge from each pair.
    if is_directed || (e <= inv(g,e))
      push!(stmts, Graphviz.Edge(gv_path(e), eprops(g, e)))
    end
  end

  attrs = gprops(g)
  Graphviz.Graph(
    name = get(attrs, :name, "G"),
    directed = is_directed,
    prog = get(attrs, :prog, is_directed ? "dot" : "neato"),
    stmts = stmts,
    graph_attrs = Graphviz.as_attributes(get(attrs, :graph, Dict())),
    node_attrs = Graphviz.as_attributes(get(attrs, :node, Dict())),
    edge_attrs = Graphviz.as_attributes(get(attrs, :edge, Dict())),
  )
end

# Graphs
########

# FIXME: Should be an abstract type after StructACSets refactor.
const IsGraph = Union{AbstractGraph, AbstractSymmetricGraph,
                      AbstractReflexiveGraph, AbstractSymmetricReflexiveGraph}

""" Convert a graph to a Graphviz graph.

A simple default style is applied. For more control over the visual appearance,
first convert the graph to a property graph, define the Graphviz attributes as
needed, and then convert to a Graphviz graph.
"""
function to_graphviz(g::IsGraph; kw...)
  to_graphviz(to_graphviz_property_graph(g; kw...))
end

function to_graphviz_property_graph(g::AbstractGraph;
    prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  node_labeler(v) = Dict(:label => node_labels ? string(v) : "")
  edge_labeler(e) = if edge_labels
    Dict(:label => string(e))
  else
    Dict{Symbol,String}()
  end
  PropertyGraph{Any}(g, node_labeler, edge_labeler;
    prog = prog,
    graph = merge!(Dict(:rankdir => "LR"), graph_attrs),
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(Dict(:arrowsize => "0.5"), edge_attrs),
  )
end

default_node_attrs(show_labels::Bool) = Dict(
  :shape => show_labels ? "circle" : "point",
  :width => "0.05",
  :height => "0.05",
  :margin => "0",
)

# Symmetric graphs
##################

function to_graphviz_property_graph(g::AbstractSymmetricGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  node_labeler(v) = Dict(:label => node_labels ? string(v) : "")
  edge_labeler(e) = if edge_labels
    e′ = inv(g,e)
    Dict(:label => "($(min(e,e′)),$(max(e,e′)))")
  else
    Dict{Symbol,String}()
  end
  SymmetricPropertyGraph{Any}(g, node_labeler, edge_labeler;
    prog = prog,
    graph = graph_attrs,
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(Dict(:len => "0.5"), edge_attrs),
  )
end

# Reflexive graphs
##################

function to_graphviz_property_graph(g::AbstractReflexiveGraph;
    prog::AbstractString="dot", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false,
    show_reflexive::Bool=false)
  pg = PropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(Dict(:arrowsize => "0.5"), edge_attrs),
  )
  for v in vertices(g)
    add_vertex!(pg, label=node_labels ? string(v) : "")
  end
  reflexive_edges = Set(refl(g))
  for e in edges(g)
    is_reflexive = e ∈ reflexive_edges
    if show_reflexive || !is_reflexive
      e′ = add_edge!(pg, src(g,e), tgt(g,e))
      if is_reflexive; set_eprop!(pg, e′, :style, "dashed") end
      if edge_labels; set_eprop!(pg, e′, :label, string(e)) end
    end
  end
  pg
end

# Symmetric reflexive graphs
############################

function to_graphviz_property_graph(g::AbstractSymmetricReflexiveGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false,
    show_reflexive::Bool=false)
  pg = SymmetricPropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(Dict(:len => "0.5"), edge_attrs),
  )
  for v in vertices(g)
    add_vertex!(pg, label=node_labels ? string(v) : "")
  end
  reflexive_edges = Set(refl(g))
  for e in edges(g)
    is_reflexive = e ∈ reflexive_edges
    if is_reflexive && show_reflexive
      e′ = add_edge!(pg, src(g,e), tgt(g,e), style="dashed")
      if edge_labels; set_eprop!(pg, e′, :label, string(e)) end
    elseif !is_reflexive && e <= inv(g,e)
      e′ = add_edge!(pg, src(g,e), tgt(g,e))
      if edge_labels; set_eprop!(pg, e′, :label, "($e,$(inv(g,e)))") end
    end
  end
  pg
end

# Half-edge graphs
##################

to_graphviz(g::AbstractHalfEdgeGraph; kw...) =
  to_graphviz(to_graphviz_property_graph(g; kw...))

function to_graphviz_property_graph(g::AbstractHalfEdgeGraph;
    prog::AbstractString="neato", graph_attrs::AbstractDict=Dict(),
    node_attrs::AbstractDict=Dict(), edge_attrs::AbstractDict=Dict(),
    node_labels::Bool=false, edge_labels::Bool=false)
  pg = SymmetricPropertyGraph{Any}(; prog = prog,
    graph = graph_attrs,
    node = merge!(default_node_attrs(node_labels), node_attrs),
    edge = merge!(Dict(:len => "0.5"), edge_attrs),
  )
  for v in vertices(g)
    add_vertex!(pg, label=node_labels ? string(v) : "")
  end
  for e in half_edges(g)
    if e == inv(g,e)
      # Dangling half-edge: add an invisible vertex.
      v = add_vertex!(pg, style="invis", shape="none", label="")
      e′ = add_edge!(pg, vertex(g,e), v)
      if edge_labels; set_eprop!(pg, e′, :label, string(e)) end
    elseif e < inv(g,e)
      # Pair of distict half-edges: add a standard edge.
      e′ = add_edge!(pg, vertex(g,e), vertex(g,inv(g,e)))
      if edge_labels; set_eprop!(pg, e′, :label, "($e,$(inv(g,e)))") end
    end
  end
  pg
end

# Subgraphs
###########

to_graphviz(subgraph::Subobject{<:IsGraph}; kw...) =
  to_graphviz(to_graphviz_property_graph(subgraph; kw...))

function to_graphviz_property_graph(
    subgraph::Subobject{<:Union{AbstractGraph,AbstractSymmetricGraph}};
    subgraph_node_attrs::AbstractDict=Dict(:color => "cornflowerblue"),
    subgraph_edge_attrs::AbstractDict=Dict(:color => "cornflowerblue"), kw...)
  pg = to_graphviz_property_graph(ob(subgraph); kw...)
  f = hom(subgraph)
  for v in vertices(dom(f))
    set_vprops!(pg, f[:V](v), subgraph_node_attrs)
  end
  for e in edges(dom(f))
    set_eprops!(pg, f[:E](e), subgraph_edge_attrs)
  end
  pg
end

# Schemas
#########

to_graphviz(pres::Presentation{Schema}) =
  to_graphviz(to_graphviz_property_graph(pres))

function to_graphviz_property_graph(pres::Presentation{Schema})
  obs,homs,datas,attrs = generators.(Ref(pres), [:Ob,:Hom,:Data,:Attr])
  g = PropertyGraph{Any}()

  add_vertices!(g,length(obs))
  for (i,ob) in enumerate(obs)
    set_vprop!(g,i,:label,string(nameof(ob)))
    set_vprop!(g,i,:shape,"plain")
    set_vprop!(g,i,:margin,"2")
  end

  add_vertices!(g,length(datas))
  for (i,data) in enumerate(datas)
    set_vprop!(g,i+length(obs),:label,string(nameof(data)))
  end

  add_edges!(g,
             generator_index.(Ref(pres), nameof.(dom.(homs))),
             generator_index.(Ref(pres), nameof.(codom.(homs))))
  for (i,hom) in enumerate(homs)
    set_eprop!(g,i,:label,string(nameof(hom)))
    set_eprop!(g,i,:len,"2")
  end
  
  add_edges!(g,
             generator_index.(Ref(pres), nameof.(dom.(attrs))),
             length(obs) .+ generator_index.(Ref(pres), nameof.(codom.(attrs))))
  for (i,attr) in enumerate(attrs)
    set_eprop!(g,i+length(homs),:label,string(nameof(attr)))
    set_eprop!(g,i+length(homs),:len,"2")
  end

  set_gprop!(g,:graph,Dict(:rankdir => "LR"))
  set_gprop!(g,:prog,"neato")

  g
end

end
