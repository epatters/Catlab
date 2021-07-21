module TestGraphvizWiringDiagrams

using Test
import JSON

using Catlab.Theories, Catlab.WiringDiagrams, Catlab.Graphics,
      Catlab.CategoricalAlgebra
using Catlab.Programs: @relation
import Catlab.Graphics: Graphviz
using Catlab.Graphics.WiringDiagramLayouts: position, normal

function stmts(graph::Graphviz.Graph, type::Type)
  [ stmt for stmt in graph.stmts if stmt isa type ]
end
function stmts(graph::Graphviz.Graph, type::Type, attr::Symbol)
  [ stmt.attrs[attr] for stmt in graph.stmts
    if stmt isa type && haskey(stmt.attrs, attr) ]
end

# Directed drawing
##################

f = singleton_diagram(Box(:f, [:A], [:B]))
g = singleton_diagram(Box(:g, [:B], [:A]))

# Simple wiring diagrams, with default settings.
graph = to_graphviz(f)
@test graph isa Graphviz.Graph && graph.directed
@test stmts(graph, Graphviz.Node, :comment) == ["f"]
@test stmts(graph, Graphviz.Edge, :comment) == ["A","B"]
@test stmts(graph, Graphviz.Edge, :label) == []
@test stmts(graph, Graphviz.Edge, :xlabel) == []
@test length(stmts(graph, Graphviz.Subgraph)) == 2

graph = to_graphviz(singleton_diagram(Box(:h, Symbol[], [:A])))
@test stmts(graph, Graphviz.Node, :comment) == ["h"]
@test length(stmts(graph, Graphviz.Subgraph)) == 1

graph = to_graphviz(singleton_diagram(Box(:h, Symbol[], Symbol[])))
@test stmts(graph, Graphviz.Node, :comment) == ["h"]
@test length(stmts(graph, Graphviz.Subgraph)) == 0

graph = to_graphviz(compose(f,g))
@test stmts(graph, Graphviz.Node, :comment) == ["f","g"]

# Layout orientation.
for orientation in instances(LayoutOrientation)
  graph = to_graphviz(compose(f,g); orientation=orientation)
  @test stmts(graph, Graphviz.Node, :comment) == ["f","g"]
end

# Junction nodes.
graph = to_graphviz(add_junctions!(compose(f, mcopy(Ports([:B])))))
@test stmts(graph, Graphviz.Node, :comment) == ["f","junction"]

# Edge labels.
graph = to_graphviz(f; labels=true)
@test stmts(graph, Graphviz.Edge, :label) == ["A","B"]
@test stmts(graph, Graphviz.Edge, :xlabel) == []

graph = to_graphviz(f; labels=true, label_attr=:xlabel)
@test stmts(graph, Graphviz.Edge, :label) == []
@test stmts(graph, Graphviz.Edge, :xlabel) == ["A","B"]

# Anchoring of outer ports.
graph = to_graphviz(otimes(f,g); anchor_outer_ports=true)
@test stmts(graph, Graphviz.Node, :comment) == ["f","g"]
graph = to_graphviz(otimes(f,g); anchor_outer_ports=false)
@test stmts(graph, Graphviz.Node, :comment) == ["f","g"]

# Undirected drawing
####################

d = singleton_diagram(UndirectedWiringDiagram, 2)
graph = to_graphviz(d)
@test stmts(graph, Graphviz.Node, :id) ==
  ["box1", "outer1", "outer2", "junction1", "junction2"]
@test length(stmts(graph, Graphviz.Edge)) == 4

graph = to_graphviz(d, implicit_junctions=true)
@test stmts(graph, Graphviz.Node, :id) == ["box1", "outer1", "outer2"]
@test length(stmts(graph, Graphviz.Edge)) == 2

d = @relation ((x,z) where (x,y,z)) -> (R(x,y); S(y,z))
graph = to_graphviz(d)
@test stmts(graph, Graphviz.Node, :id) ==
  ["box1", "box2", "outer1", "outer2", "junction1", "junction2", "junction3"]
@test length(stmts(graph, Graphviz.Edge)) == 6

graph = to_graphviz(d, implicit_junctions=true)
@test stmts(graph, Graphviz.Node, :id) == ["box1", "box2", "outer1", "outer2"]
@test length(stmts(graph, Graphviz.Edge)) == 3

# Box, port, and junction labels.
graph = to_graphviz(d, box_labels=:name, junction_labels=:variable,
                    port_labels=false)
@test filter(!isempty, stmts(graph, Graphviz.Node, :label)) == ["R", "S"]
@test stmts(graph, Graphviz.Node, :xlabel) == ["x", "y", "z"]
@test stmts(graph, Graphviz.Edge, :taillabel) == []

graph = to_graphviz(d, box_labels=true, junction_labels=true, port_labels=true)
@test filter(!isempty, stmts(graph, Graphviz.Node, :label)) == ["1", "2"]
@test stmts(graph, Graphviz.Node, :xlabel) == ["1", "2", "3"]
@test stmts(graph, Graphviz.Edge, :taillabel) == ["1","1","2","1","2","2"]

# Directed layout
#################

diagram = include(joinpath("data", "graphviz_wiring_diagram.jl"))
doc = open(JSON.parse,
  joinpath(@__DIR__, "data", "graphviz_wiring_diagram.json"), "r")
graph = parse_graphviz(doc)
layout = graphviz_layout(diagram, graph)

# Is original data preserved?
values(xs) = map(x -> x.value, xs)
@test values(input_ports(layout)) == input_ports(diagram)
@test values(output_ports(layout)) == output_ports(diagram)
@test values(values(boxes(layout))) == values(boxes(diagram))

# Basic geometry.
positions = map(position, boxes(layout))
@test positions[1][1] < positions[2][1]
@test positions[1][2] < positions[3][2]

# CPG drawing
#############

# Cycle CPG
d = @acset CPortGraph begin
  Box = 4
  Port = 4
  Wire = 4
  box = [1,2,3,4]
  src = [1,2,3,4]
  tgt = [2,3,4,1]
end

# Star CPG
d2 = @acset CPortGraph begin
  Box = 4
  Port = 6
  Wire = 3
  box = [1,1,1,2,3,4]
  src = [1,2,3]
  tgt = [4,5,6]
end

graph = to_graphviz(d)
@test stmts(graph, Graphviz.Node, :id) == ["box1", "box2", "box3", "box4"]
@test length(stmts(graph, Graphviz.Edge)) == 4

graph = to_graphviz(d2)
@test stmts(graph, Graphviz.Node, :id) == ["box1", "box2", "box3", "box4"]
@test length(stmts(graph, Graphviz.Edge)) == 3

# Box and port labels
#--------------------
graph = to_graphviz(d, port_labels=true, box_labels=true)
@test stmts(graph, Graphviz.Edge, :taillabel) == fill("1", 4)
@test stmts(graph, Graphviz.Edge, :headlabel) == fill("1", 4)
@test stmts(graph, Graphviz.Node, :label) == ["1", "2", "3" ,"4"]

graph = to_graphviz(d2, port_labels=true, box_labels=true)
@test stmts(graph, Graphviz.Edge, :taillabel) == ["1", "2", "3"]
@test stmts(graph, Graphviz.Edge, :headlabel) == ["1", "1", "1"]
@test stmts(graph, Graphviz.Node, :label) == ["1", "2", "3" ,"4"]

end
