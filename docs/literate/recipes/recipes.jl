using Catlab
using Catlab.Doctrines
using Catlab.Programs
using Catlab.WiringDiagrams
using Catlab.Graphics
using Catlab.Graphics.Graphviz

import Catlab.Doctrines: Ob, Hom, dom, codom, compose,
  ⋅, ∘, id, otimes, ⊗, munit, braid,
  mcopy, Δ, delete, ◊, mmerge, ∇, create, □

draw(d::WiringDiagram) = to_graphviz(d, orientation=LeftToRight, labels=true)

@present Bakery(FreeBiproductCategory) begin
  egg::Ob
  butter::Ob
  cream::Ob
  herbs::Ob
  cheese::Ob

  crust::Ob
  lemon::Ob
  sugar::Ob
  yolk::Ob
  white::Ob
  lemonfilling::Ob
  meringue::Ob
  unbakedlemonpie::Ob
  unbakedpie::Ob
  pie::Ob

  separate::Hom(egg, yolk ⊗ white)
  makefilling::Hom(lemon⊗butter⊗sugar⊗yolk, lemonfilling)
  fillcrust::Hom(crust⊗lemonfilling, unbakedlemonpie)
  makemeringue::Hom(white ⊗ sugar, meringue)
  addmeringue::Hom(unbakedlemonpie ⊗ meringue, unbakedpie)
  bake::Hom(unbakedpie, pie)
end


d = @program Bakery (c::crust, l::lemon, b::butter, s::sugar, e::egg, s′::sugar) begin
  y, w = separate(e)
  f = makefilling(l,b,s,y)
  p = fillcrust(c,f)
  m = makemeringue(w, s′)
  return addmeringue(p,m)
end
draw(d)

@present Kitchen(FreeBiproductCategory) begin
  egg::Ob
  butter::Ob
  pan::Ob
  friedeggs::Ob
  bacon::Ob
  cookedbacon::Ob
  crispybacon::Ob
  oil::Ob
  onion::Ob
  salt::Ob
  pepper::Ob
  cream::Ob
  herbs::Ob
  cheese::Ob
  eggmix::Ob
  quiche::Ob
  crust::Ob
  lemon::Ob
  sugar::Ob
  yolk::Ob
  white::Ob

  separate::Hom(egg, yolk ⊗ white)
  fry::Hom(otimes(egg, butter, pan), otimes(friedeggs, pan))
  cook::Hom(bacon, cookedbacon)
  saute::Hom(oil⊗onion, onion)
  drain::Hom(cookedbacon, crispybacon ⊗ oil)
  whisk::Hom(egg⊗yolk⊗cream⊗herbs, eggmix)
  bakequiche::Hom(eggmix⊗bacon⊗onion⊗crust, quiche)
end
d = @program Kitchen (e::egg, b::butter) begin
  p = create{pan}()
  return fry(e,b, p)
end

draw(d)

d = @program Kitchen (e::egg, y::yolk, c::cream, h::herbs, b::bacon, o::onion, cr::crust) begin
  b, ol = drain(cook(b))
  mix = whisk(e, y, c, h)
  o = saute(ol, o)
  return bakequiche(mix, b, o, cr)
end

draw(d)

# TODO define a theory that has term constructors for generic operations
# @theory CartesianCategory(Ob,Hom) => Recipes(Ob,Hom) begin
#   mixed(X::Ob,Y::Ob)::Ob
#
# end

# TODO use pushout to define the combination of cooking theories
# TODO make a recipe that requires both Bakery and Kitchen as subrecipes
