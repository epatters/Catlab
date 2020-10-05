export AbstractFunctor, AbstractMonoidalFunctor

abstract type AbstractFunctor end

function dom(F::AbstractFunctor)::Category end
function codom(F::AbstractFunctor)::Category end

function (F::AbstractFunctor)(f::HomExpr{:compose})
  compose(map(x->F(x), f.args))
end

abstract type AbstractMonoidalFunctor <: AbstractFunctor end

function dom(F::AbstractMonoidalFunctor)::MonoidalCategory end
function codom(F::AbstractMonoidalFunctor)::MonoidalCategory end

function (F::AbstractMonoidalFunctor)(f::ObExpr{:otimes})
  otimes(map(x->F(x), f.args))
end

function (F::AbstractMonoidalFunctor)(f::HomExpr{:otimes})
  otimes(map(x->F(x), f.args))
end
