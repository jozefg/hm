signature TYPEINFER =
sig
    type tvar =  int
    datatype monotype = TBool
                      | TArr of monotype * monotype
                      | TVar of tvar
    datatype polytype = PolyType of int list * monotype
    datatype exp = True
                 | False
                 | Var of int
                 | App of exp * exp
                 | Let of exp * exp
                 | Fn of exp
                 | If of exp * exp * exp
    val infer : exp -> polytype
end
