signature TYPEINFER =
sig

    structure TpOps : sig
                  datatype t = All of int | Arr | Bool
                  val eq : ''a * ''a -> bool
                  val arity : t -> int list
                  val toString : t -> string
              end

    structure Tp : ABT where type Variable.t = Variable.t
                         and type Operator.t = TpOps.t

    structure ExpOps : sig
                  datatype t = App | False | Fn | If | Let | True
                  val eq : ''a * ''a -> bool
                  val arity : t -> int list
                  val toString : t -> string
              end

    structure Exp : ABT where type Variable.t = Variable.t
                          and type Operator.t = ExpOps.t

    val infer : Exp.t -> Tp.t
end
