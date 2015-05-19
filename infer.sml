structure TypeInfer :> TYPEINFER =
struct

fun dedup [] = []
  | dedup (x :: xs) =
    if List.exists (fn y => x = y) xs
    then dedup xs
    else x :: dedup xs

(* A normal (not polymorphic) type *)
structure TpOps =
struct
  datatype t = Bool | Arr | All of int
  val eq = op=

  fun arity Bool = []
    | arity Arr = [0, 0]
    | arity (All i) = [i]

  fun toString Bool = "bool"
    | toString Arr = "arr"
    | toString (All i) = "all[" ^ Int.toString i ^ "]"
end

structure Tp = Abt(structure O = TpOps; structure V = Variable)

(* Our definition of expressions in our language *)
structure ExpOps =
struct
  datatype t = True | False | App | Let | Fn | If

  val eq = op=

  fun arity True = []
    | arity False = []
    | arity App = [0, 0]
    | arity Let = [0, 1]
    | arity Fn = [1]
    | arity If = [0, 0, 0]

  fun toString True = "true"
    | toString False = "false"
    | toString App = "app"
    | toString Let = "let"
    | toString Fn = "fn"
    | toString If = "if"
end

structure Exp = Abt(structure O = ExpOps; structure V = Variable)

structure Context = RedBlackDict(structure Key = struct
                                   open Variable
                                   val eq = op=
                                 end)

type context = Tp.t Context.dict


(* Any polytype can construct a new monotype with the polymorphic
 * variables replaced by fresh weakly polymorphic variables *)
local
    open Tp
    open TpOps
in
fun mintNewMonoType e =
    case out e of
        Oper (All 0, [b]) => b
      | Oper (All i, [b]) => (
          case out b of
              Bind (_, b') => mintNewMonoType (oper (All (i - 1)) [b'])
            | _ => raise Fail "Impossible"
      )
      | _ => e
end

fun generalizeMonoType ctx ty =
    let fun notMem xs x = List.all (fn y => x <> y) xs
        val ctxVars = (List.concat
                       o List.map #2
                       o Context.toList
                       o Context.map Tp.free) ctx
        val polyVars = dedup (List.filter (notMem ctxVars) (Tp.free ty))
        val ty' = List.foldl (fn (v, t) => Tp.bind v t) ty polyVars
    in Tp.oper (TpOps.All (List.length polyVars)) [ty'] end

exception UnboundVar of Variable.t

(* Lookup a variable in a list. If we don't find the variable then we throw
 * an UnboundVar exception *)
fun lookupVar var ctx =
    case Context.find ctx var of
        NONE => raise UnboundVar var
      | SOME tp => mintNewMonoType tp


(* A big part of the type checker is the generation of
 * "constraints". These are assertions that some type is equivalent to
 * another. These are represented with just a tuple of types which is to be
 * read "The left component unifies with the right component".
 *
 * Once we solve these constrains we get a [sol] which is a list of
 * variables to the monotypes the become.
 *)
structure Sol = RedBlackDict(structure Key = struct
                               open Variable
                               val eq = op=
                             end)

type constr = Tp.t * Tp.t
type sol    = Tp.t Sol.dict

exception UnificationError of constr

(* Substitute a type for a type variable in a list of constraints *)
fun substConstrs ty var (cs : constr list) : constr list =
    map (fn (l, r) => (Tp.subst ty var l, Tp.subst ty var r)) cs

(* Given a solution and a type, apply the solution by rewriting each
 * variable with what the solution says it's equivalent to.
 *)
fun applySol sol ty =
    Sol.foldl (fn (v, ty, ty') => Tp.subst ty v ty') ty sol

fun applySolCxt sol cxt = Context.map (applySol sol) cxt


(* Given a solution, add a new member to the solution ensuring that
 * the rhs of the new part of the solution is normal with respect to the
 * rest of the solution.
 *)
fun addSol v ty sol = Sol.insert sol v (applySol sol ty)


(* Returns true if a variable occurs in the type *)
fun occursIn v ty = List.exists (fn v' => v = v') (Tp.free ty)

local
    open TpOps
    open Tp
in
fun unify ([] : constr list) : sol = Sol.empty
  | unify ((l, r) :: constrs) =
    case (out l, out r) of
        (Oper (Bool, []), Oper (Bool, [])) => unify constrs
      | (Var i, Var j) =>
        if i = j
        then unify constrs
        else addSol i (var j) (unify (substConstrs (var j) i constrs))
      | ((Var i, ty) | (ty, Var i)) =>
        if occursIn i (into ty)
        then raise UnificationError (l, r)
        else addSol i (into ty) (unify (substConstrs (into ty) i constrs))
      | (Oper (Arr, [l, r]), Oper (Arr, [l', r'])) =>
        unify ((l, l') :: (r, r') :: constrs)
      | _ => raise UnificationError (l, r)
end


fun <+> (sol1, sol2) =
    let
        val sol1' = List.foldl (fn (v, s) => Sol.remove s v)
                               sol1
                               (Sol.domain sol2)
    in
        Sol.union (Sol.map (fn ty => applySol sol1 ty) sol2)
                  sol1'
                  (fn (_, tp, _) => tp)
    end
infixr 3 <+>

local
    open ExpOps
    open Exp
    open TpOps
in
(* Generate all the constraints and solve them for a given expression *)
fun constrain ctx e =
    case out e of
        Oper (True, []) => (Tp.oper Bool [], Sol.empty)
      | Oper (False, []) => (Tp.oper Bool [], Sol.empty)
      | Var i => (lookupVar i ctx, Sol.empty)
      | Oper (Fn, [e]) =>
        let val Bind (x, body) = out e
            val argTy = Tp.var (Variable.gen "argTy")
            val (rTy, sol) = constrain (Context.insert ctx x argTy) body
        in (Tp.oper Arr [applySol sol argTy, rTy], sol) end
      | Oper (If, [i, t, e]) =>
        let val (iTy, sol1) = constrain ctx i
            val (tTy, sol2) = constrain (applySolCxt sol1 ctx) t
            val (eTy, sol3) = constrain (applySolCxt (sol1 <+> sol2) ctx) e
            val sol = sol1 <+> sol2 <+> sol3
            val sol = sol <+> unify [ (applySol sol iTy, Tp.oper Bool [])
                                    , (applySol sol tTy, applySol sol eTy)]
        in
            (tTy, sol)
        end
      | Oper (App, [l, r]) =>
        let val domTy = Tp.var (Variable.gen "domTy")
            val ranTy = Tp.var (Variable.gen "ranTy")
            val (funTy, sol1) = constrain ctx l
            val (argTy, sol2) = constrain (applySolCxt sol1 ctx) r
            val sol = sol1 <+> sol2
            val sol = sol <+>
                          unify [(applySol sol funTy,
                                  applySol sol (Tp.oper Arr [domTy, ranTy]))
                                , (applySol sol argTy, applySol sol domTy)]
        in (ranTy, sol) end

      | Oper (Let, [e, b]) =>
        let val Bind (x, body) = out b
            val (eTy, sol1) = constrain ctx e
            val ctx' = applySolCxt sol1 ctx
            val eTy' = generalizeMonoType ctx' (applySol sol1 eTy)
            val (rTy, sol2) = constrain (Context.insert ctx' x eTy') body
        in (rTy, sol1 <+> sol2) end
      | _ => raise Fail "Impossible"
end

(* Finally, infer and solve all the constraints for a type,
 * generating a final, inferred, polytype *)
fun infer e =
    let val (ty, sol) = constrain Context.empty e
    in generalizeMonoType Context.empty (applySol sol ty) end
end
