(* An example of type inference for a tiny ML-like language.
 * Our language includes
 *
 *   - Functions
 *   - Booleans
 *   - If expressions
 *   - Let abstraction
 *
 * This means the types are function types [t -> t] and booleans
 * [bool] as well as type variables for polymorphic types
 *
 * To simplify the process of representing variables, we use something
 * called DeBruijn indices (pronounced "DeBrown"). With these a
 * variable is a number that counts how many binders it is away from
 * where it was bound
 *
 * So if we had
 *
 *   __________
 *  |          |
 * fn => fn => 1 + 0
 *        |________|
 *
 * The 0 refers to the inner binder and the 1 to the binder 1 binder
 * away. Here's the wikipedia article:
 *    http://www.wikiwand.com/en/De_Bruijn_index
 *
 * For types we'll just use numbers to indicate binding. Since we
 * never have nested scopes (all the binders for a type are fully
 * shifted to the left) we don't need a clever scheme like DeBruijn
 * indices. We don't allow the user to annotate types: we infer
 * absolutely everything.
 *)

structure TypeInfer :> TYPEINFER =
struct
(* As mentioned, type variables are just integers: They're globally unique *)
type tvar = int

(* Cough, cough, ignore this bit. It lets us generate fresh type
 * variables but uses some features of SML we haven't talked about yet *)
local val freshSource = ref 0 in
fun fresh () : tvar =
    !freshSource before freshSource := !freshSource + 1
end

(* A normal (not polymorphic) type *)
datatype monotype = TBool
                  | TArr of monotype * monotype
                  | TVar of tvar

(* A polymorphic type which has binds a list of type variables *)
datatype polytype = PolyType of int list * monotype

(* Our definition of expressions in our language *)
datatype exp = True
             | False
             | Var of int
             | App of exp * exp
             | Let of exp * exp
             | Fn of exp
             | If of exp * exp * exp

(* A piece of information we know about a particular variable. We
   either know it has a polytype or a monotype *)
datatype info = PolyTypeVar of polytype
              | MonoTypeVar of monotype

(* A list of information. The ith entry is about the DeBruijn variable i *)
type context = info list

(* Substitute some type var for another type *)
fun subst ty' var ty =
    case ty of
        TVar var' => if var = var' then ty' else TVar var'
      | TArr (l, r) => TArr (subst ty' var l, subst ty' var r)
      | TBool => TBool

(* Collect a list of all the variables in a type *)
fun freeVars t =
    case t of
        TVar v => [v]
      | TArr (l, r) => freeVars l @ freeVars r
      | TBool => []

(* Any polytype can construct a new monotype with the polymorphic
 * variables replaced by fresh weakly polymorphic variables *)
fun mintNewMonoType (PolyType (ls, ty)) =
    foldl (fn (v, t) => subst (TVar (fresh ())) v t) ty ls

fun generalizeMonoType ctx ty =
    let fun notMem xs x = List.all (fn y => x <> y) xs
        fun free (MonoTypeVar m) = freeVars m
          | free (PolyTypeVar (PolyType (bs, m))) =
            List.filter (notMem bs) (freeVars m)
        val ctxVars = List.concat (List.map free ctx)
    in PolyType (List.filter (notMem ctxVars) (freeVars ty), ty) end

exception UnboundVar of int

(* Lookup a variable in a list. If we don't find the variable then we throw
 * an UnboundVar exception *)
fun lookupVar var ctx =
    case List.nth (ctx, var) handle Subscript => raise UnboundVar var of
        PolyTypeVar pty => mintNewMonoType pty
      | MonoTypeVar mty => mty

(* A big part of the type checker is the generation of
 * "constraints". These are assertions that some type is equivalent to
 * another. These are represented with just a tuple of types which is to be
 * read "The left component unifies with the right component".
 *
 * Once we solve these constrains we get a [sol] which is a list of
 * variables to the monotypes the become.
 *)
type constr = (monotype * monotype)
type sol    = (tvar * monotype) list

exception UnificationError of constr

(* Substitute a type for a type variable in a list of constraints *)
fun substConstrs ty var (cs : constr list) : constr list =
    map (fn (l, r) => (subst ty var l, subst ty var r)) cs

(* Given a solution and a type, apply the solution by rewriting each
 * variable with what the solution says it's equivalent to.
 *)
fun applySol sol ty =
    foldl (fn ((v, ty), ty') => subst ty v ty') ty sol

fun applySolCxt sol cxt =
    let fun applyInfo i =
            case i of
                PolyTypeVar (PolyType (bs, m)) =>
                PolyTypeVar (PolyType (bs, (applySol sol m)))
              | MonoTypeVar m => MonoTypeVar (applySol sol m)
    in map applyInfo cxt end

(* Given a solution, add a new member to the solution ensuring that
 * the rhs of the new part of the solution is normal with respect to the
 * rest of the solution.
 *)
fun addSol v ty sol = (v, applySol sol ty) :: sol

(* Returns true if a variable occurs in the type *)
fun occursIn v ty = List.exists (fn v' => v = v') (freeVars ty)

fun unify ([] : constr list) : sol = []
  | unify (c :: constrs) =
    case c of
        (TBool, TBool) => unify constrs
      | (TVar i, TVar j) =>
        if i = j
        then unify constrs
        else addSol i (TVar j) (unify (substConstrs (TVar j) i constrs))
      | ((TVar i, ty) | (ty, TVar i)) =>
        if occursIn i ty
        then raise UnificationError c
        else addSol i ty (unify (substConstrs ty i constrs))
      | (TArr (l, r), TArr (l', r')) =>
        unify ((l, l') :: (r, r') :: constrs)
      | _ => raise UnificationError c

fun <+> (sol1, sol2) =
    let fun inSol2 v = List.all (fn (v', _) => v <> v') sol2
        val sol1' = List.filter (fn (v, _) => inSol2 v) sol1
    in
        map (fn (v, ty) => (v, applySol sol1 ty)) sol2 @ sol1'
    end
infixr 3 <+>

(* Generate all the constraints and solve them for a given expression *)
fun constrain ctx True = (TBool, [])
  | constrain ctx False = (TBool, [])
  | constrain ctx (Var i) = (lookupVar i ctx, [])
  | constrain ctx (Fn body) =
    let val argTy = TVar (fresh ())
        val (rTy, sol) = constrain (MonoTypeVar argTy :: ctx) body
    in (TArr (applySol sol argTy, rTy), sol) end
  | constrain ctx (If (i, t, e)) =
    let val (iTy, sol1) = constrain ctx i
        val (tTy, sol2) = constrain (applySolCxt sol1 ctx) t
        val (eTy, sol3) = constrain (applySolCxt (sol1 <+> sol2) ctx) e
    in
        (tTy, sol1 <+> sol2 <+> sol3 <+> unify [(iTy, TBool), (tTy, eTy)])
    end
  | constrain ctx (App (l, r)) =
    let val (domTy, ranTy) = (TVar (fresh ()), TVar (fresh ()))
        val (funTy, sol1) = constrain ctx l
        val (argTy, sol2) = constrain (applySolCxt sol1 ctx) r
        val sol = unify [(funTy, TArr (domTy, ranTy)), (argTy, domTy)]
                  <+> sol1
                  <+> sol2
    in (ranTy, sol) end
  | constrain ctx (Let (e, body)) =
    let val (eTy, sol1) = constrain ctx e
        val ctx' = applySolCxt sol1 ctx
        val eTy' = generalizeMonoType ctx' (applySol sol1 eTy)
        val (rTy, sol2) = constrain (PolyTypeVar eTy' :: ctx') body
    in (rTy, sol1 <+> sol2) end

(* Finally, infer and solve all the constraints for a type,
 * generating a final, inferred, polytype *)
fun infer e =
    let val (ty, sol) = constrain [] e
    in generalizeMonoType [] (applySol sol ty) end
end
