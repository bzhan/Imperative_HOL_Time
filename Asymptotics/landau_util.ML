(* Utility for landau symbols

   We can handle asymptotic bounds of the form polylog m n, which is
   the normalized form of %x. x^m (log x)^n.
 *)

signature LANDAU_UTIL =
sig
  val bd_of_th: thm -> term
  val dest_abs_t: term -> term * term

  val add_asym_bound: thm -> theory -> theory
  val find_asym_bound: theory -> string -> thm option

  val nat_to_real: term
  val to_real_t: Proof.context -> conv

  val runtime_rec_th: Proof.context -> thm -> thm -> thm list -> thm

  (* TODO: move*)
  val apply_thm: Proof.context -> thm list * term -> thm -> thm
  val eta_contract: thm -> thm
  val realT: typ
  val nat_power_t: term
  val real_power_t: term
  val ln_real: term

  val fold_polylog_args: conv
  val norm_poly_log: cterm * Proof.context -> conv
  val norm_poly_log_abs: Proof.context -> conv
  val analyze_poly_log: term -> int * int

  val pair_less_goal: int * int * int * int -> term
  val pair_le_goal: int * int * int * int -> term
  val compare_poly_log: Proof.context -> term * term -> (order * thm) option

  val stable_th: Proof.context -> term -> thm
  val event_mono_th: Proof.context -> term -> thm
  val event_nonneg_th: Proof.context -> term -> thm
  val bigtheta: term
  val cv_of_compare: order * thm -> conv
  val plus_absorb_cv: (Proof.context -> term * term -> (order * thm) option) ->
                      Proof.context -> conv
  val reduce_poly_log_sum: Proof.context -> conv
  val reduce_poly_log_all: Proof.context -> conv
  val asym_bound_th: Proof.context -> term -> thm
  val asym_bound_gen: Proof.context -> cterm * term -> thm
  val asym_bound_prfstep: proofstep
  val add_asym_bound_proofsteps: theory -> theory
end;

structure LandauUtil : LANDAU_UTIL =
struct

structure Data = Theory_Data (
  type T = thm Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge Thm.eq_thm
)

(* Asymptotic bound of the theorem *)
fun bd_of_th th =
    th |> prop_of' |> dest_arg

fun dest_abs_t t =
    case t of
        Abs (abs as (_, T, _)) =>
        let
          val (x, body) = Term.dest_abs abs
        in
          (Free (x, T), body)
        end
      | _ => raise Fail "dest_abs_t"

(* Given th of the form (%x. f(x)) : \Theta(%x. g(x)), add the theorem
   as an asymptotic bound rule under the function name f. *)
fun add_asym_bound th thy =
    let
      val (_, r_body) = dest_abs_t (th |> prop_of' |> dest_arg1)
      val body = dest_arg r_body
      val (f, _) = Term.strip_comb body
      val (nm, _) = Term.dest_Const f
      val _ = writeln ("Name is " ^ nm)
    in
      thy |> Data.map (Symtab.update (nm, th))
    end

(* Given function name f, find asymptotic bound rule for %x. f(x). *)
fun find_asym_bound thy nm =
    let
      val tbl = Data.get thy
    in
      Symtab.lookup tbl nm
    end

(* Conversion function from nat to real. *)
val nat_to_real = @{term real}

(* Convert the expression to the form real (...). For example:

   - real a + real b => real (a + b)

   - real a * real b => real (a * b)
 *)
fun to_real_t ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if UtilArith.is_plus t then
        Conv.every_conv [Conv.binop_conv (to_real_t ctxt),
                         rewr_obj_eq (obj_sym @{thm of_nat_add})] ct
      else if UtilArith.is_times t then
        Conv.every_conv [Conv.binop_conv (to_real_t ctxt),
                         rewr_obj_eq (obj_sym @{thm of_nat_mult})] ct
      else if UtilArith.is_numc t then
        let
          val n = UtilArith.dest_numc t
          val t' = nat_to_real $ mk_nat n
          val eq = UtilArith.prove_by_arith ctxt [] (UtilBase.mk_eq (t, t'))
        in
          to_meta_eq eq
        end
      else if Term.head_of t aconv nat_to_real then
        Conv.all_conv ct
      else
        raise Fail "to_real_t"
    end

(* Move real(...) to the innermost in the expression. *)
fun from_real ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if Term.head_of t aconv nat_to_real then
        if UtilArith.is_plus (dest_arg t) then
          Conv.every_conv [rewr_obj_eq @{thm of_nat_add},
                           Conv.binop_conv (from_real ctxt)] ct
        else if UtilArith.is_times (dest_arg t) then
          Conv.every_conv [rewr_obj_eq @{thm of_nat_mult},
                           Conv.binop_conv (from_real ctxt)] ct
        else if UtilArith.is_numc (dest_arg t) then
          let
            val n = UtilArith.dest_numc (dest_arg t)
            val t' = HOLogic.mk_number @{typ real} n
            val eq = UtilArith.prove_by_arith ctxt [] (UtilBase.mk_eq (t, t'))
          in
            to_meta_eq eq
          end
        else
          Conv.all_conv ct
      else
        Conv.all_conv ct
    end

(* Used in applying the Master theorem *)
fun runtime_rec_th ctxt eq_th def_eq rewr_ths =
    let
      val cvar = (Term.add_vars (Thm.prop_of eq_th) [])
                    |> the_single |> Var |> Thm.cterm_of ctxt
      val subst = [(cvar, Thm.cterm_of ctxt (Free ("n", natT)))]

      val rhs_cv = Conv.every_conv (
            map (fn th => Conv.bottom_conv
                              (K (Conv.try_conv (rewr_obj_eq th))) ctxt)
                (obj_sym def_eq :: rewr_ths))

      val prem_cv = Conv.try_conv (Trueprop_conv (
                                      rewr_obj_eq @{thm Nat.less_eq_Suc_le}))

      val eq1 = eq_th |> Util.subst_thm_atomic subst
                      |> to_meta_eq
      val t = eq1 |> Thm.prems_of |> the_single
      val subst' = [(Thm.cterm_of ctxt (Free ("n", natT)), cvar)]
    in
      eq1 |> Util.send_all_to_hyps
          |> Thm.combination (Thm.reflexive @{cterm real})
          |> Util.apply_to_lhs (rewr_obj_eq (obj_sym def_eq))
          |> Util.apply_to_rhs (from_real ctxt)
          |> Util.apply_to_rhs rhs_cv
          |> to_obj_eq
          |> Thm.implies_intr (Thm.cterm_of ctxt t)
          |> apply_to_thm (Conv.arg1_conv prem_cv)
          |> Util.subst_thm_atomic subst'
    end

fun apply_thm ctxt (ths, t) th =
    let
      val pat = concl_of' th
      val thy = Proof_Context.theory_of ctxt
      val inst = Pattern.match thy (pat, t) fo_init
                 handle Pattern.MATCH =>
                        let
                          val _ = trace_tlist ctxt "Input" [pat, t]
                        in
                          raise Fail "apply_thm"
                        end
      val th' = Util.subst_thm_thy thy inst th
    in
      ths MRS th'
    end

val eta_contract = Drule.eta_contraction_rule

val realT = @{typ real}
val nat_power_t = Const (@{const_name power}, natT --> natT --> natT)
val real_power_t = Const (@{const_name power}, realT --> natT --> realT)
val ln_real = Const (@{const_name ln}, realT --> realT)

val fold_polylog_args =
    Conv.every_conv (
      map (fn i => Util.argn_conv i Nat_Util.nat_fold_conv) [0, 1])

(* Normalize the term (as a function of var) into polylog form. *)
fun norm_poly_log (cvar, ctxt) ct =
    let
      val var = Thm.term_of cvar
      val t = Thm.term_of ct
    in
      if t aconv @{term "1::real"} then
        Conv.every_conv [rewr_obj_eq (obj_sym @{thm of_nat_1}),
                         norm_poly_log (cvar, ctxt)] ct
      else if t aconv (nat_to_real $ mk_nat 1) then
        let
          val env = fo_init |> Util.update_env (("x",0), var)
          val norm_th = @{thm landau_norms(1)} |> Util.subst_thm ctxt env
        in
          rewr_obj_eq norm_th ct
        end
      else if t aconv (nat_to_real $ var) then
        rewr_obj_eq @{thm landau_norms(2)} ct
      else if Term.head_of t aconv nat_to_real andalso
              Term.head_of (dest_arg t) aconv nat_power_t andalso
              dest_arg1 (dest_arg t) aconv var then
        rewr_obj_eq @{thm landau_norms(4)} ct
      else if t aconv (ln_real $ (nat_to_real $ var)) then
        rewr_obj_eq @{thm landau_norms(3)} ct
      else if Term.head_of t aconv real_power_t andalso
              dest_arg1 t aconv (ln_real $ (nat_to_real $ var)) then
        rewr_obj_eq @{thm landau_norms(5)} ct
      else if UtilArith.is_times t then
        Conv.every_conv [Conv.binop_conv (norm_poly_log (cvar, ctxt)),
                         rewr_obj_eq @{thm landau_norms(6)},
                         fold_polylog_args] ct
      else
        Conv.all_conv ct
    end

(* Normalize a term of the form %x. f(x) into polylog form. This can
   also handle a sum of functions, e.g. %x. f(x) + g(x). *)
fun norm_poly_log_abs ctxt ct =
    let
      val t = Thm.term_of ct
      val (_, body) = dest_abs_t t
    in
      if UtilArith.is_plus body then
        Conv.every_conv [rewr_obj_eq (obj_sym @{thm plus_fun_def}),
                         Conv.binop_conv (norm_poly_log_abs ctxt)] ct
      else
        Conv.every_conv [Conv.abs_conv norm_poly_log ctxt,
                         Thm.eta_conversion] ct
    end

(* Given t of the form polylog m n, return the two numbers m and n. *)
fun analyze_poly_log t =
    let
      val (_, args) = Term.strip_comb t
    in
      apply2 (UtilArith.dest_numc) (hd args, nth args 1)
    end

(* (a1 < a2) | (a1 = a2 & b1 < b2) *)
fun pair_less_goal (a1, a2, b1, b2) =
    disj $ (Nat_Util.mk_less (mk_nat a1, mk_nat a2))
         $ (conj $ (UtilBase.mk_eq (mk_nat a1, mk_nat a2))
                 $ Nat_Util.mk_less (mk_nat b1, mk_nat b2))

(* (a1 < a2) | (a1 = a2 & b1 <= b2) *)
fun pair_le_goal (a1, a2, b1, b2) =
    disj $ (Nat_Util.mk_less (mk_nat a1, mk_nat a2))
         $ (conj $ (UtilBase.mk_eq (mk_nat a1, mk_nat a2))
                 $ Nat_Util.mk_le (mk_nat b1, mk_nat b2))

(* Given two polylog functions s and t, return one of (EQUAL, (s == t)),
   (LESS, s : o(t)), and (GREATER, t : o(s)).
 *)
fun compare_poly_log ctxt (t1, t2) =
    let
      val (a1, b1) = analyze_poly_log t1
      val (a2, b2) = analyze_poly_log t2
    in
      if a1 = a2 andalso b1 = b2 then
        SOME (EQUAL, Thm.reflexive (Thm.cterm_of ctxt t1))
      else if a1 < a2 orelse (a1 = a2 andalso b1 < b2) then
        let
          val goal = pair_less_goal (a1, a2, b1, b2)
          val th = UtilArith.prove_by_arith ctxt [] goal
        in
          SOME (LESS, eta_contract (th RS @{thm poly_log_compare}))
        end
      else (* a2 < a1 orelse (a2 = a1 andalso b2 < b1) *)
        let
          val goal = pair_less_goal (a2, a1, b2, b1)
          val th = UtilArith.prove_by_arith ctxt [] goal
        in
          SOME (GREATER, eta_contract (th RS @{thm poly_log_compare}))
        end
    end

(* Given a term t, return stablebigO t. *)
fun stable_th ctxt t =
    apply_thm ctxt ([], @{term stablebigO} $ t) @{thm stable_polylog}

(* Given a term t, return event_mono t. *)
fun event_mono_th ctxt t =
    apply_thm ctxt ([], @{term event_mono} $ t) @{thm event_mono_polylog}

(* Given a term t, return event_nonneg t. *)
fun event_nonneg_th ctxt t =
    if UtilArith.is_plus t then
      let
        val (th1, th2) = apply2 (event_nonneg_th ctxt) (Util.dest_binop_args t)
      in
        [th1, th2] MRS @{thm event_nonneg_add'}
      end
    else
      let
        val event_nonneg_t =
            @{term "eventually_nonneg at_top (b::nat=>real)"}
                 |> Term.dest_comb |> fst
      in
        (apply_thm ctxt ([], event_nonneg_t $ t) @{thm event_nonneg_polylog})
            |> eta_contract
      end

val bigtheta = @{term "\<Theta>(b::nat=>real)"} |> Term.dest_comb |> fst

(* Given t of the form \Theta(a + b), and res as returned by
   compare_poly_log(a, b), rewrite t to one of \Theta(a) or \Theta(b).
   This function works for general \Theta, including the 2d case. *)
fun cv_of_compare res ct =
    case res of
        (LESS, th) =>
        rewr_obj_eq (th RS @{thm plus_absorb1'}) ct
      | (GREATER, th) =>
        rewr_obj_eq (th RS @{thm plus_absorb2'}) ct
      | (EQUAL, _) =>
        rewr_obj_eq (@{thm plus_absorb_same'}) ct

(* Given t of the form \Theta(a + b), use cmp_f to compare a and b,
   then use cv_of_compare to possibly reduce. *)
fun plus_absorb_cv cmp_f ctxt ct =
    let
      val arg = ct |> Thm.term_of |> dest_arg
    in
      case cmp_f ctxt (Util.dest_binop_args arg) of
          SOME res => cv_of_compare res ct
        | NONE => raise Fail "plus_absorb_cv"
    end

(* Function for reducing a sum \Theta(a_1 + ... + a_n), in the 1d case. *)
fun reduce_poly_log_sum ctxt ct =
    let
      val arg = ct |> Thm.term_of |> dest_arg
    in
      if UtilArith.is_plus arg then
        let
          val (t1, t2) = (bigtheta $ dest_arg1 arg, bigtheta $ dest_arg arg)
          val (ct1, ct2) = apply2 (Thm.cterm_of ctxt) (t1, t2)
          val (th1, th2) = apply2 (reduce_poly_log_sum ctxt) (ct1, ct2)
          val (a, b) = th1 |> Thm.prop_of |> Logic.dest_equals
                           |> apply2 dest_arg
          val (c, d) = th2 |> Thm.prop_of |> Logic.dest_equals
                           |> apply2 dest_arg
          val (nna, nnb) = apply2 (event_nonneg_th ctxt) (a, b)
          val (nnc, nnd) = apply2 (event_nonneg_th ctxt) (c, d)
          val th = [nna, nnb, nnc, nnd, to_obj_eq th1, to_obj_eq th2]
                       MRS @{thm Theta_plus'}
        in
          Conv.every_conv [rewr_obj_eq th,
                           plus_absorb_cv compare_poly_log ctxt] ct
        end
      else
        Conv.all_conv ct
    end

(* Normalization function of \Theta targets. Converts a term of form
   \Theta(f_1(x) + ... + f_n(x)) by first normalizing each f_i to polylog,
   then add the terms using plus_absorb. *)
fun reduce_poly_log_all ctxt ct =
    Conv.every_conv [Conv.arg_conv (norm_poly_log_abs ctxt),
                     reduce_poly_log_sum ctxt] ct

(* Main function for deriving the asymptotic bound of a function t. Returns
   a theorem of the form t : \Theta(polylog m n). *)
fun asym_bound_th ctxt t =
    let
      val (var, r_body) = dest_abs_t t
      val body = dest_arg r_body
      val asym_cv = apply_to_thm' o Conv.arg_conv o Conv.arg_conv
    in
      if UtilArith.is_plus body then
        (* Plus case *)
        let
          val (a, b) = Util.dest_binop_args body
          val a' = Util.lambda_abstract var (nat_to_real $ a)
          val b' = Util.lambda_abstract var (nat_to_real $ b)
          val (th1, th2) = apply2 (asym_bound_th ctxt) (a', b')
          val cv = plus_absorb_cv compare_poly_log ctxt
          val g1 = dest_arg (bd_of_th th1)
          val g2 = dest_arg (bd_of_th th2)
        in
          ([event_nonneg_th ctxt g1, event_nonneg_th ctxt g2,
            th1, th2] MRS @{thm bigtheta_add})
              |> apply_to_thm' (Conv.arg_conv cv)
        end
      else if UtilArith.is_minus body then
        (* Minus case. Only handles a - b where a is linear and b is constant *)
        let
          val (a, b) = Util.dest_binop_args body
          val a' = Util.lambda_abstract var (nat_to_real $ a)
          val b' = Util.lambda_abstract var (nat_to_real $ b)
          val (th1, th2) = apply2 (asym_bound_th ctxt) (a', b')
          val th1 = asym_cv (rewr_obj_eq @{thm landau_norm_linear}) th1
          val th2 = asym_cv (rewr_obj_eq @{thm landau_norm_const}) th2
        in
          ([th1, th2] MRS @{thm asym_bound_diff})
              |> asym_cv (rewr_obj_eq (obj_sym @{thm landau_norm_linear}))
        end
      else if UtilArith.is_times body then
        (* Times case *)
        let
          val (a, b) = Util.dest_binop_args body
          val a' = Util.lambda_abstract var (nat_to_real $ a)
          val b' = Util.lambda_abstract var (nat_to_real $ b)
          val (th1, th2) = apply2 (asym_bound_th ctxt) (a', b')
          val cv = Conv.every_conv [rewr_obj_eq @{thm landau_norm_times},
                                    fold_polylog_args]
        in
          ([th1, th2] MRS @{thm bigtheta_mult}) |> asym_cv cv
        end
      else if UtilArith.is_numc body andalso UtilArith.dest_numc body > 0 then
        (* Constant case *)
        let
          val c_gt_0 = Nat_Util.nat_less_th 0 (UtilArith.dest_numc body)
        in
          c_gt_0 RS @{thm bigtheta_const}
        end
      else if not (Term.is_Const body orelse Util.occurs_free var body) then
        let
          val c_gt_0 = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (Nat_Util.mk_less (Nat_Util.nat0, body))))
        in
          c_gt_0 RS @{thm bigtheta_const}
        end             
      else if UtilArith.is_divide body then
        (* Divide case *)
        let
          val (a, b) = Util.dest_binop_args body
          val a' = Util.lambda_abstract var (nat_to_real $ a)
          val c_gt_0 = Nat_Util.nat_less_th 0 (UtilArith.dest_numc b)
          val th1 = (asym_bound_th ctxt a')
                        |> asym_cv (rewr_obj_eq @{thm landau_norm_linear})
        in
          ([c_gt_0, th1] MRS @{thm asym_bound_div_linear})
              |> asym_cv (rewr_obj_eq (obj_sym @{thm landau_norm_linear}))
        end
      else if body aconv var then
        (* Linear case *)
        @{thm bigtheta_linear}
      else
        (* Registered function case *)
        let
          val thy = Proof_Context.theory_of ctxt
          val (f, args) = Term.strip_comb body
        in
          if length args <= 1 then
            let
              val (nm, _) = Term.dest_Const f
              val th1 =
                  case find_asym_bound thy nm of
                      NONE => raise Fail ("Asymptotic bound not found." ^ nm)
                    | SOME th => th |> apply_to_thm' (
                                  Conv.arg_conv (
                                    Conv.arg_conv (norm_poly_log_abs ctxt)))
              val arg = if length args = 1 then the_single args else var
            in
              if arg aconv var then th1
              else let
                val a' = Util.lambda_abstract var (nat_to_real $ arg)
                val th2 = asym_bound_th ctxt a'
                val f = dest_arg (bd_of_th th1)
                val stable_f = stable_th ctxt f
                val event_mono_f = event_mono_th ctxt f
              in
                [stable_f, event_mono_f, th1, th2]
                    MRS @{thm bigTheta_compose_linear'}
              end
            end
          else
            raise Fail "asym_bound_sum: function with more than one arguments."
        end
    end

(* Derive a theorem of the form t : \Theta(goal). This works by first finding
   the asymptotic bound of t using asym_bound_th, then compare that bound to
   the normalized form of goal. *)
fun asym_bound_gen ctxt (ct, goal) =
    let
      val eq_th = Conv.abs_conv (to_real_t o snd) ctxt ct
      val t' = Util.rhs_of eq_th
      val th = asym_bound_th ctxt t'
      val goal_th = reduce_poly_log_all ctxt (Thm.cterm_of ctxt goal)
    in
      if Util.rhs_of goal_th aconv bd_of_th th then
        th |> apply_to_thm' (Conv.arg1_conv (Conv.rewr_conv (meta_sym eq_th)))
           |> apply_to_thm' (Conv.arg_conv (Conv.rewr_conv (meta_sym goal_th)))
      else let
        val _ = trace_t ctxt "Produced asym bound: " (bd_of_th th)
        val _ = trace_t ctxt "Needed asym bound: " (Util.rhs_of goal_th)
      in
        raise Fail "asym_bound_gen"
      end
    end

val asym_bound_prfstep =
    ProofStep.prfstep_custom
        "asym_bound"
        [WithItem (TY_PROP, @{term_pat "~((?f::nat=>real) : \<Theta>(?g))"})]
        (fn ((id, _), ths) => fn _ => fn ctxt =>
            let
              val th = the_single ths
              val (t, goal) = th |> prop_of' |> dest_not |> Util.dest_binop_args
              val res = asym_bound_gen ctxt (Thm.cterm_of ctxt t, goal)
              val contra = ([th, res] MRS UtilBase.contra_triv_th)
                              |> fold Thm.implies_intr (map (Thm.cterm_of ctxt) (Thm.hyps_of res))
              val contra = if Util.is_implies (Thm.prop_of contra) then
                             contra |> apply_to_thm UtilLogic.rewrite_from_contra_form
                                    |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
                           else
                             contra
            in
              [Update.thm_update (id, contra)]
            end)

val add_asym_bound_proofsteps =
    fold add_prfstep [
      asym_bound_prfstep
    ]

end  (* structure LandauUtil. *)

val _ = Theory.setup LandauUtil.add_asym_bound_proofsteps
