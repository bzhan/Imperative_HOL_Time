(* Utility for landau symbols in two variables.

   In two variables, the normal form is polylog2 a b c d, which is the
   normalized form of %(x,y). x^a (log x)^b y^c (log y)^d, and the sum
   of these functions.
 *)

signature LANDAU_UTIL_2D =
sig
  val fold_polylog2_args: conv
  val fst_nat_t: term
  val snd_nat_t: term

  val norm_poly_log2: cterm * Proof.context -> conv
  val norm_poly_log2_abs: Proof.context -> conv
  val analyze_poly_log2: term -> int * int * int * int
  val compare_poly_log2: Proof.context -> term * term -> (order * thm) option

  val stable2_th: Proof.context -> term -> thm
  val event_mono2_th: Proof.context -> term -> thm
  val event_nonneg2_th: Proof.context -> term -> thm

  val is_prod: term -> bool
  val bigtheta2: term
  val reduce_poly_log2_plus1: Proof.context -> conv
  val reduce_poly_log2_sum: Proof.context -> conv
  val reduce_poly_log2_times1: Proof.context -> conv
  val reduce_poly_log2_times: Proof.context -> conv
  val reduce_poly_log2_all: Proof.context -> conv
  val asym_bound2_th: Proof.context -> term -> thm
  val asym_bound2_gen: Proof.context -> cterm * term -> thm
  val asym_bound2_prfstep: proofstep

  val add_asym_bound2_proofsteps: theory -> theory
end;

structure LandauUtil2D : LANDAU_UTIL_2D =
struct

open LandauUtil

(* Simplify every argument of polylog2 a b c d *)
val fold_polylog2_args =
    Conv.every_conv (
      map (fn i => Util.argn_conv i Nat_Util.nat_fold_conv) [0, 1, 2, 3])

val fst_nat_t = @{term "fst::nat*nat=>nat"}
val snd_nat_t = @{term "snd::nat*nat=>nat"}

(* Normalization of a term into polylog2 form. Here, the two arguments are
   fst(var) and snd(var).

   Currently, can handle the following cases:

   - Only fst(var) is present in the expression.

   - Only snd(var) is present in the expression.

   - Sums in normalized form.

   - Product of two valid expressions.

   - Expressions of the form real(m*n), where real(m) and real(n) are valid.
 *)
fun norm_poly_log2 (cvar, ctxt) ct =
    let
      val var = Thm.term_of cvar
      val t = Thm.term_of ct
    in
      if not (Util.is_subterm (snd_nat_t $ var) t) then
        Conv.every_conv [
          norm_poly_log (Thm.cterm_of ctxt (fst_nat_t $ var), ctxt),
          rewr_obj_eq @{thm landau_norms2(1)}] ct
      else if not (Util.is_subterm (fst_nat_t $ var) t) then
        Conv.every_conv [
          norm_poly_log (Thm.cterm_of ctxt (snd_nat_t $ var), ctxt),
          rewr_obj_eq @{thm landau_norms2(2)}] ct
      else if UtilArith.is_plus t then
        Conv.every_conv [Conv.binop_conv (norm_poly_log2 (cvar, ctxt)),
                         rewr_obj_eq (obj_sym @{thm plus_fun_apply})] ct
      else if UtilArith.is_times t then
        Conv.every_conv [Conv.binop_conv (norm_poly_log2 (cvar, ctxt)),
                         rewr_obj_eq @{thm landau_norms2(3)},
                         fold_polylog2_args] ct
      else if Term.head_of t aconv nat_to_real andalso
              UtilArith.is_plus (dest_arg t) then
        Conv.every_conv [rewr_obj_eq @{thm of_nat_add},
                         norm_poly_log2 (cvar, ctxt)] ct
      else if Term.head_of t aconv nat_to_real andalso
              UtilArith.is_times (dest_arg t) then
        Conv.every_conv [rewr_obj_eq @{thm of_nat_mult},
                         norm_poly_log2 (cvar, ctxt)] ct
      else
        raise Fail "norm_poly_log2"
    end

(* Normalize a term of the form %(x,y). f(x,y) into polylog2 form. This can
   also handle a sum of functions. *)
fun norm_poly_log2_abs ctxt ct =
    let
      val t = Thm.term_of ct
    in
      case t of
          Abs _ =>
          let
            val (_, body) = LandauUtil.dest_abs_t t
          in
            if UtilArith.is_plus body then
              Conv.every_conv [rewr_obj_eq (obj_sym @{thm plus_fun_def}),
                               Conv.binop_conv (norm_poly_log2_abs ctxt)] ct
            else
              Conv.every_conv [Conv.abs_conv norm_poly_log2 ctxt,
                               Thm.eta_conversion] ct
          end
        | Const (@{const_name case_prod}, _) $ _ =>
          Conv.every_conv [rewr_obj_eq @{thm case_prod_beta'},
                           norm_poly_log2_abs ctxt] ct
        | _ => Conv.all_conv ct
    end

(* Given t of the form polylog a b c d, return the four numbers a b c and d. *)
fun analyze_poly_log2 t =
    let
      val (_, args) = Term.strip_comb t
    in
      (UtilArith.dest_numc (hd args), UtilArith.dest_numc (nth args 1),
       UtilArith.dest_numc (nth args 2), UtilArith.dest_numc (nth args 3))
    end

(* Compare two polylog2 expressions *)
fun compare_poly_log2 ctxt (t1, t2) =
    let
      val (a1, b1, c1, d1) = analyze_poly_log2 t1
      val (a2, b2, c2, d2) = analyze_poly_log2 t2
    in
      if a1 = a2 andalso b1 = b2 andalso c1 = c2 andalso d1 = d2 then
        SOME (EQUAL, Thm.reflexive (Thm.cterm_of ctxt t1))
      else if (a1 < a2 orelse (a1 = a2 andalso b1 < b2)) andalso
              (c1 < c2 orelse (c1 = c2 andalso d1 <= d2)) then
        let
          val goal = conj $ pair_less_goal (a1, a2, b1, b2)
                          $ pair_le_goal (c1, c2, d1, d2)
          val th = UtilArith.prove_by_arith ctxt [] goal
        in
          SOME (LESS, eta_contract (th RS @{thm polylog2_compare'}))
        end
      else if (a1 < a2 orelse (a1 = a2 andalso b1 <= b2)) andalso
              (c1 < c2 orelse (c1 = c2 andalso d1 < d2)) then
        let
          val goal = conj $ pair_le_goal (a1, a2, b1, b2)
                          $ pair_less_goal (c1, c2, d1, d2)
          val th = UtilArith.prove_by_arith ctxt [] goal
        in
          SOME (LESS, eta_contract (th RS @{thm polylog2_compare2'}))
        end
      else if (a2 < a1 orelse (a2 = a1 andalso b2 < b1)) andalso
              (c2 < c1 orelse (c2 = c1 andalso d2 <= d1)) then
        let
          val goal = conj $ pair_less_goal (a2, a1, b2, b1)
                          $ pair_le_goal (c2, c1, d2, d1)
          val th = UtilArith.prove_by_arith ctxt [] goal
        in
          SOME (GREATER, eta_contract (th RS @{thm polylog2_compare'}))
        end
      else if (a2 < a1 orelse (a2 = a1 andalso b2 <= b1)) andalso
              (c2 < c1 orelse (c2 = c1 andalso d2 < d1)) then
        let
          val goal = conj $ pair_le_goal (a2, a1, b2, b1)
                          $ pair_less_goal (c2, c1, d2, d1)
          val th = UtilArith.prove_by_arith ctxt [] goal
        in
          SOME (GREATER, eta_contract (th RS @{thm polylog2_compare2'}))
        end
      else
        NONE
    end

val event_nonneg2_t =
    @{term "eventually_nonneg (prod_filter at_top at_top) (b::nat*nat=>real)"}
         |> Term.dest_comb |> fst

(* Given a term t, return event_nonneg2 t. *)
fun event_nonneg2_th ctxt t =
    if UtilArith.is_plus t then
      let
        val (th1, th2) = apply2 (event_nonneg2_th ctxt) (Util.dest_binop_args t)
      in
        [th1, th2] MRS @{thm event_nonneg_add'}
      end
    else if UtilArith.is_times t then
      let
        val (th1, th2) = apply2 (event_nonneg2_th ctxt) (Util.dest_binop_args t)
      in
        [th1, th2] MRS @{thm event_nonneg_mult'}
      end
    else
      (apply_thm ctxt ([], event_nonneg2_t $ t) @{thm event_nonneg_polylog2})
          |> eta_contract

(* Given a term t, return stablebigO2 t. *)
fun stable2_th ctxt t =
    if UtilArith.is_plus t then
      let
        val (t1, t2) = Util.dest_binop_args t
        val (th1, th2) = apply2 (stable2_th ctxt) (t1, t2)
        val (nneg1, nneg2) = apply2 (event_nonneg2_th ctxt) (t1, t2)
      in
        [th1, th2, nneg1, nneg2] MRS @{thm stablebigO2_plus}
      end
    else
      (apply_thm ctxt ([], @{term stablebigO2} $ t) @{thm stable_polylog2})
          |> eta_contract

(* Given a term t, return event_mono2 t. *)
fun event_mono2_th ctxt t =
    if UtilArith.is_plus t then
      let
        val (t1, t2) = Util.dest_binop_args t
        val (th1, th2) = apply2 (event_mono2_th ctxt) (t1, t2)
        val (nneg1, nneg2) = apply2 (event_nonneg2_th ctxt) (t1, t2)
      in
        [th1, th2, nneg1, nneg2] MRS @{thm event_mono2_plus}
      end
    else
      (apply_thm ctxt ([], @{term event_mono2} $ t) @{thm event_mono2_polylog2})
          |> eta_contract

fun is_prod t =
    case t of
        Const (@{const_name Pair}, _) $ _ $ _ => true
      | _ => false

val bigtheta2 = @{term "\<Theta>\<^sub>2(b::nat*nat=>real)"}
                     |> Term.dest_comb |> fst

val plus_ac_fn = Nat_Util.plus_ac_on_typ @{theory} @{typ "nat*nat=>real"}

(* Given ct of the form \Theta(a + b), and cv1, cv2 used for rewriting
   \Theta(a) and \Theta(b), rewrite using cv1 and cv2 and combine the
   results using theorem Theta_plus'. *)
fun theta2_binop_cv' ctxt (cv1, cv2) ct =
    let
      val (ct1, ct2) = ct |> Thm.term_of |> dest_arg
                          |> Util.dest_binop_args
                          |> apply2 (fn t => bigtheta2 $ t)
                          |> apply2 (Thm.cterm_of ctxt)
      val (th1, th2) = (cv1 ct1, cv2 ct2)
      val (a, b) = th1 |> Thm.prop_of |> Logic.dest_equals
                       |> apply2 dest_arg
      val (c, d) = th2 |> Thm.prop_of |> Logic.dest_equals
                       |> apply2 dest_arg
      val (nna, nnb) = apply2 (event_nonneg2_th ctxt) (a, b)
      val (nnc, nnd) = apply2 (event_nonneg2_th ctxt) (c, d)
      val th = [nna, nnb, nnc, nnd, to_obj_eq th1, to_obj_eq th2]
                   MRS @{thm Theta_plus'}
    in
      to_meta_eq th
    end

fun theta2_binop_cv ctxt cv ct = theta2_binop_cv' ctxt (cv, cv) ct
fun theta2_arg1_cv ctxt cv ct = theta2_binop_cv' ctxt (cv, Conv.all_conv) ct
fun theta2_arg_cv ctxt cv ct = theta2_binop_cv' ctxt (Conv.all_conv, cv) ct

(* Given ct of form Theta_2 (f_1 + ... + f_n + g), compare g to each
   of f_i, reduce if possible. Assume f_1 + ... + f_n is in normal
   form.
 *)
fun reduce_poly_log2_plus1 ctxt ct =
    let
      val arg = ct |> Thm.term_of |> dest_arg
      val (fs, g) = arg |> Util.dest_binop_args
                        |> apfst (ACUtil.dest_ac plus_ac_fn)
    in
      if length fs = 1 then
        case compare_poly_log2 ctxt (the_single fs, g) of
            SOME res => cv_of_compare res ct
          | NONE => Conv.all_conv ct
      else
        case get_index (fn f => compare_poly_log2 ctxt (f, g)) fs of
            NONE => Conv.all_conv ct
          | SOME (i, (ord, th)) =>
            Conv.every_conv [
              Conv.arg_conv (Conv.arg1_conv (
                                ACUtil.move_outmost plus_ac_fn (nth fs i))),
              Conv.arg_conv (ACUtil.assoc_cv plus_ac_fn),
              theta2_arg_cv ctxt (cv_of_compare (ord, th)),
              reduce_poly_log2_plus1 ctxt] ct
    end

(* Reduce ct of the form Theta_2((f_1 + ... + f_n) + (g_1 + ... +
   g_n)), by calling the previous function on each of g_i. Assume f_1
   + ... + f_n and g_1 + ... + g_n are in normal forms.
 *)
fun reduce_poly_log2_sum ctxt ct =
    let
      val (_, b) = ct |> Thm.term_of |> dest_arg |> Util.dest_binop_args
    in
      if UtilArith.is_plus b then
        Conv.every_conv [
          Conv.arg_conv (ACUtil.assoc_sym_cv plus_ac_fn),
          theta2_arg1_cv ctxt (reduce_poly_log2_plus1 ctxt),
          reduce_poly_log2_sum ctxt] ct
      else
        reduce_poly_log2_plus1 ctxt ct
    end

(* Function for reducing a term of the form (f_1 + f_2 + .. + f_n) *
   g. Here we assume that f_1 + ... + f_n is normalized.
 *)
fun reduce_poly_log2_times1 ctxt ct =
    let
      val (a, _) = ct |> Thm.term_of |> dest_arg |> Util.dest_binop_args
    in
      if UtilArith.is_plus a then
        Conv.every_conv [
          Conv.arg_conv (rewr_obj_eq @{thm algebra_simps(17)}),
          theta2_arg1_cv ctxt (reduce_poly_log2_times1 ctxt),
          Conv.arg_conv (Conv.arg_conv (rewr_obj_eq @{thm landau_norms2'})),
          Conv.arg_conv (Conv.arg_conv fold_polylog2_args),
          reduce_poly_log2_plus1 ctxt] ct
      else
        Conv.every_conv [
          Conv.arg_conv (rewr_obj_eq @{thm landau_norms2'}),
          Conv.arg_conv fold_polylog2_args] ct
    end

(* Function for reducing a term of the form (f_1 + ... + f_n) * (g_1 +
   ... + g_n).
 *)
fun reduce_poly_log2_times ctxt ct =
    let
      val (_, b) = ct |> Thm.term_of |> dest_arg |> Util.dest_binop_args
    in
      if UtilArith.is_plus b then
        Conv.every_conv [
          Conv.arg_conv (rewr_obj_eq @{thm algebra_simps(18)}),
          theta2_arg1_cv ctxt (reduce_poly_log2_times ctxt),
          theta2_arg_cv ctxt (reduce_poly_log2_times1 ctxt),
          reduce_poly_log2_sum ctxt] ct
      else
        reduce_poly_log2_times1 ctxt ct
    end

(* General normalization function. *)
fun reduce_poly_log2_all ctxt ct =
    let
      val arg = ct |> Thm.term_of |> dest_arg
    in
      if UtilArith.is_plus arg then
        Conv.every_conv [theta2_binop_cv ctxt (reduce_poly_log2_all ctxt),
                         reduce_poly_log2_sum ctxt] ct
      else if UtilArith.is_times arg then
        Conv.every_conv [theta2_binop_cv ctxt (reduce_poly_log2_all ctxt),
                         reduce_poly_log2_times ctxt] ct
      else
        Conv.all_conv ct
    end

(* Main function for deriving the asymptotic bound of a function t. Returns
   a theorem of the form t : \Theta_2(f_1 + ... + f_n), where each f_i is in
   polylog2 form. *)
fun asym_bound2_th ctxt t =
    let
      val thy = Proof_Context.theory_of ctxt

      val (var, r_body) = LandauUtil.dest_abs_t t
      val body' = dest_arg r_body
    in
      if UtilArith.is_plus body' then
        (* Plus case: find asymptotic bound of the two sides, then add
           them together.
         *)
        let
          val (a, b) = Util.dest_binop_args body'
          val t1 = (Term.abstract_over (var, nat_to_real $ a))
                       |> Term.lambda var
          val t2 = (Term.abstract_over (var, nat_to_real $ b))
                       |> Term.lambda var
          val (th1, th2) = apply2 (asym_bound2_th ctxt) (t1, t2)
          val g1 = dest_arg (bd_of_th th1)
          val g2 = dest_arg (bd_of_th th2)
          val (nn1, nn2) = apply2 (event_nonneg2_th ctxt) (g1, g2)
        in
          ([nn1, nn2, th1, th2] MRS @{thm bigtheta_add})
              |> apply_to_thm' (Conv.arg_conv (reduce_poly_log2_sum ctxt))
              |> eta_contract
        end
      else if UtilArith.is_times body' then
        (* Times case: currently only handle the case where both sides
           are one polylog2.
         *)
        let
          val (a, b) = Util.dest_binop_args body'
          val t1 = (Term.abstract_over (var, nat_to_real $ a))
                       |> Term.lambda var
          val t2 = (Term.abstract_over (var, nat_to_real $ b))
                       |> Term.lambda var
          val (th1, th2) = apply2 (asym_bound2_th ctxt) (t1, t2)
        in
          ([th1, th2] MRS @{thm bigtheta_mult})
              |> apply_to_thm' (Conv.arg_conv (reduce_poly_log2_times ctxt))
              |> eta_contract
        end
      else if not (Util.is_subterm (snd_nat_t $ var) body') then
        (* Only n appears *)
        let
          val abs = Term.abstract_over (fst_nat_t $ var, nat_to_real $ body')
          val t1 = Term.lambda var abs
          val th1 = asym_bound_th ctxt t1
        in
          (th1 RS @{thm mult_Theta_bivariate1})
              |> apply_to_thm' (Conv.arg_conv Thm.eta_conversion)
        end
      else if not (Util.is_subterm (fst_nat_t $ var) body') then
        (* Only m appears *)
        let
          val abs = Term.abstract_over (snd_nat_t $ var, nat_to_real $ body')
          val t2 = Term.lambda var abs
          val th2 = asym_bound_th ctxt t2
        in
          (th2 RS @{thm mult_Theta_bivariate2})
              |> apply_to_thm' (Conv.arg_conv Thm.eta_conversion)
        end
      else
        (* Registered function case *)
        let
          val (f, args) = Term.strip_comb body'
          val norm_asym2 = apply_to_thm' (
                Conv.arg_conv (Conv.arg_conv (norm_poly_log2_abs ctxt)))
        in
          if length args = 1 andalso is_prod (the_single args) then
            let
              val (nm, _) = Term.dest_Const f
              val th_f =
                  case find_asym_bound thy nm of
                      NONE => raise Fail "Asymptotic bound not found."
                    | SOME th => th |> eta_contract |> norm_asym2
              val arg = the_single args
              val (arg1, arg2) = HOLogic.dest_prod arg
              val _ = assert (
                    not (Util.is_subterm (snd_nat_t $ var) arg1) andalso
                    not (Util.is_subterm (fst_nat_t $ var) arg2))
                             "asym_bound2_th: not in the form f (g_1 m, g_2 n)."
              val t1 = (Term.abstract_over (fst_nat_t $ var, nat_to_real $ arg1))
                           |> Term.lambda var
              val t2 = (Term.abstract_over (snd_nat_t $ var, nat_to_real $ arg2))
                           |> Term.lambda var
              val th1 = asym_bound_th ctxt t1
              val th2 = asym_bound_th ctxt t2
              val g1 = dest_arg (bd_of_th th_f)
              val stable2_g1 = stable2_th ctxt g1
              val event_mono2_g1 = event_mono2_th ctxt g1
            in
              ([stable2_g1, event_mono2_g1, th_f, th1, th2]
                   MRS @{thm bigTheta2_compose_both_linear'})
                  |> apply_to_thm' (Conv.arg_conv Thm.eta_conversion)
            end
          else
            raise Fail "compose2_th: registered function case"
        end
    end

(* Derive a theorem of the form t : \Theta_2(goal). This works by first finding
   the asymptotic bound of t using asym_bound2_th, then compare that bound to
   the normalized form of goal. *)
fun asym_bound2_gen ctxt (ct, goal) =
    let
      val th = asym_bound2_th ctxt (Thm.term_of ct)
      val cv = Conv.every_conv [Conv.arg_conv (norm_poly_log2_abs ctxt),
                                reduce_poly_log2_all ctxt]
      val goal_th = cv (Thm.cterm_of ctxt goal)
    in
      if Util.rhs_of goal_th aconv bd_of_th th then
        th |> apply_to_thm' (Conv.arg_conv (Conv.rewr_conv (meta_sym goal_th)))
      else let
        val _ = trace_t ctxt "Produced asym bound: " (bd_of_th th)
        val _ = trace_t ctxt "Needed asym bound: " (Util.rhs_of goal_th)
      in
        raise Fail "asym_bound2_gen"
      end
    end

val asym_bound2_prfstep =
    ProofStep.prfstep_custom
        "asym_bound2"
        [WithItem (TY_PROP,
                   @{term_pat "~((?f::nat*nat=>real) : \<Theta>\<^sub>2(?g))"})]
        (fn ((id, _), ths) => fn _ => fn ctxt =>
            let
              val th = the_single ths
              val (t, goal) = th |> prop_of' |> dest_not |> Util.dest_binop_args
              val res = asym_bound2_gen ctxt (Thm.cterm_of ctxt t, goal)
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

val add_asym_bound2_proofsteps =
    fold add_prfstep [
      asym_bound2_prfstep
    ]

end  (* structure LandauUtil2D *)

val _ = Theory.setup LandauUtil2D.add_asym_bound2_proofsteps
