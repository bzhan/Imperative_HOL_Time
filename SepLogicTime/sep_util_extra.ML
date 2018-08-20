(* Instantiation-dependent functions . *)

structure SepUtilExtra : SEP_UTIL_EXTRA =
struct

open SepUtil
open SepTimeUtil

fun is_case_prod t =
    case t of
        Const (@{const_name case_prod}, _) $ _ $ _ => true
      | _ => false

fun combine_time_credit1 ct =
    Conv.every_conv [
      rewr_obj_eq (obj_sym @{thm time_credit_add}),
      Conv.arg_conv NatRing.norm_full] ct

fun sort_by t =
    case t of
        Const (@{const_name pure_assn}, _) $ _ => 3
      | Const (@{const_name top_assn}, _) => 2
      | Const (@{const_name timeCredit_assn}, _) $ _ => 1
      | _ => 0

fun pure_ord (t, s) =
    if sort_by t = 0 andalso sort_by s = 0 then
      Term_Ord.term_ord (t, s) = LESS
    else
      sort_by t < sort_by s

fun normalize_times_cv ctxt ct =
    let
      val (A, B) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_ex_assn A then
        Conv.every_conv [rewr_obj_eq (obj_sym @{thm ex_distrib_star}),
                         Conv.binder_conv (normalize_times_cv o snd) ctxt] ct
      else if is_ex_assn B then
        Conv.every_conv [ACUtil.comm_cv assn_ac_info,
                         normalize_times_cv ctxt] ct
      else
        Conv.every_conv [
          ACUtil.normalize_au assn_ac_info,
          ACUtil.normalize_comm_gen assn_ac_info pure_ord,
          ACUtil.norm_combine assn_ac_info SepUtil.is_true_assn
                              (rewr_obj_eq @{thm top_assn_reduce}),
          ACUtil.norm_combine assn_ac_info is_time_credit
                              combine_time_credit1] ct
    end

(* Normalization function for assertions. This function pulls all EX_A
   to the front, then apply AC-rules to the inside, putting all pure
   assertions on the right.
 *)
fun normalize_assn_cv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_ex_assn t then
        Conv.binder_conv (normalize_assn_cv o snd) ctxt ct
      else if t aconv @{term "$0"} then
        rewr_obj_eq @{thm zero_time} ct
      else if UtilArith.is_times t then
        Conv.every_conv [Conv.binop_conv (normalize_assn_cv ctxt),
                         normalize_times_cv ctxt] ct
      else if is_pure_assn t andalso is_conj (dest_arg t) then
        Conv.every_conv [rewr_obj_eq @{thm pure_conj},
                         normalize_assn_cv ctxt] ct
      else if is_case_prod t then
        Conv.every_conv [rewr_obj_eq @{thm case_prod_beta},
                         normalize_assn_cv ctxt] ct
      else if is_time_credit t then
        Conv.arg_conv NatRing.norm_full ct
      else
        Conv.all_conv ct
    end

val times_ac_info = Nat_Util.times_ac_on_typ @{theory} natT
val plus_ac_info = Nat_Util.plus_ac_on_typ @{theory} natT

(* Rewrite terms for P in the form $(n). *)
fun time_credit_rewr_terms P =
    P |> dest_arg
      |> ACUtil.dest_ac plus_ac_info
      |> maps (ACUtil.dest_ac times_ac_info)
      |> filter_out UtilArith.is_numc

fun atomic_rewr_terms P =
    if is_time_credit P then
      time_credit_rewr_terms P
    else
      P |> Term.strip_comb |> snd

(* Rewrite terms for an assertion *)
fun assn_rewr_terms P =
    P |> ACUtil.dest_ac assn_ac_info
      |> filter_out is_pure_assn
      |> maps atomic_rewr_terms
      |> distinct (op aconv)

end  (* structure AssnNorm. *)
