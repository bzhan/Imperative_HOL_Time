(* Utility functions for timed version. *)

signature SEP_TIME_UTIL =
sig
  val is_time_credit: term -> bool
  val dest_time_credit: term -> term
  val mk_time_credit: term -> term
end;

structure SepTimeUtil : SEP_TIME_UTIL =
struct

fun is_time_credit t =
    case t of
        Const (@{const_name timeCredit_assn}, _) $ _ => true
      | _ => false

fun dest_time_credit t =
    case t of
        Const (@{const_name timeCredit_assn}, _) $ n => n
      | _ => raise Fail "dest_time_credit: unexpected t."

fun mk_time_credit n =
    Const (@{const_name timeCredit_assn}, natT --> @{typ assn}) $ n

end  (* structure SepTimeUtil *)
