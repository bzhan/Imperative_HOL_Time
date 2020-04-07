(* Unit test for sep_times_steps.ML. *)

local
  open SepUtil
  open SepTimeSteps
  val ctxt = @{context}
in

val test_normalize_time =
    let
      val ctxt' = ctxt |> fold Proof_Context.augment [
            Free ("P", assnT), Free ("S", natT --> assnT),
            Free ("T", natT --> assnT)]
      val test = Util.test_conv ctxt' (SepUtil.normalize_assn_cv ctxt')
                                "normalize_assn"

      val test_data = [
        ("$1 * $2", "$3"),
        ("$n * $1", "$(n + 1)"),
        ("$1 * $2 * $3", "$6"),
        ("$1 * true * $2 * true * \<up>b", "$3 * true * \<up>b")
      ]
    in
      map test test_data
    end

end
