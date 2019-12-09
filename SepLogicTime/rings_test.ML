(* Unit test for rings *)

local

  val ts = map (fn x => Free (x, natT)) ["a", "b", "c", "m", "n"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

fun test_term ctxt f err_str (str1, str2) =
    let
      val (t1, t2) = (Proof_Context.read_term_pattern ctxt str1,
                      Proof_Context.read_term_pattern ctxt str2)
      val t2' = f t1
    in
      if t2 aconv t2' then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" t2'
      in
        raise Fail err_str
      end
    end

val test =
    let
      val test_data = [
        (* No repeated terms. *)
        ("a", "a"),
        ("a + b", "a + b"),

        (* Numerical constants (on one side only). *)
        ("0::nat", "0::nat"),
        ("2::nat", "2::nat"),
        ("a + 2 + 3", "a + 5"),
        ("2 + 3 + a", "a + 5"),

        (* Monomial *)
        ("a * 3", "a * 3"),
        ("3 * a", "a * 3"),
        ("a * b + b * a", "a * b * 2"),

        (* Cancellation between terms *)
        ("a * 3 + a * 2", "a * 5"),

        (* Distributivity *)
        ("(a + 2) * b", "b * 2 + a * b"),
        ("(a + 2) * 2", "a * 2 + 4")
      ]
    in
      map (Util.test_conv ctxt NatRing.norm_full "test") test_data @
      map (test_term ctxt NatRing.norm_ring_term "test_t") test_data
    end

end
