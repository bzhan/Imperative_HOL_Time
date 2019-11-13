
local

  val ctxt = @{context}

in

val bigtheta = LandauUtil.bigtheta
val bigtheta2 = LandauUtil2D.bigtheta2
val smallo = @{term "o(b::nat=>real)"} |> Term.dest_comb |> fst
val smallo2 = @{term "o\<^sub>2(b::nat*nat=>real)"} |> Term.dest_comb |> fst

val test_norm_poly_log =
    let
      val test_data = [
        ("%x::nat. (1::real)", "polylog 0 0"),
        ("%x::nat. real 1", "polylog 0 0"),
        ("%x. real x", "polylog 1 0"),
        ("%x. real (x ^ a)", "polylog a 0"),
        ("%x. ln (real x)", "polylog 0 1"),
        ("%x. ln (real x) ^ b", "polylog 0 b"),
        ("%x. real x * ln (real x)", "polylog 1 1"),
        ("%x. real (x ^ 2) * ln (real x) ^ 3", "polylog 2 3"),
        ("%x. real x * real x", "polylog 2 0"),
        ("%x. ln (real x) * real x", "polylog 1 1"),
        ("%x. real x + real x", "polylog 1 0 + polylog 1 0"),
        ("%x. real x + ln (real x) + real (x ^ 2)",
         "polylog 1 0 + polylog 0 1 + polylog 2 0")
      ]
    in
      map (Util.test_conv ctxt (LandauUtil.norm_poly_log_abs ctxt)
                          "test_norm_poly_log") test_data
    end

val test_norm_poly_log2 =
    let
      val test_data = [
        ("%(x::nat*nat). real 1", "polylog2 0 0 0 0"),
        ("%(x::nat*nat). real (fst x)", "polylog2 1 0 0 0"),
        ("%(x::nat*nat). real (snd x)", "polylog2 0 0 1 0"),
        ("%x. real (fst x) * real (snd x)", "polylog2 1 0 1 0"),
        ("%x. real (snd x) * real (fst x)", "polylog2 1 0 1 0"),
        ("%x. real (fst x * snd x)", "polylog2 1 0 1 0"),
        ("%x. real ((fst x) ^ 2 * (snd x) ^ 3)", "polylog2 2 0 3 0")
      ]
    in
      map (Util.test_conv ctxt (LandauUtil2D.norm_poly_log2_abs ctxt)
                          "test_norm_poly_log2") test_data
    end

fun test_compare ctxt f smallo (str1, str2) =
    let
      val (t1, t2) = apply2 (Syntax.read_term ctxt) (str1, str2)
      val (ord, th) = the (f ctxt (t1, t2))
      val goal = case ord of
                     LESS => mk_Trueprop (mk_mem (t1, smallo $ t2))
                   | GREATER => mk_Trueprop (mk_mem (t2, smallo $ t1))
                   | EQUAL => Logic.mk_equals (t1, t2)
    in
      if goal aconv Thm.prop_of th then ()
      else let
        val _ = trace_t ctxt "Expected" goal
        val _ = trace_t ctxt "Actual" (Thm.prop_of th)
      in
        raise Fail "test_compare_poly_log"
      end
    end

val test_compare_poly_log =
    let
      val test_data = [
        ("polylog 0 0", "polylog 0 1"),
        ("polylog 0 1", "polylog 1 0"),
        ("polylog 1 0", "polylog 1 1"),
        ("polylog 1 1", "polylog 2 0"),
        ("polylog 1 0", "polylog 0 1"),
        ("polylog 1 1", "polylog 1 1")
      ]
    in
      map (test_compare ctxt LandauUtil.compare_poly_log smallo) test_data
    end

val test_compare_poly_log2 =
    let
      val test_data = [
        ("polylog2 0 0 0 0", "polylog2 0 0 0 0"),
        ("polylog2 0 1 0 1", "polylog2 0 1 0 1"),
        ("polylog2 0 0 0 0", "polylog2 0 0 0 1"),
        ("polylog2 0 0 0 1", "polylog2 0 0 0 0"),
        ("polylog2 0 0 0 0", "polylog2 0 1 0 0"),
        ("polylog2 0 1 0 0", "polylog2 0 0 0 0"),
        ("polylog2 0 0 0 0", "polylog2 0 1 0 1"),
        ("polylog2 0 1 0 1", "polylog2 0 0 0 0")
      ]
    in
      map (test_compare ctxt LandauUtil2D.compare_poly_log2 smallo2) test_data
    end

fun test_theta_conv ctxt cv bigtheta err_str (str1, str2) =
    let
      val (t1, t2) = (bigtheta $ Proof_Context.read_term_pattern ctxt str1,
                      bigtheta $ Proof_Context.read_term_pattern ctxt str2)
      val th = cv (Thm.cterm_of ctxt t1)
    in
      if t1 aconv (Util.lhs_of th) andalso t2 aconv (Util.rhs_of th) then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" (Thm.prop_of th)
      in
        raise Fail err_str
      end
    end

val test_reduce_poly_log_sum =
    let
      val test_data = [
        ("polylog 0 0 + polylog 0 0", "polylog 0 0"),
        ("polylog 0 0 + polylog 0 1", "polylog 0 1"),
        ("polylog 0 1 + polylog 0 0", "polylog 0 1"),
        ("polylog 1 0 + polylog 0 1", "polylog 1 0"),
        ("polylog 1 1 + polylog 2 0", "polylog 2 0"),
        ("polylog 0 1 + polylog 0 2 + polylog 0 3", "polylog 0 3"),
        ("polylog 0 3 + polylog 0 2 + polylog 0 1", "polylog 0 3")
      ]
    in
      map (test_theta_conv ctxt (LandauUtil.reduce_poly_log_sum ctxt) bigtheta
                           "reduce_poly_log_sum") test_data
    end

val test_reduce_poly_log_all =
    let
      val test_data = [
        ("%x. real x", "polylog 1 0"),
        ("%x. real x + real x", "polylog 1 0"),
        ("%x. real x + real 1", "polylog 1 0"),
        ("%x. real x + (1::real)", "polylog 1 0"),
        ("%x. real x + real (x ^ 2) + ln (real x)", "polylog 2 0"),
        ("%x. real x * real x + ln (real x)", "polylog 2 0")
      ]
    in
      map (test_theta_conv ctxt (LandauUtil.reduce_poly_log_all ctxt) bigtheta
                           "reduce_poly_log_all") test_data
    end

val test_reduce_poly_log2_plus1 =
    let
      val test_data = [
        ("polylog2 1 0 0 0 + polylog2 0 0 1 0",
         "polylog2 1 0 0 0 + polylog2 0 0 1 0"),
        ("polylog2 1 0 0 0 + polylog2 0 0 1 0 + polylog2 1 0 1 0",
         "polylog2 1 0 1 0"),
        ("polylog2 1 0 0 0 + polylog2 0 0 1 0 + polylog2 2 0 0 0",
         "polylog2 0 0 1 0 + polylog2 2 0 0 0")
      ]
    in
      map (test_theta_conv ctxt (LandauUtil2D.reduce_poly_log2_plus1 ctxt)
                           bigtheta2 "reduce_poly_log2_plus1") test_data
    end

val test_reduce_poly_log2_all =
    let
      val test_data = [
        ("%(x::nat*nat). real (fst x)", "polylog2 1 0 0 0"),
        ("%(x::nat*nat). real (fst x) + real ((fst x) ^ 2)", "polylog2 2 0 0 0"),
        ("%x. ln (real (fst x)) + ln (real (fst x)) * ln (real (snd x))",
         "polylog2 0 1 0 1"),
        ("%(x::nat*nat). real 1 + (1::real) + real 1", "polylog2 0 0 0 0"),
        ("%x. real (fst x * snd x) + real (fst x) * real (snd x) + real 1",
         "polylog2 1 0 1 0"),
        ("%x. real (fst x) + real (snd x)",
         "polylog2 1 0 0 0 + polylog2 0 0 1 0"),
        ("%x. real (fst x * snd x) + real (fst x) + real (snd x)",
         "polylog2 1 0 1 0"),
        ("%x. real (fst x) + real (snd x) + real (fst x * snd x)",
         "polylog2 1 0 1 0"),
        (* %(n,m) input *)
        ("%(n,m). real n * real m", "polylog2 1 0 1 0")
      ]

      val cv = Conv.every_conv [
            Conv.arg_conv (LandauUtil2D.norm_poly_log2_abs ctxt),
            LandauUtil2D.reduce_poly_log2_all ctxt]
    in
      map (test_theta_conv ctxt cv bigtheta2 "reduce_poly_log2_all") test_data
    end

fun test_asym_bound ctxt f bigtheta (str1, str2) =
    let
      val t = Syntax.read_term ctxt str1
      val bd = Syntax.read_term ctxt str2
      val res = f ctxt t
    in
      if not (dest_arg1 (prop_of' res) aconv t) then
        let
          val _ = trace_t ctxt "Expected:" t
          val _ = trace_t ctxt "Actual:" (dest_arg1 (prop_of' res))
        in
          raise Fail "test_asym_bound: t"
        end
      else if not (dest_arg (prop_of' res) aconv (bigtheta $ bd)) then
        let
          val _ = trace_t ctxt "Expected:" (bigtheta $ bd)
          val _ = trace_t ctxt "Actual:" (dest_arg (prop_of' res))
        in
          raise Fail "test_asym_bound: bd"
        end
      else ()
    end

val test_asym_bound_th =
    let
      val c = "polylog 0 0"
      val log = "polylog 0 1"
      val n = "polylog 1 0"
      val n2 = "polylog 2 0"
      val n3 = "polylog 3 0"

      val test_data = [
        ("%x::nat. real 1", c),
        ("%x::nat. real 3", c),
        ("%x. real x", n),
        ("%x. real (3 * x)", n),
        ("%x. real (x * x)", "polylog 2 0"),
        ("%x. real (2 * x + 1)", n),
        ("%x. real (f x)", n),
        ("%x. real (f (x + 1))", n),
        ("%x. real (f (x + 3 * x + 1) + 1)", n),
        ("%x. real (f x * x)", n2),
        ("%x. real (1 + x + f x * x + x * f x * x)", n3),

        ("%x. real (f x + g x)", n),
        ("%x. real (3 * f x + 2 * g x)", n),
        ("%x. real (x div 2)", n),
        ("%x. real (f (x div 2))", n),
        ("%x. real (f (((x + 1) div 2) + (x div 2) + 3 * x + 5))", n),
        ("%x. real (flog (x + 1))", log),

        ("%x. real (x - 1)", n),
        ("%x. real (f x - g x)", n)
      ]
    in
      map (test_asym_bound ctxt LandauUtil.asym_bound_th bigtheta) test_data
    end

val test_asym_bound2_th =
    let
      val nm = "polylog2 1 0 1 0"
      val npm = "polylog2 1 0 0 0 + polylog2 0 0 1 0"
      val npm' = "polylog2 0 0 1 0 + polylog2 1 0 0 0"
      val n = "polylog2 1 0 0 0"
      val m = "polylog2 0 0 1 0"
      val c = "polylog2 0 0 0 0"

      val test_data = [
        ("%x::(nat*nat). real 1", c),
        ("%x::(nat*nat). real (fst x)", n),
        ("%x::(nat*nat). real (snd x)", m),
        ("%x. real (fst x * snd x)", nm),

        (* Composition cases *)
        ("%x. real (f_prod (fst x, snd x + 1))", nm),
        ("%x. real (f_prod (fst x + 1, snd x))", nm),
        ("%x. real (f_prod (fst x + 1, snd x + 1))", nm),

        (* Product case *)
        ("%x. real (f (fst x) * f (snd x))", nm),
        ("%x. real (f (fst x + 1) * f (snd x + 1))", nm),
        ("%x. real (f (fst x) * g (snd x))", n),
        ("%x. real (g (fst x) * f (snd x))", m),
        ("%x::(nat*nat). real (f (fst x))", n),
        ("%x::(nat*nat). real (f (snd x))", m),
        ("%x::(nat*nat). real (f (5 * snd x + 1))", m),

        (* Sum case *)
        ("%x. real (f_prod (fst x, snd x) + 1)", nm),
        ("%x. real (f_prod (fst x + 1, snd x + 1) + 1)", nm),
        ("%x. real (f_sum (fst x, snd x))", npm),
        ("%x. real (f_sum (fst x + 1, snd x + 1) + 1)", npm'),
        ("%x. real (f_prod (fst x, snd x) + f_sum (fst x, snd x))", nm)
      ]
    in
      map (test_asym_bound ctxt LandauUtil2D.asym_bound2_th bigtheta2) test_data
    end

end
