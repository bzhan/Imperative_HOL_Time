(* Wrapper for Master theorem *)

fun read_term_with_type ctxt T = Syntax.check_term ctxt o Type.constraint T o Syntax.parse_term ctxt

fun parse_assoc key scan = Scan.lift (Args.$$$ key -- Args.colon) -- scan >> snd

val parse_param =
    let
      fun term_with_type T =
          Scan.peek (fn context => Args.embedded_inner_syntax >>
                        read_term_with_type (Context.proof_of context) T);
    in
      parse_assoc "recursion" Attrib.thm >> (fn x => (SOME x, NONE, NONE, NONE, NONE)) ||
                  parse_assoc "x0" (term_with_type HOLogic.natT) >> (fn x => (NONE, SOME x, NONE, NONE, NONE)) ||
                  parse_assoc "x1" (term_with_type HOLogic.natT) >> (fn x => (NONE, NONE, SOME x, NONE, NONE)) ||
                  parse_assoc "p'" (term_with_type HOLogic.realT) >> (fn x => (NONE, NONE, NONE, SOME x, NONE)) ||
                  parse_assoc "rew" Attrib.thms >> (fn x => (NONE, NONE, NONE, NONE, SOME x))
    end

val parse_params =
    let
      fun add_option NONE y = y
        | add_option x _ = x
      fun go (a,b,c,d,e) (a',b',c',d',e') =
          (add_option a a', add_option b b', add_option c c', add_option d d', add_option e e')
    in
      Scan.repeat parse_param >> (fn xs => fold go xs (NONE, NONE, NONE, NONE, NONE))
    end

fun master_theorem_tac_wrapper caseno simp x0 x1 p' ctxt rewrites thm someint =
    let
      val rewrites = these rewrites
      val rec_th = the thm
      val rec_th' = LandauUtil.runtime_rec_th
                        ctxt rec_th (hd rewrites) (tl rewrites)
      val _ = trace_thm ctxt "rec_th'" rec_th'
    in
      (fn goal => let
         val res = Akra_Bazzi.master_theorem_tac
                       caseno simp (SOME rec_th') x0 x1 p' ctxt someint goal
         val lres = Seq.list_of res
       in
         if null lres then res else
         let
           val res_th = hd lres |> Thm.permute_prems 0 1
           val _ = trace_thm ctxt "res" res_th
           val subgoals = Thm.prems_of res_th
           val goal2 = nth subgoals 0
           val _ = trace_t ctxt "goal2" goal2
           val cvar = (Term.add_vars (Thm.prop_of rec_th') [])
                         |> the_single |> Var |> Thm.cterm_of ctxt
           val thm2 = Thm.forall_intr cvar rec_th'
           val _ = trace_thm ctxt "thm2" thm2
           val _ = assert (goal2 aconv (Thm.prop_of thm2)) "no match"
           val res_th' = Thm.implies_elim res_th thm2
         in
           Seq.single res_th'
         end
       end)
    end


val setup_master_theorem =
    Scan.option (Scan.lift (Parse.number || Parse.float_number))
      -- Scan.lift (Args.parens (Args.$$$ "nosimp") >> K false || Scan.succeed true)
      -- parse_params
      >>
      (fn ((caseno, simp), (thm, x0, x1, p', rewrites)) => fn ctxt =>
          let
            val _ =
                case caseno of
                    SOME caseno =>
                    if member (op =) ["1","2.1","2.2","2.3","3"] caseno then
                      ()
                    else
                      cat_error "illegal Master theorem case: " caseno
                  | NONE => ()
          in
            SIMPLE_METHOD' (master_theorem_tac_wrapper caseno simp x0 x1 p' ctxt rewrites thm)
          end)
