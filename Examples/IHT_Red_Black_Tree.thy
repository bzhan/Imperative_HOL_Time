(* Verification of imperative red-black trees. *)

theory IHT_Red_Black_Tree
  imports
    Auto2_Imperative_HOL.RBTree
    "../SepLogicTime/SLTC_Main"
    "../Asymptotics/Asymptotics_2D"
begin

section \<open>Tree nodes\<close>

datatype ('a, 'b) rbt_node =
  Node (lsub: "('a, 'b) rbt_node ref option") (cl: color) (key: 'a) (val: 'b) (rsub: "('a, 'b) rbt_node ref option")
setup \<open>fold add_rewrite_rule @{thms rbt_node.sel}\<close>

fun color_encode :: "color \<Rightarrow> nat" where
  "color_encode B = 0"
| "color_encode R = 1"

instance color :: heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "color_encode"])
  apply (metis color_encode.simps(1) color_encode.simps(2) not_B zero_neq_one)
  ..

fun rbt_node_encode :: "('a::heap, 'b::heap) rbt_node \<Rightarrow> nat" where
  "rbt_node_encode (Node l c k v r) = to_nat (l, c, k, v, r)"

instance rbt_node :: (heap, heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "rbt_node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun btree :: "('a::heap, 'b::heap) rbt \<Rightarrow> ('a, 'b) rbt_node ref option \<Rightarrow> assn" where
  "btree Leaf p = \<up>(p = None)"
| "btree (rbt.Node lt c k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp)"
| "btree (rbt.Node lt c k v rt) None = false"
setup \<open>fold add_rewrite_ent_rule @{thms btree.simps}\<close>

lemma btree_Leaf [forward_ent]: "btree Leaf p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma btree_Node [forward_ent]:
  "btree (rbt.Node lt c k v rt) p \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. the p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp * \<up>(p \<noteq> None))"
@proof @case "p = None" @qed

lemma btree_none: "emp \<Longrightarrow>\<^sub>A btree Leaf None" by auto2

lemma btree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (rbt.Node lt c k v rt) (Some p)" by auto2

setup \<open>fold add_entail_matcher [@{thm btree_none}, @{thm btree_constr_ent}]\<close>
setup \<open>fold del_prfstep_thm @{thms btree.simps}\<close>

type_synonym ('a, 'b) btree = "('a, 'b) rbt_node ref option"

section \<open>Operations\<close>

subsection \<open>Basic operations\<close>

definition tree_empty :: "('a, 'b) btree Heap" where
  "tree_empty = return None"

lemma tree_empty_rule [hoare_triple]:
  "<$1> tree_empty <btree Leaf>" by auto2

definition tree_is_empty :: "('a, 'b) btree \<Rightarrow> bool Heap" where
  "tree_is_empty b = return (b = None)"

lemma tree_is_empty_rule:
  "<btree t b * $1> tree_is_empty b <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Leaf)>" by auto2

definition btree_constr ::
  "('a::heap, 'b::heap) btree \<Rightarrow> color \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_constr lp c k v rp = do { p \<leftarrow> ref (Node lp c k v rp); return (Some p) }"

lemma btree_constr_rule [hoare_triple]:
  "<btree lt lp * btree rt rp * $2>
   btree_constr lp c k v rp
   <btree (rbt.Node lt c k v rt)>" by auto2

definition set_color :: "color \<Rightarrow> ('a::heap, 'b::heap) btree \<Rightarrow> unit Heap" where
  "set_color c p = (case p of
    None \<Rightarrow> raise ''set_color''
  | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      pp := Node (lsub t) c (key t) (val t) (rsub t)
    })"

lemma set_color_rule [hoare_triple]:
  "<btree (rbt.Node a c x v b) p * $2>
   set_color c' p
   <\<lambda>_. btree (rbt.Node a c' x v b) p>\<^sub>t" by auto2

definition get_color :: "('a::heap, 'b::heap) btree \<Rightarrow> color Heap" where
  "get_color p = (case p of
     None \<Rightarrow> return B
   | Some pp \<Rightarrow> do {
       t \<leftarrow> !pp;
       return (cl t)
     })"

lemma get_color_rule [hoare_triple]:
  "<btree t p * $2> get_color p <\<lambda>r. btree t p * \<up>(r = rbt.cl t)>\<^sub>t"
@proof @case "t = Leaf" @qed

definition paint :: "color \<Rightarrow> ('a::heap, 'b::heap) btree \<Rightarrow> unit Heap" where
  "paint c p = (case p of
    None \<Rightarrow> return ()
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     pp := Node (lsub t) c (key t) (val t) (rsub t)
   })"
  
lemma paint_rule [hoare_triple]:
  "<btree t p *$2>
   paint c p
   <\<lambda>_. btree (RBTree.paint c t) p>\<^sub>t"
@proof @case "t = Leaf" @qed

subsection \<open>Rotation\<close>

definition btree_rotate_l :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_rotate_l p = (case p of
    None \<Rightarrow> raise ''Empty btree''
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     (case rsub t of
        None \<Rightarrow> raise ''Empty rsub''
      | Some rp \<Rightarrow> do {
          rt \<leftarrow> !rp;
          pp := Node (lsub t) (cl t) (key t) (val t) (lsub rt);
          rp := Node p (cl rt) (key rt) (val rt) (rsub rt);
          return (rsub t) })})"

lemma btree_rotate_l_rule [hoare_triple]:
  "<btree (rbt.Node a c1 x v (rbt.Node b c2 y w c)) p * $5>
   btree_rotate_l p
   <btree (rbt.Node (rbt.Node a c1 x v b) c2 y w c)>\<^sub>t" by auto2

definition btree_rotate_r :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_rotate_r p = (case p of
    None \<Rightarrow> raise ''Empty btree''
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     (case lsub t of
        None \<Rightarrow> raise ''Empty lsub''
      | Some lp \<Rightarrow> do {
          lt \<leftarrow> !lp;
          pp := Node (rsub lt) (cl t) (key t) (val t) (rsub t);
          lp := Node (lsub lt) (cl lt) (key lt) (val lt) p;
          return (lsub t) })})"

definition btree_rotate_r_time :: "nat" where [rewrite]: "btree_rotate_r_time = 5"

lemma btree_rotate_r_rule [hoare_triple]:
  "<btree (rbt.Node (rbt.Node a c1 x v b) c2 y w c) p * $5>
   btree_rotate_r p
   <btree (rbt.Node a c1 x v (rbt.Node b c2 y w c))>" by auto2

lemma btree_rotate_r_time_bound [asym_bound]:
  "(\<lambda>n::nat. btree_rotate_r_time) \<in> \<Theta>(\<lambda>n. 1)"
  apply (simp only: btree_rotate_r_time_def) by auto2

subsection \<open>Balance\<close>

definition btree_balanceR :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_balanceR p = (case p of None \<Rightarrow> return None | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     cl_r \<leftarrow> get_color (rsub t);
     if cl_r = R then do {
       rt \<leftarrow> !(the (rsub t));
       cl_lr \<leftarrow> get_color (lsub rt);
       cl_rr \<leftarrow> get_color (rsub rt);
       if cl_lr = R then do {
         rp' \<leftarrow> btree_rotate_r (rsub t);
         pp := Node (lsub t) (cl t) (key t) (val t) rp';
         p' \<leftarrow> btree_rotate_l p;
         t' \<leftarrow> !(the p');
         set_color B (rsub t');
         return p'
       } else if cl_rr = R then do {
         p' \<leftarrow> btree_rotate_l p;
         t' \<leftarrow> !(the p');
         set_color B (rsub t');
         return p'
        } else return p }
     else return p})"

definition btree_balanceR_time :: "nat" where [rewrite]:
  "btree_balanceR_time = 24"

lemma balanceR_to_fun [hoare_triple]:
  "<btree (rbt.Node l B k v r) p * $24>
   btree_balanceR p
   <btree (balanceR l k v r)>\<^sub>t"
@proof @unfold "balanceR l k v r" @qed

definition btree_balance :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_balance p = (case p of None \<Rightarrow> return None | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     cl_l \<leftarrow> get_color (lsub t);
     if cl_l = R then do {
       lt \<leftarrow> !(the (lsub t));
       cl_rl \<leftarrow> get_color (rsub lt);
       cl_ll \<leftarrow> get_color (lsub lt);
       if cl_ll = R then do {
         p' \<leftarrow> btree_rotate_r p;
         t' \<leftarrow> !(the p');
         set_color B (lsub t');
         return p' }
       else if cl_rl = R then do {
         lp' \<leftarrow> btree_rotate_l (lsub t);
         pp := Node lp' (cl t) (key t) (val t) (rsub t);
         p' \<leftarrow> btree_rotate_r p;
         t' \<leftarrow> !(the p');
         set_color B (lsub t');
         return p'
       } else btree_balanceR p }
     else do {
       p' \<leftarrow> btree_balanceR p;
       return p'}})"
declare [[print_trace]]

lemma balance_to_fun [hoare_triple]:
  "<btree (rbt.Node l B k v r) p * $32>
   btree_balance p
   <btree (balance l k v r)>\<^sub>t"
@proof @unfold "balance l k v r" @qed

subsection \<open>Insertion\<close>

partial_function (heap_time) rbt_ins ::
  "'a::{heap,ord} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_ins k v p = (case p of
     None \<Rightarrow> btree_constr None R k v None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      (if cl t = B then
        (if k = key t then do {
           pp := Node (lsub t) (cl t) k v (rsub t);
           return (Some pp) }
         else if k < key t then do {
           q \<leftarrow> rbt_ins k v (lsub t);
           pp := Node q (cl t) (key t) (val t) (rsub t);
           btree_balance p }
         else do {
           q \<leftarrow> rbt_ins k v (rsub t);
           pp := Node (lsub t) (cl t) (key t) (val t) q;
           btree_balance p })
       else
        (if k = key t then do {
           pp := Node (lsub t) (cl t) k v (rsub t);
           return (Some pp) }
         else if k < key t then do {
           q \<leftarrow> rbt_ins k v (lsub t);
           pp := Node q (cl t) (key t) (val t) (rsub t);
           return (Some pp) }
         else do {
           q \<leftarrow> rbt_ins k v (rsub t);
           pp := Node (lsub t) (cl t) (key t) (val t) q;
           return (Some pp) }))})"



fun rbt_ins_time' :: "('a, 'b) rbt \<Rightarrow> 'a::ord \<Rightarrow> nat" where
    "rbt_ins_time' Leaf k = 4"
  | "rbt_ins_time' (rbt.Node l c ka va r) k = (if c=B
       then
       (if k=ka then 4 else (if k<ka then 50 + rbt_ins_time' l k else 100 + rbt_ins_time' r k)) 
        else
       (if k=ka then 4 else (if k<ka then 100 + rbt_ins_time' l k else 100 + rbt_ins_time' r k)) ) "
setup \<open>fold add_rewrite_rule @{thms rbt_ins_time'.simps}\<close>


lemma rbt_ins_to_fun'[hoare_triple]: 
  "<btree t p *  $(rbt_ins_time' t k)>
   rbt_ins k v p
   <btree (ins k v t)>\<^sub>t"
@proof @induct t arbitrary p @qed


definition rbt_ins_time :: "nat \<Rightarrow> nat" where
    "rbt_ins_time n = 400 * n + 4"

lemma rbt_ins_time'[resolve]: "rbt_ins_time' t k \<le> rbt_ins_time (max_depth t)"
  by (induct t, auto simp: rbt_ins_time_def) 

lemma rbt_ins_to_fun[hoare_triple]:
  "<btree t p * $(rbt_ins_time (max_depth t))>
   rbt_ins k v p
   <btree (ins k v t)>\<^sub>t"
@proof
  @have "(rbt_ins_time (max_depth t)) \<ge>\<^sub>t rbt_ins_time' t k"
@qed
 
definition rbt_insert ::
  "'a::{heap,ord} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_insert k v p = do {
    p' \<leftarrow> rbt_ins k v p;
    paint B p';
    return p' }"


definition rbt_insert_time :: "nat \<Rightarrow> nat" where [rewrite]:
    "rbt_insert_time n = rbt_ins_time n + 4"

lemma rbt_insert_to_fun [hoare_triple]:
  "<btree t p * $(rbt_insert_time (max_depth t))>
   rbt_insert k v p
   <btree (RBTree.rbt_insert k v t)>\<^sub>t" by auto2

subsection \<open>Search\<close>
 
partial_function (heap_time) rbt_search ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> 'b option Heap" where
  "rbt_search x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = key t then return (Some (val t))
       else if x < key t then rbt_search x (lsub t)
       else rbt_search x (rsub t)) })"


fun rbt_search_time' :: "('a, 'b) rbt \<Rightarrow> 'a::ord \<Rightarrow> nat" where
    "rbt_search_time' Leaf k = 1"
  | "rbt_search_time' (rbt.Node l c ka va r) k =  
       (if k=ka then 2 else (if k<ka then 1 + rbt_search_time' l k else 1 + rbt_search_time' r k))   "
setup \<open>fold add_rewrite_rule @{thms rbt_search_time'.simps}\<close>

lemma btree_search_correct' [hoare_triple]: (* order of \<up> and $ is important *)
  "<btree t b  * $(rbt_search_time' t x) * \<up>(rbt_sorted t)>
   rbt_search x b
   <\<lambda>r. btree t b * \<up>(r = RBTree.rbt_search t x)>\<^sub>t"
@proof @induct t arbitrary b @qed

abbreviation "searchC == 40"
definition rbt_search_time :: "nat \<Rightarrow> nat" where [rewrite]:
    "rbt_search_time n = searchC * n + 4" 

lemma rbt_search_time_ub[resolve]: "rbt_search_time (max_depth t) \<ge> rbt_search_time' t k"
  by(induct t, auto simp: rbt_search_time_def) 

lemma btree_search_correct [hoare_triple]: 
  "<btree t b  * $(rbt_search_time (max_depth t)) * \<up>(rbt_sorted t)>
   rbt_search x b
   <\<lambda>r. btree t b * \<up>(r = RBTree.rbt_search t x)>\<^sub>t"
@proof @have "rbt_search_time (max_depth t) \<ge>\<^sub>t rbt_search_time' t x" @qed 

setup \<open>del_prfstep_thm @{thm rbt_search_time_def}\<close>


subsection \<open>Delete\<close>
  
definition btree_balL :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_balL p = (case p of
     None \<Rightarrow> return None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      cl_l \<leftarrow> get_color (lsub t);
      if cl_l = R then do {
        set_color B (lsub t);   \<comment> \<open> case 1 \<close>
        return p}
      else case rsub t of
        None \<Rightarrow> return p  \<comment> \<open> case 2\<close>
      | Some rp \<Rightarrow> do {  
         rt \<leftarrow> !rp;
         if cl rt = B then do {
           set_color R (rsub t);  \<comment> \<open> case 3\<close>
           set_color B p;
           btree_balance p}
         else case lsub rt of
           None \<Rightarrow> return p  \<comment> \<open> case 4 \<close>
         | Some lrp \<Rightarrow> do {
            lrt \<leftarrow> !lrp;
            if cl lrt = B then do {
              set_color R (lsub rt); \<comment> \<open> case 5 \<close>
              paint R (rsub rt);
              set_color B (rsub t); 
              rp' \<leftarrow> btree_rotate_r (rsub t);
              pp := Node (lsub t) (cl t) (key t) (val t) rp';
              p' \<leftarrow> btree_rotate_l p;
              t' \<leftarrow> !(the p');
              set_color B (lsub t');
              rp'' \<leftarrow> btree_balance (rsub t');
              the p' := Node (lsub t') (cl t') (key t') (val t') rp'';
              return p'}
            else return p}}})"

lemma balL_to_fun [hoare_triple]:
  "<btree (rbt.Node l R k v r) p * $60 >
   btree_balL p
   <btree (balL l k v r)>\<^sub>t"
@proof @unfold "balL l k v r" @qed

definition btree_balR :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_balR p = (case p of
     None \<Rightarrow> return None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      cl_r \<leftarrow> get_color (rsub t);
      if cl_r = R then do {
        set_color B (rsub t);  \<comment>\<open>case 1 \<close>
        return p}
      else case lsub t of
        None \<Rightarrow> return p   \<comment>\<open>case 2\<close>
      | Some lp \<Rightarrow> do {  
         lt \<leftarrow> !lp;
         if cl lt = B then do {
           set_color R (lsub t);   \<comment>\<open>case 3\<close>
           set_color B p;
           btree_balance p}
         else case rsub lt of
           None \<Rightarrow> return p   \<comment>\<open>case 4\<close>
         | Some rlp \<Rightarrow> do {
            rlt \<leftarrow> !rlp;
            if cl rlt = B then do {
              set_color R (rsub lt);   \<comment>\<open>case 5\<close>
              paint R (lsub lt);
              set_color B (lsub t); 
              lp' \<leftarrow> btree_rotate_l (lsub t);
              pp := Node lp' (cl t) (key t) (val t) (rsub t);
              p' \<leftarrow> btree_rotate_r p;
              t' \<leftarrow> !(the p');
              set_color B (rsub t');
              lp'' \<leftarrow> btree_balance (lsub t');
              the p' := Node lp'' (cl t') (key t') (val t') (rsub t');
              return p'}
            else return p}}})"

lemma balR_to_fun [hoare_triple]:
  "<btree (rbt.Node l R k v r) p * $60>
   btree_balR p
   <btree (balR l k v r)>\<^sub>t"
@proof @unfold "balR l k v r" @qed

partial_function (heap_time) btree_combine ::
  "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_combine lp rp =
   (if lp = None then return rp
    else if rp = None then return lp
    else do {
      lt \<leftarrow> !(the lp);
      rt \<leftarrow> !(the rp);
      if cl lt = R then
        if cl rt = R then do {
          tmp \<leftarrow> btree_combine (rsub lt) (lsub rt);
          cl_tm \<leftarrow> get_color tmp;
          if cl_tm = R then do {
            tmt \<leftarrow> !(the tmp);
            the lp := Node (lsub lt) R (key lt) (val lt) (lsub tmt);
            the rp := Node (rsub tmt) R (key rt) (val rt) (rsub rt);
            the tmp := Node lp R (key tmt) (val tmt) rp;
            return tmp}
          else do {
            the rp := Node tmp R (key rt) (val rt) (rsub rt);
            the lp := Node (lsub lt) R (key lt) (val lt) rp;
            return lp}}
        else do {
          tmp \<leftarrow> btree_combine (rsub lt) rp;
          the lp := Node (lsub lt) R (key lt) (val lt) tmp;
          return lp}
      else if cl rt = B then do {
        tmp \<leftarrow> btree_combine (rsub lt) (lsub rt);
        cl_tm \<leftarrow> get_color tmp;
        if cl_tm = R then do {
          tmt \<leftarrow> !(the tmp);
          the lp := Node (lsub lt) B (key lt) (val lt) (lsub tmt);
          the rp := Node (rsub tmt) B (key rt) (val rt) (rsub rt);
          the tmp := Node lp R (key tmt) (val tmt) rp;
          return tmp}
        else do {
          the rp := Node tmp B (key rt) (val rt) (rsub rt);
          the lp := Node (lsub lt) R (key lt) (val lt) rp;
          btree_balL lp}}
      else do {
        tmp \<leftarrow> btree_combine lp (lsub rt);
        the rp := Node tmp R (key rt) (val rt) (rsub rt);
        return rp}})"

fun rbt_combine_time' :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> nat" where
    "rbt_combine_time' Leaf _ = 1"
  | "rbt_combine_time' (rbt.Node l c ka va r) Leaf = 1" 
  | "rbt_combine_time' (rbt.Node l1 c1 k1 v1 r1) (rbt.Node l2 c2 k2 v2 r2) = 
      (if c1=R then
         (if c2=R then 20 +  rbt_combine_time' r1 l2
             else 20 +  rbt_combine_time' r1 (rbt.Node l2 c2 k2 v2 r2) )
        else
          (if c2=B then 80 +  rbt_combine_time' r1 l2
              else 20 + rbt_combine_time' (rbt.Node l1 c1 k1 v1 r1) l2)
           )   "
setup \<open>fold add_rewrite_rule @{thms rbt_combine_time'.simps}\<close>



lemma combine_to_fun' [hoare_triple]:
  "<btree lt lp * btree rt rp * $(rbt_combine_time' lt rt)>
   btree_combine lp rp
   <btree (combine lt rt)>\<^sub>t"
@proof @fun_induct "combine lt rt" arbitrary lp rp @with
  @subgoal "(lt = rbt.Node l1 c1 k1 v1 r1, rt = rbt.Node l2 c2 k2 v2 r2)"
    @unfold "combine (rbt.Node l1 c1 k1 v1 r1) (rbt.Node l2 c2 k2 v2 r2)"
  @endgoal @end
@qed

abbreviation "combineC == 40"
definition btree_combine_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where  
  "btree_combine_time n m = combineC * n + combineC * m + 1"

lemma btree_combine_time_ub[resolve]: "btree_combine_time (max_depth t1) (max_depth t2) \<ge> rbt_combine_time' t1 t2"
  apply(induct rule: rbt_combine_time'.induct) by (auto simp: btree_combine_time_def)

lemma combine_to_fun [hoare_triple]:
  "<btree lt lp * btree rt rp * $(btree_combine_time (max_depth lt) (max_depth rt))>
   btree_combine lp rp
   <btree (combine lt rt)>\<^sub>t"
@proof @have "btree_combine_time (max_depth lt) (max_depth rt) \<ge>\<^sub>t rbt_combine_time' lt rt" @qed
  

partial_function (heap_time) rbt_del ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_del x p = (case p of
     None \<Rightarrow> return None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      (if x = key t then btree_combine (lsub t) (rsub t)
       else if x < key t then case lsub t of
         None \<Rightarrow> do {
           set_color R p;
           return p}
       | Some lp \<Rightarrow> do {
           lt \<leftarrow> !lp;
           if cl lt = B then do {
             q \<leftarrow> rbt_del x (lsub t);
             pp := Node q R (key t) (val t) (rsub t);
             btree_balL p }
           else do {
             q \<leftarrow> rbt_del x (lsub t);
             pp := Node q R (key t) (val t) (rsub t);
             return p }}
       else case rsub t of
         None \<Rightarrow> do {
           set_color R p;
           return p}
       | Some rp \<Rightarrow> do {
           rt \<leftarrow> !rp;
           if cl rt = B then do {
             q \<leftarrow> rbt_del x (rsub t);
             pp := Node (lsub t) R (key t) (val t) q;
             btree_balR p }
           else do {
             q \<leftarrow> rbt_del x (rsub t);
             pp := Node (lsub t) R (key t) (val t) q;
             return p }})})"


fun rbt_del_time' :: "('a, 'b) rbt \<Rightarrow> 'a::ord \<Rightarrow> nat" where
    "rbt_del_time' Leaf _ = 1"
  | "rbt_del_time' (rbt.Node l c ka va r) k  = 
      (if k=ka
        then 2 + btree_combine_time (max_depth l) (max_depth r)
        else (if k < ka then 
            (if l = Leaf then 10
            else 80 + rbt_del_time' l k)
        else 
            (if r = Leaf then 10
            else 80 + rbt_del_time' r k)
        ))
         "
setup \<open>fold add_rewrite_rule @{thms rbt_del_time'.simps}\<close>

lemma rbt_del_to_fun' [hoare_triple]:
  "<btree t p * $(rbt_del_time' t x)>
   rbt_del x p
   <btree (del x t)>\<^sub>t"
@proof @induct t arbitrary p @with
  @subgoal "t = rbt.Node l c k v r"
    @unfold "del x (rbt.Node l c k v r)"
  @endgoal @end
@qed

definition btree_del_time :: "nat \<Rightarrow> nat" where  
  "btree_del_time n = 200 * combineC * n + 8"

lemma btree_del_time_ub[resolve]: "btree_del_time (max_depth t) \<ge> rbt_del_time' t k"
  by (induct t, auto simp: btree_del_time_def btree_combine_time_def)
 
lemma rbt_del_to_fun [hoare_triple]:
  "<btree t p * $(btree_del_time (max_depth t))>
   rbt_del x p
   <btree (del x t)>\<^sub>t"
@proof @have "btree_del_time (max_depth t) \<ge>\<^sub>t rbt_del_time' t x" @qed 
   
definition rbt_delete ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_delete k p = do {
    p' \<leftarrow> rbt_del k p;
    paint B p';
    return p'}"

definition rbt_delete_time :: "nat \<Rightarrow> nat" where [rewrite]:
    "rbt_delete_time n = btree_del_time n + 4"

lemma rbt_delete_to_fun [hoare_triple]:
  "<btree t p * $(rbt_delete_time (max_depth t))>
   rbt_delete k p
   <btree (RBTree.delete k t)>\<^sub>t" by auto2
 
section \<open>Height-Size Relation\<close>


fun size :: "('a, 'b) rbt \<Rightarrow> nat" where
  "size Leaf = 0"
| "size (rbt.Node l c k v r) =  1 + size l + size r"

definition size1 :: "('a, 'b) rbt \<Rightarrow> nat" where "size1 t = 1 + size t"

lemma bheight_size_bound: "is_rbt t \<Longrightarrow> size1 t \<ge> 2 ^ (black_depth t)"
  apply(induction t) apply simp apply (auto simp: is_rbt_def size1_def )
  subgoal for t1 x2 x3 x4 t2 apply(cases x2)
    by auto done
 
                                                                                 
lemma max_black_aux: "is_rbt t \<Longrightarrow> (if rbt.cl t = R then max_depth t \<le> 2 * black_depth t + 1
                               else max_depth t \<le> 2 * black_depth t)"
@proof @induct t  @with
  @subgoal "t = rbt.Node l c k v r" @case "c = R" @endgoal
  @end
@qed


lemma max_black: "is_rbt t  \<Longrightarrow> (max_depth t -1)/2 \<le>   black_depth t"
  using max_black_aux  apply(cases "rbt.cl t") by fastforce+

 

lemma rbt_height_le: assumes "is_rbt t" shows "max_depth t \<le> 2 * log 2 (size1 t) + 1"
proof -
  have "2 powr ((max_depth t - 1 )/ 2) \<le> 2 powr black_depth t"
    using max_black[OF assms] by (simp)
  also have "\<dots> \<le> size1 t" using assms
    by (simp add: powr_realpow bheight_size_bound  )
  finally have "2 powr ((max_depth t -1) / 2) \<le> size1 t" .
  hence "(max_depth t -1) / 2 \<le> log 2 (size1 t)"
    by(simp add: le_log_iff size1_def del: divide_le_eq_numeral1(1))
  thus ?thesis by simp
qed  

subsection "size1 of operations"

lemma size1Leaf[rewrite]: "size1 Leaf = 1" by (simp add: size1_def)

lemma size1_paint[simp]: "size1 (RBTree.paint b t) = size1 t" by(induct t, auto simp: size1_def)
lemma size_paint[simp]: "size (RBTree.paint b t) = size t" by(induct t, auto)


lemma size_red_subs: "rbt.cl t = R \<Longrightarrow> size t = size (rbt.lsub t) + size (rbt.rsub t) + 1"
   apply(cases t) by auto 

lemma size_balanceR[simp]: "size (RBTree.balanceR l k v r) = 1 + size l + size r"
  apply( auto simp: balanceR_def)
  apply(cases "rbt.cl (rbt.lsub r)") by (auto simp: Let_def size_red_subs)

                                   
lemma size_balance[simp]: "size (RBTree.balance l k v r) = 1 + size l + size r"
  by (auto simp: balance_def Let_def size_red_subs) 

lemma size1_ins[simp]: "size1 (RBTree.ins k v t) \<le> size1 t + 1" by (induct t, auto simp: size1_def)

lemma size1_rbt_insert[resolve]: "size1 (RBTree.rbt_insert k v t) \<le> size1 t + 1"
  apply(simp add: RBTree.rbt_insert_def) using size1_ins by simp




section \<open>size of map\<close>

lemma [simp]: "g = Map (meval g)" apply(cases g) by auto

lemma map_of_alist_conc: "(map_of_alist (xs @ ys)) = Map (\<lambda>k.
     (case meval (map_of_alist xs) k of None \<Rightarrow> meval (map_of_alist ys) k
                                       | Some v \<Rightarrow> Some v))"
  by(induct xs, auto intro: meval_ext simp: empty_map_def update_map_def)

lemma rbt_set_keys_of: "rbt_sorted t \<Longrightarrow> keys_of (rbt_map t) = rbt_set t"
proof(induct t)
  case Leaf
  then show ?case by ( auto simp: rbt_map_def empty_map_def keys_of_def)
next
  case (Node t1 x2 x3 x4 t2) 
  have i: " keys_of (rbt_map (rbt.Node t1 x2 x3 x4 t2))
          = keys_of (rbt_map t1) \<union> {x3} \<union> (keys_of (rbt_map t2))"    
    unfolding keys_of_def rbt_map_def by (auto split: option.split simp: map_of_alist_conc update_map_def) 
  from Node show ?case unfolding i by auto
qed
  
lemma [simp]: "finite (rbt_set t)" by(induct t, auto)   

lemma rbt_map_card: "rbt_sorted (rbt.Node l c k v r) \<Longrightarrow>
     card (keys_of (rbt_map (rbt.Node l c k v r))) = card (keys_of (rbt_map l)) + 1 + card (keys_of (rbt_map r))"
proof -
  assume r: "rbt_sorted (rbt.Node l c k v r)"
  from r have [simp]: "rbt_set l \<inter> rbt_set r = {}" by (auto 3 4) 
  from r have "card (rbt_set (rbt.Node l c k v r)) = Suc (card (rbt_set l \<union> rbt_set r))"
    by (auto intro: card_insert_disjoint) 
  also have "card (rbt_set l \<union> rbt_set r) = card (rbt_set l) + card (rbt_set r)"
    apply(rule card_Un_disjoint) by auto
  finally show ?thesis using r by (auto simp: rbt_set_keys_of)
qed

lemma card_keysof_size: "RBTree.rbt_sorted t \<Longrightarrow> card (keys_of (rbt_map t)) = size t"
  apply(induct t) 
  subgoal apply (auto simp: rbt_map_def keys_of_def empty_map_def) done
  subgoal apply (auto simp: rbt_map_card) done
  done

definition sizeM1 :: "('a, 'b) Mapping_Str.map \<Rightarrow> nat" where "sizeM1 M = 1 + card (keys_of M)"

section \<open>Runtime in terms of size of the map\<close>

definition rbt_absch :: "nat \<Rightarrow> nat"  where "rbt_absch n = (nat (ceiling (2 * log 2 n + 1)))"

lemma rbt_absch_bound[asym_bound]: "(\<lambda>x. rbt_absch x) \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding rbt_absch_def apply(rule ceiling_Theta) 
unfolding eventually_nonneg_def eventually_sequentially apply(rule exI[where x=1])
  unfolding log_def by auto

lemma rbt_absch_mono: "x > 0 \<Longrightarrow> x \<le> y \<Longrightarrow> rbt_absch x \<le> rbt_absch y"
  by (auto simp: rbt_absch_def intro!: ceiling_mono nat_mono)
 

lemma "is_rbt t \<Longrightarrow> size1 t \<le> n \<Longrightarrow> rbt_absch (size1 t) \<le> rbt_absch n"  
  apply(rule rbt_absch_mono) by(auto simp: size1_def) 

subsection \<open>insert\<close>


lemma rbt_insert_time_mono: "x \<le> y \<Longrightarrow> rbt_insert_time x \<le> rbt_insert_time y"
  unfolding rbt_insert_time_def rbt_ins_time_def by auto     

definition rbt_insert_logN :: "nat \<Rightarrow> nat" where "rbt_insert_logN n = rbt_insert_time (rbt_absch n)"

lemma rbt_insert_logN_gt0[resolve]: "rbt_insert_logN n > 0"
  by (simp add: rbt_insert_logN_def rbt_absch_def rbt_insert_time_def)

lemma rbt_insert_logN_mono: "0 < x \<Longrightarrow> x\<le>y \<Longrightarrow> rbt_insert_logN x \<le> rbt_insert_logN y"
  by(auto simp: rbt_insert_logN_def intro!: rbt_insert_time_mono rbt_absch_mono)

lemma rbt_insert_time_absch: assumes "is_rbt t" "rbt_sorted t" "rbt_map t = M" shows K[backward]: "rbt_insert_time (max_depth t) \<le> rbt_insert_logN (sizeM1 M)"
  unfolding rbt_insert_logN_def
proof (rule rbt_insert_time_mono)   
  have A: "rbt_absch (size1 t) = rbt_absch (sizeM1 M)" 
    using card_keysof_size[OF assms(2)] assms(3) by(auto simp: size1_def sizeM1_def) 
  have B: "max_depth t \<le> rbt_absch (size1 t)"
    unfolding rbt_absch_def 
      using assms(1) apply(auto dest!: rbt_height_le )
      by linarith  
  from A B show "max_depth t \<le> rbt_absch (sizeM1 M)" by auto
qed
 

lemma rbt_insert_rule' [hoare_triple]:
  "is_rbt t \<Longrightarrow> rbt_sorted t \<Longrightarrow> M = rbt_map t \<Longrightarrow>
    <btree t p * $(rbt_insert_logN (sizeM1 M))>
   rbt_insert k v p
   <\<lambda>r. btree (RBTree.rbt_insert k v t) r * \<up>(is_rbt (RBTree.rbt_insert k v t))
         * \<up>(rbt_sorted (RBTree.rbt_insert k v t))
         * \<up>((M {k \<rightarrow> v}) = rbt_map (RBTree.rbt_insert k v t)) >\<^sub>t"
@proof
  @have  " rbt_insert_logN (sizeM1 M) \<ge>\<^sub>t rbt_insert_time (max_depth t)"
@qed 


subsection \<open>search\<close>


definition rbt_search_time_logN :: "nat \<Rightarrow> nat" where "rbt_search_time_logN n = rbt_search_time (rbt_absch n)"

lemma rbt_search_time_logN_gt0[resolve]: "rbt_search_time_logN n > 0"
  by (simp add: rbt_search_time_logN_def rbt_absch_def rbt_search_time_def)

lemma rbt_search_time_mono: "x \<le> y \<Longrightarrow> rbt_search_time x \<le> rbt_search_time y"
  unfolding rbt_search_time_def by auto

lemma rbt_search_time_logN_mono: "0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> rbt_search_time_logN x \<le> rbt_search_time_logN y"
  by(auto simp: rbt_search_time_logN_def intro!: rbt_absch_mono rbt_search_time_mono) 
 

lemma assumes "is_rbt t" "rbt_sorted t" "rbt_map t = M" shows L[backward]: "rbt_search_time (max_depth t) \<le> rbt_search_time_logN (sizeM1 M)"
  unfolding rbt_search_time_logN_def
proof (rule rbt_search_time_mono)   
  have A: "rbt_absch (size1 t) = rbt_absch (sizeM1 M)" 
    using card_keysof_size[OF assms(2)] assms(3) by(auto simp: size1_def sizeM1_def) 
  have B: "max_depth t \<le> rbt_absch (size1 t)"
    unfolding rbt_absch_def 
      using assms(1) apply(auto dest!: rbt_height_le  )
      by linarith  
  from A B show "max_depth t \<le> rbt_absch (sizeM1 M)" by auto
qed


lemma rbt_search_rule' [hoare_triple]:
  "is_rbt t \<Longrightarrow> rbt_sorted t \<Longrightarrow> M = rbt_map t \<Longrightarrow>
    <btree t p * $(rbt_search_time_logN (sizeM1 M))>
   rbt_search k p
   <\<lambda>r. btree t p * \<up>(r = RBTree.rbt_search t k)>\<^sub>t"
@proof
  @have  " rbt_search_time_logN (sizeM1 M) \<ge>\<^sub>t rbt_search_time (max_depth t)"
@qed 

subsection \<open>delete\<close>


definition rbt_delete_time_logN :: "nat \<Rightarrow> nat" where "rbt_delete_time_logN n = rbt_delete_time (rbt_absch n)"

lemma rbt_delete_time_logN_gt0[resolve]: "rbt_delete_time_logN n > 0"
  by (simp add: rbt_delete_time_logN_def rbt_absch_def rbt_delete_time_def)

lemma rbt_delete_time_mono: "x \<le> y \<Longrightarrow> rbt_delete_time x \<le> rbt_delete_time y"
  unfolding rbt_delete_time_def btree_del_time_def by auto

lemma rbt_delete_time_logN_mono: "0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> rbt_delete_time_logN x \<le> rbt_delete_time_logN y"
  by(auto simp: rbt_delete_time_logN_def intro!: rbt_absch_mono rbt_delete_time_mono) 


lemma assumes "is_rbt t" "rbt_sorted t" "rbt_map t = M" shows rbt_delete_time_absch[backward]: "rbt_delete_time (max_depth t) \<le> rbt_delete_time_logN (sizeM1 M)"
  unfolding rbt_delete_time_logN_def
proof (rule rbt_delete_time_mono)   
  have A: "rbt_absch (size1 t) = rbt_absch (sizeM1 M)" 
    using card_keysof_size[OF assms(2)] assms(3) by(auto simp: size1_def sizeM1_def) 
  have B: "max_depth t \<le> rbt_absch (size1 t)"
    unfolding rbt_absch_def 
      using assms(1) apply(auto dest!: rbt_height_le  )
      by linarith  
  from A B show "max_depth t \<le> rbt_absch (sizeM1 M)" by auto
qed

lemma rbt_delete_rule' [hoare_triple]:
  "is_rbt t \<Longrightarrow> rbt_sorted t \<Longrightarrow> M = rbt_map t \<Longrightarrow>
    <btree t p * $(rbt_delete_time_logN (sizeM1 M))>
   rbt_delete k p
   <\<lambda>p. btree (RBTree.delete k t) p * \<up>(is_rbt (RBTree.delete k t))
       * \<up>(rbt_sorted (RBTree.delete k t)) * \<up>((delete_map k M) = rbt_map (RBTree.delete k t))>\<^sub>t"
@proof
  @have  " rbt_delete_time_logN (sizeM1 M) \<ge>\<^sub>t rbt_delete_time (max_depth t)"
@qed 


section \<open>Outer interface\<close>
 

definition rbt_map_assn :: "('a, 'b) map \<Rightarrow> ('a::{heap,linorder}, 'b::heap) rbt_node ref option \<Rightarrow> assn" where
  "rbt_map_assn M p = (\<exists>\<^sub>At. btree t p * \<up>(is_rbt t) * \<up>(rbt_sorted t) * \<up>(M = rbt_map t))"
setup \<open>add_rewrite_ent_rule @{thm rbt_map_assn_def}\<close>

subsection \<open>tree empty\<close>

theorem rbt_empty_rule [hoare_triple]:
  "<$1> tree_empty <rbt_map_assn empty_map>" by auto2

subsection \<open>insert\<close>

theorem rbt_insert_rule [hoare_triple]:
  "<rbt_map_assn M b * $(rbt_insert_logN (sizeM1 M))> rbt_insert k v b <rbt_map_assn (M {k \<rightarrow> v})>\<^sub>t"
by auto2 

lemma rbt_insert_logN_bound[asym_bound]: 
  "(\<lambda>n. rbt_insert_logN n) \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding rbt_insert_logN_def rbt_insert_time_def rbt_ins_time_def  
  by auto2 

subsection \<open>search\<close>

lemma rbt_search_time_logN_bound[asym_bound]:
  "(\<lambda>n. rbt_search_time_logN n) \<in> \<Theta>(\<lambda>n. ln n)" unfolding rbt_search_time_logN_def rbt_search_time_def by auto2

theorem rbt_search [hoare_triple]:
  "<rbt_map_assn M b * $(rbt_search_time_logN (sizeM1 M))> rbt_search x b <\<lambda>r. rbt_map_assn M b * \<up>(r = M\<langle>x\<rangle>)>\<^sub>t"
  by auto2


subsection \<open>delete\<close>

lemma rbt_delete_time_logN_bound[asym_bound]:
  "(\<lambda>n. rbt_delete_time_logN n) \<in> \<Theta>(\<lambda>n. ln n)" unfolding rbt_delete_time_logN_def rbt_delete_time_def btree_del_time_def by auto2

theorem rbt_delete_rule [hoare_triple]:
  "<rbt_map_assn M b * $(rbt_delete_time_logN (sizeM1 M))> rbt_delete k b <rbt_map_assn (delete_map k M)>\<^sub>t" by auto2

end
