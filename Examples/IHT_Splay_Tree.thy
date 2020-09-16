theory IHT_Splay_Tree
  imports 
    IHT_Tree 
    Amortized_Complexity.Splay_Tree_Analysis
    "../Asymptotics/Asymptotics_1D"
begin

definition rotate_rr :: "'a::heap ptree \<Rightarrow> 'a ptree Heap" where
  "rotate_rr p = do {
    p' \<leftarrow> rotate_r p;
    rotate_r p'
   }"

lemma rotate_rr_rule [hoare_triple]:
  "<btree \<langle>\<langle>\<langle>A1, a', A2\<rangle>, a, B\<rangle>, b, CD\<rangle> p * $10>
    rotate_rr p
   <btree \<langle>A1, a', \<langle>A2, a, \<langle>B, b, CD\<rangle>\<rangle>\<rangle>>" by auto2

definition rotate_lr :: "'a::heap ptree \<Rightarrow> 'a ptree Heap" where
  "rotate_lr p = (case p of
     None \<Rightarrow> raise ''Empty ptree''
   | Some pp \<Rightarrow> do {
       t \<leftarrow> !pp;
       lp' \<leftarrow> rotate_l (lsub t);
       pp := Node lp' (val t) (rsub t);
       rotate_r p
     })"

lemma rotate_lr_rule [hoare_triple]:
  "<btree \<langle>\<langle>A, a, \<langle>B1, b', B2\<rangle>\<rangle>, b, CD\<rangle> p * $12>
    rotate_lr p
   <btree \<langle>\<langle>A, a, B1\<rangle>, b', \<langle>B2, b, CD\<rangle>\<rangle>>" by auto2

definition rotate_rl :: "'a::heap ptree \<Rightarrow> 'a ptree Heap" where
  "rotate_rl p = (case p of
     None \<Rightarrow> raise ''Empty ptree''
   | Some pp \<Rightarrow> do {
       t \<leftarrow> !pp;
       rp' \<leftarrow> rotate_r (rsub t);
       pp := Node (lsub t) (val t) rp';
       rotate_l p
     })"

lemma rotate_rl_rule [hoare_triple]:
  "<btree \<langle>AB, b, \<langle>\<langle>C1, c', C2\<rangle>, c, D\<rangle>\<rangle> p * $12>
    rotate_rl p
   <btree \<langle>\<langle>AB, b, C1\<rangle>, c', \<langle>C2, c, D\<rangle>\<rangle>>" by auto2

definition rotate_ll :: "'a::heap ptree \<Rightarrow> 'a ptree Heap" where
  "rotate_ll p = do {
    p' \<leftarrow> rotate_l p;
    rotate_l p'
  }"

lemma rotate_ll_rule [hoare_triple]:
  "<btree \<langle>A1, a', \<langle>A2, a, \<langle>B, b, CD\<rangle>\<rangle>\<rangle> p * $10>
    rotate_ll p
   <btree \<langle>\<langle>\<langle>A1, a', A2\<rangle>, a, B\<rangle>, b, CD\<rangle>>" by auto2

partial_function (heap_time) splay_impl :: "'a::{heap,linorder} \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree Heap" where
  "splay_impl x p = (case p of
     None \<Rightarrow> return None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      if x = val t then return p
      else if x < val t then (case lsub t of
         None \<Rightarrow> return p
       | Some lp \<Rightarrow> do {
           lt \<leftarrow> !lp;
           if x = val lt then rotate_r p
           else if x < val lt then (case lsub lt of
              None \<Rightarrow> rotate_r p
            | Some llp \<Rightarrow> do {
               llp' \<leftarrow> splay_impl x (lsub lt);
               lp := Node llp' (val lt) (rsub lt);
               rotate_rr p })
           else (case rsub lt of
              None \<Rightarrow> rotate_r p
            | Some rlp \<Rightarrow> do {
               rlp' \<leftarrow> splay_impl x (rsub lt);
               lp := Node (lsub lt) (val lt) rlp';
               rotate_lr p })})
      else (case rsub t of
         None \<Rightarrow> return p
       | Some rp \<Rightarrow> do {
           rt \<leftarrow> !rp;
           if x = val rt then rotate_l p
           else if x < val rt then (case lsub rt of
              None \<Rightarrow> rotate_l p
            | Some lrp \<Rightarrow> do {
               lrp' \<leftarrow> splay_impl x (lsub rt);
               rp := Node lrp' (val rt) (rsub rt);
               rotate_rl p })
           else (case rsub rt of
              None \<Rightarrow> rotate_l p
            | Some rrp \<Rightarrow> do {
               rrp' \<leftarrow> splay_impl x (rsub rt);
               rp := Node (lsub rt) (val rt) rrp';
               rotate_ll p })}) })"
 
declare splay.simps(1) [rewrite]

lemma splay_code': "splay x (Tree.Node AB b CD) =
  (if x=b
   then Tree.Node AB b CD
   else if x < b
        then case AB of
          Leaf \<Rightarrow> Tree.Node AB b CD |
          Tree.Node A a B \<Rightarrow>
            (if x=a then Tree.Node A a (Tree.Node B b CD)
             else if x < a
                  then if A = Leaf then Tree.Node A a (Tree.Node B b CD)
                       else case splay x A of
                         Tree.Node A\<^sub>1 a' A\<^sub>2 \<Rightarrow> Tree.Node A\<^sub>1 a' (Tree.Node A\<^sub>2 a (Tree.Node B b CD))
                  else if B = Leaf then Tree.Node A a (Tree.Node B b CD)
                       else case splay x B of
                         Tree.Node B\<^sub>1 b' B\<^sub>2 \<Rightarrow> Tree.Node (Tree.Node A a B\<^sub>1) b' (Tree.Node B\<^sub>2 b CD))
        else case CD of
          Leaf \<Rightarrow> Tree.Node AB b CD |
          Tree.Node C c D \<Rightarrow>
            (if x=c then Tree.Node (Tree.Node AB b C) c D
             else if x < c
                  then if C = Leaf then Tree.Node (Tree.Node AB b C) c D
                       else case splay x C of
                         Tree.Node C\<^sub>1 c' C\<^sub>2 \<Rightarrow> Tree.Node (Tree.Node AB b C\<^sub>1) c' (Tree.Node C\<^sub>2 c D)
                  else if D=Leaf then Tree.Node (Tree.Node AB b C) c D
                       else case splay x D of
                         Tree.Node D\<^sub>1 d D\<^sub>2 \<Rightarrow> Tree.Node (Tree.Node (Tree.Node AB b C) c D\<^sub>1) d D\<^sub>2))"
  by(auto split!: tree.split)

declare splay_code' [rewrite]

definition splay_time :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
  "splay_time a t = 15 * t_splay a t"

lemma splay_time_simp:
  "splay_time a Leaf = 15"
  "splay_time a \<langle>l, b, r\<rangle> =
    (if a = b then 15
     else if a < b then case l of
        Leaf \<Rightarrow> 15
      | \<langle>ll, c, lr\<rangle> \<Rightarrow>
        (if a = c then 15
         else if a < c then if ll = Leaf then 15 else splay_time a ll + 15
              else if lr = Leaf then 15 else splay_time a lr + 15)
     else case r of
        Leaf \<Rightarrow> 15
      | \<langle>rl, c, rr\<rangle> \<Rightarrow>
         (if a = c then 15
          else if a < c then if rl = Leaf then 15 else splay_time a rl + 15
               else if rr = Leaf then 15 else splay_time a rr + 15))"
  by (auto split!: tree.split simp: splay_time_def)
declare splay_time_simp [rewrite]
setup \<open>add_fun_induct_rule (@{term_pat splay}, @{thm t_splay.induct[simplified LT EQ GT]})\<close>
 

lemma splay_not_Leaf: "splay x \<langle>l, a, r\<rangle> \<noteq> Leaf" by auto
setup \<open>add_forward_prfstep_cond @{thm splay_not_Leaf} [with_term "splay ?x \<langle>?l, ?a, ?r\<rangle>"]\<close>


lemma splay_correct [hoare_triple]:
  "<btree t a * $(splay_time x t)>
    splay_impl x a
   <btree (splay x t)>\<^sub>t"
@proof @fun_induct "splay x t" arbitrary a @with
  @subgoal "(x = x, t = \<langle>lt, b, rt\<rangle>)"
    @case "x = b"
    @case "x < b" @with
      @case "lt = Leaf"
    @end
    @case "x > b" @with
      @case "rt = Leaf"
    @end
  @endgoal @end
@qed 


definition tree_constr_gen :: "'a::heap ptree \<Rightarrow> 'a \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree Heap" where
  "tree_constr_gen lp v rp = do {
     p \<leftarrow> ref (Node lp v rp);
     return (Some p)
   }"

lemma tree_constr_gen_rule [hoare_triple]:
  "<btree lt lp * btree rt rp * $2>
    tree_constr_gen lp v rp
   <btree \<langle>lt, v, rt\<rangle>>" by auto2

definition insert_impl :: "'a::{heap,linorder} \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree Heap" where
  "insert_impl x p = (case p of
     None \<Rightarrow> tree_constr x
   | _ \<Rightarrow> do {
      p' \<leftarrow> splay_impl x p;
      (case p' of
        None \<Rightarrow> raise ''splay_insert''
      | Some pp' \<Rightarrow> do {
          t' \<leftarrow> !pp';
          case cmp x (val t') of
            EQ \<Rightarrow> return p'
          | LT \<Rightarrow> do {
              pp' := Node None (val t') (rsub t');
              tree_constr_gen (lsub t') x p'
            }
          | GT \<Rightarrow> do {
              pp' := Node (lsub t') (val t') None;
              tree_constr_gen p' x (rsub t')
            }})})"

definition insert_time :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where [rewrite]:
  "insert_time x t = splay_time x t + 4"

setup \<open>add_rewrite_rule @{thm Splay_Tree.insert.simps}\<close>
setup \<open>fold add_rewrite_rule @{thms cmp_val.case}\<close>
setup \<open>add_cases_rule @{thm cmp_val.induct}\<close>

lemma insert_correct [hoare_triple]:
  "<btree t a * $(insert_time x t)>
    insert_impl x a
   <btree (insert x t)>\<^sub>t"
@proof
  @case "t = Leaf"
  @let "V = cmp x (value (splay x t))"
  @cases V
@qed

partial_function (heap_time) splay_max_impl :: "'a::{heap,linorder} ptree \<Rightarrow> 'a ptree Heap" where
  "splay_max_impl p = (case p of
     None \<Rightarrow> return None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      case rsub t of
        None \<Rightarrow> return p
      | Some rp \<Rightarrow> do {
          rt \<leftarrow> !rp;
          if rsub rt = None then rotate_l p
          else do {
            rrp' \<leftarrow> splay_max_impl (rsub rt);
            case rrp' of
              None \<Rightarrow> raise ''splay_max_impl''
            | Some rrt \<Rightarrow> do {
                rp := Node (lsub rt) (val rt) rrp';
                rotate_ll p }}}})"

definition splay_max_time :: "'a::linorder tree \<Rightarrow> nat" where
  "splay_max_time t = 15 * t_splay_max t"

lemma splay_max_time_simps [rewrite]:
  "splay_max_time Leaf = 15"
  "splay_max_time \<langle>l, b, Leaf\<rangle> = 15"
  "splay_max_time \<langle>l, b, \<langle>rl, c, rr\<rangle>\<rangle> = (if rr=Leaf then 15 else splay_max_time rr + 15)"
  by (simp add: splay_max_time_def)+

setup \<open>fold add_rewrite_rule @{thms splay_max.simps}\<close>

lemma splay_max_not_Leaf: "splay_max \<langle>l, a, r\<rangle> \<noteq> Leaf" by auto
setup \<open>add_forward_prfstep_cond @{thm splay_max_not_Leaf} [with_term "splay_max \<langle>?l, ?a, ?r\<rangle>"]\<close>

lemma splay_max_correct [hoare_triple]:
  "<btree t a * $(splay_max_time t)>
    splay_max_impl a
   <btree (splay_max t)>\<^sub>t"
@proof @fun_induct "splay_max t" arbitrary a @qed

definition delete_impl :: "'a::{heap,linorder} \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree Heap" where
  "delete_impl x p = (case p of
     None \<Rightarrow> return None
   | Some _ \<Rightarrow> do {
       p' \<leftarrow> splay_impl x p;
       case p' of
         None \<Rightarrow> raise ''delete_impl''
       | Some pp' \<Rightarrow> do {
           t' \<leftarrow> !pp';
           if x = val t' then
              if lsub t' = None then return (rsub t')
              else do {
                lp' \<leftarrow> splay_max_impl (lsub t');
                (case lp' of
                    None \<Rightarrow> raise ''delete_impl''
                  | Some lpp' \<Rightarrow> do {
                      lt' \<leftarrow> !lpp';
                      pp' := Node (lsub lt') (val lt') (rsub t');
                      return p' })}
           else return p' }})"

definition delete_time :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
  "delete_time a t = 15 * t_delete a t + 5"

lemma delete_time_simps [rewrite]:
  "delete_time a t = (if t = Leaf then 5 else splay_time a t + (case splay a t of
    \<langle>l, x, r\<rangle> \<Rightarrow>
      if x=a then case l of Leaf \<Rightarrow> 5 | _ \<Rightarrow> splay_max_time l + 5
      else 5))"
  by (auto split!: tree.split simp: splay_time_def splay_max_time_def delete_time_def t_delete_def)

setup \<open>add_rewrite_rule @{thm Splay_Tree.delete_def}\<close>

lemma splay_delete_correct [hoare_triple]:
  "<btree t a * $(delete_time x t)>
    delete_impl x a
   <btree (delete x t)>\<^sub>t"
@proof
  @case "t = Leaf"
  @case "x = value (splay x t)"
@qed

section \<open>Amortized analysis\<close>

definition splay_tree_P :: "'a tree \<Rightarrow> nat" where
  "splay_tree_P t = 15 * nat \<lceil>\<Phi> t\<rceil>"

definition splay_tree :: "'a::heap tree \<Rightarrow> 'a ptree \<Rightarrow> assn" where [rewrite_ent]:
  "splay_tree t a = btree t a * $(splay_tree_P t)"

lemma \<Phi>_nneg: "\<Phi> t \<ge> 0" by (induct t) auto

definition splay_atime :: "nat \<Rightarrow> nat" where
  "splay_atime n = 15 * nat (\<lceil>3 * log 2 n + 1\<rceil> + 1)"

lemma amor_transfer:
  assumes "real t + P a - P b \<le> c" and "c \<ge> 0" and "\<forall>x. P x \<ge> 0"
  shows "t + nat \<lceil>P a\<rceil> \<le> nat \<lceil>P b\<rceil> + nat (\<lceil>c\<rceil> + 1)" (is "?lhs \<le> ?rhs")
proof -
  have transfer': "real ?lhs \<le> real ?rhs"
  proof -
    have ineq1: "real t + \<lceil>P a\<rceil> - \<lceil>P b\<rceil> \<le> \<lceil>c\<rceil> + 1" using assms by linarith
    have ineq2: "\<forall>x. \<lceil>P x\<rceil> \<ge> 0" using assms by (smt zero_le_ceiling)
    show ?thesis using ineq1 ineq2 by (simp only: of_nat_add of_nat_nat assms)
  qed
  then show ?thesis
    using of_nat_le_iff by blast
qed

lemma a_splay [resolve]:
  assumes "bst t"
  shows "splay_time a t + splay_tree_P (splay a t) \<le> splay_tree_P t + splay_atime (size1 t)"
proof -
  have ineq1: "t_splay a t + nat (\<lceil>\<Phi> (splay a t)\<rceil>) \<le> nat (\<lceil>\<Phi> t\<rceil>) + nat (\<lceil>3 * log 2 (size1 t) + 1\<rceil> + 1)"
    apply (rule amor_transfer [of "t_splay a t" "\<Phi>"])
    apply (subst a_splay_def[symmetric])
    using assms by (rule a_splay_ub3) (simp add: \<Phi>_nneg)+
  then show ?thesis
    by (simp only: splay_tree_P_def splay_atime_def splay_time_def)
qed

lemma splay_tree_splay_amor [hoare_triple]:
  "bst t \<Longrightarrow>
   <splay_tree t a * $(splay_atime (size1 t))>
    splay_impl x a
   <splay_tree (splay x t)>\<^sub>t"
@proof
  @have "splay_tree_P t + splay_atime (size1 t) \<ge>\<^sub>t splay_time x t + splay_tree_P (splay x t)"
@qed

lemma splay_atime_alt: "\<forall>\<^sub>F x in sequentially. real (splay_atime x) = 30 + 15 * real (nat (\<lceil>3 * log 2 (real x)\<rceil>))"
  unfolding eventually_sequentially apply(rule exI[where x=1])  
  apply (auto simp: splay_atime_def) apply(subst nat_add_distrib)
  apply auto apply(rule less_le_trans[of _ 0]) using log2_gt_zero by auto

lemma splay_atime_asym [asym_bound]:
  "(\<lambda>n. splay_atime n) \<in> \<Theta>(\<lambda>x. ln (real x))" 
  apply(rule landau_theta.ev_eq_trans2[OF splay_atime_alt]) 
  using abcd_lnx[of 30 15 3 0] by auto

definition insert_atime :: "nat \<Rightarrow> nat" where
  "insert_atime n = 15 * nat (\<lceil>4 * log 2 n + 2\<rceil> + 1) + 4"

lemma a_insert [backward]:
  assumes "bst t"
  shows "insert_time x t + splay_tree_P (insert x t) \<le> splay_tree_P t + insert_atime (size1 t)"
proof -
  have ineq1: "t_splay x t + nat \<lceil>\<Phi> (insert x t)\<rceil> \<le> nat \<lceil>\<Phi> t\<rceil> + nat (\<lceil>4 * \<phi> t + 2\<rceil> + 1)"
    apply (rule amor_transfer [of "t_splay x t" "\<Phi>"])
    using assms by (rule amor_insert) (simp add: \<Phi>_nneg)+
  then show ?thesis
    by (simp only: insert_time_def splay_tree_P_def insert_atime_def splay_time_def)
qed

lemma insert_atime_alt: "\<forall>\<^sub>F x in sequentially. real (insert_atime x) = 49 + 15 * real (nat (\<lceil>4 * log 2 (real x)\<rceil>))"
  unfolding eventually_sequentially apply(rule exI[where x=1])  
  apply (auto simp: insert_atime_def) apply(subst nat_add_distrib)
  apply auto apply(rule less_le_trans[of _ 0] ) using log2_gt_zero by auto

lemma insert_atime_asym [asym_bound]:
  "(\<lambda>n. insert_atime n) \<in> \<Theta>(\<lambda>x. ln (real x))"
  apply(rule landau_theta.ev_eq_trans2[OF insert_atime_alt]) 
  using abcd_lnx[of 49 15 4 0] by auto

lemma splay_tree_insert_amor [hoare_triple]:
  "bst t \<Longrightarrow>
   <splay_tree t a * $(insert_atime (size1 t))>
    insert_impl x a
   <splay_tree (insert x t)>\<^sub>t"
@proof
  @have "splay_tree_P t + insert_atime (size1 t) \<ge>\<^sub>t insert_time x t + splay_tree_P (insert x t)"
@qed

definition delete_atime :: "nat \<Rightarrow> nat" where
  "delete_atime n = 15 * nat (\<lceil>6 * log 2 n + 2\<rceil> + 1) + 5"

lemma a_delete [backward]:
  assumes "bst t"
  shows "delete_time x t + splay_tree_P (delete x t) \<le> splay_tree_P t + delete_atime (size1 t)"
proof -
  have ineq1: "t_delete x t + nat \<lceil>\<Phi> (delete x t)\<rceil> \<le> nat \<lceil>\<Phi> t\<rceil> + nat (\<lceil>6 * \<phi> t + 2\<rceil> + 1)"
    apply (rule amor_transfer [of "t_delete x t" "\<Phi>"])
    using assms by (rule amor_delete) (simp add: \<Phi>_nneg)+
  then show ?thesis
    by (simp only: delete_time_def splay_tree_P_def delete_atime_def)
qed

lemma delete_atime_alt: "\<forall>\<^sub>F x in sequentially. real (delete_atime x) = 50 + 15 * real (nat (\<lceil>6 * log 2 (real x)\<rceil>))"
  unfolding eventually_sequentially apply(rule exI[where x=1])  
  apply (auto simp: delete_atime_def) apply(subst nat_add_distrib)
  apply auto apply(rule less_le_trans[of _ 0] ) using log2_gt_zero by auto

lemma delete_atime_asym [asym_bound]:
  "(\<lambda>n. delete_atime n) \<in> \<Theta>(\<lambda>x. ln (real x))" 
  apply(rule landau_theta.ev_eq_trans2[OF delete_atime_alt]) 
  using abcd_lnx[of 50 15 6 0] by auto

lemma splay_tree_delete_amor [hoare_triple]:
  "bst t \<Longrightarrow>
   <splay_tree t a * $(delete_atime (size1 t))>
    delete_impl x a
   <splay_tree (delete x t)>\<^sub>t"
@proof
  @have "splay_tree_P t + delete_atime (size1 t) \<ge>\<^sub>t delete_time x t + splay_tree_P (delete x t)"
@qed

setup \<open>del_prfstep_thm @{thm splay_tree_def}\<close>

section \<open>Abstract assertion\<close>

definition splay_tree_set :: "'a::{heap,linorder} set \<Rightarrow> 'a ptree \<Rightarrow> assn" where [rewrite_ent]:
  "splay_tree_set S a = (\<exists>\<^sub>At. splay_tree t a * \<up>(bst t) * \<up>(set_tree t = S))"

lemma size_set_tree:
  "bst t \<Longrightarrow> card (set_tree t) = size t"
proof (induct t)
  case Leaf show ?case by simp
next
  case (Node t1 x2 t2)
  have "set_tree t1 \<inter> set_tree t2 = {}" using Node by fastforce
  then have size1: "card (set_tree t1 \<union> set_tree t2) = size t1 + size t2"
    using Node by (simp add: card_Un_disjoint)
  have "x2 \<notin> set_tree t1 \<union> set_tree t2" using Node by fastforce
  then show ?case using size1 by auto
qed

lemma size1_set_tree [rewrite]:
  "bst t \<Longrightarrow> card (set_tree t) + 1 = size1 t"
  using size_set_tree by auto

setup \<open>add_forward_prfstep_cond @{thm bst_splay} [with_term "splay ?a ?t"]\<close>
setup \<open>add_rewrite_rule @{thm set_splay}\<close>

lemma splay_tree_splay_rule [hoare_triple]:
  "<splay_tree_set S a * $(splay_atime (card S + 1))>
    splay_impl x a
   <splay_tree_set S>\<^sub>t" by auto2

setup \<open>add_forward_prfstep_cond @{thm bst_insert} [with_term "insert ?a ?t"]\<close>
setup \<open>add_rewrite_rule @{thm set_insert}\<close>

lemma splay_tree_insert_rule [hoare_triple]:
  "<splay_tree_set S a * $(insert_atime (card S + 1))>
    insert_impl x a
   <splay_tree_set ({x} \<union> S)>\<^sub>t" by auto2

setup \<open>add_forward_prfstep_cond @{thm bst_delete} [with_term "delete ?a ?t"]\<close>
setup \<open>add_rewrite_rule @{thm set_delete}\<close>

lemma splay_tree_delete_rule [hoare_triple]:
  "<splay_tree_set S a * $(delete_atime (card S + 1))>
    delete_impl x a
   <splay_tree_set (S - {x})>\<^sub>t" by auto2

end
