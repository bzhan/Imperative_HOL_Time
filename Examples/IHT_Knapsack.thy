(* Author: Maximilian P. L. Haslbeck *)

theory IHT_Knapsack
  imports
    "../Functional/Knapsack"
    "../SepLogicTime/SLTC_Main"
    "../Asymptotics/Asymptotics_Recurrences"
    IHT_Matrix
begin

section \<open>functional hybrid version using list of lists\<close>

definition kna' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list list \<Rightarrow> nat" where [rewrite]:
  "kna' i j W xs = (case i of
     0 \<Rightarrow> 0
   | Suc i' \<Rightarrow> 
     (if j < w (Suc i')
      then \<comment> \<open>cant be added\<close>
        (xs ! i') ! j
      else \<comment> \<open>can be added\<close>
        max ((xs ! i') ! j) (v (Suc i') + ((xs ! i') ! (j - w (Suc i')))))
    )"

lemma kna'_correct:
  "i < length xs \<Longrightarrow> \<forall>ii\<le>i. length (xs!ii) = W \<Longrightarrow>
   \<forall>ii<i. \<forall>jj<W. (xs!ii)!jj = knapsack (ii,jj) \<Longrightarrow>
   j<W \<Longrightarrow> kna' i j W xs = knapsack (i,j)"
  unfolding kna'_def by (cases i) auto

fun fillrow_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "fillrow_fun i 0 W xs = xs"
| "fillrow_fun i (Suc j) W xs = 
   (let xs' = fillrow_fun i j W xs;
        V = kna' i j W xs'
      in xs'[i:=((xs'!i)[j:=V])])"
declare fillrow_fun.simps [rewrite]

lemma fillrow_fun_length_o [rewrite]:
  "i < length xs \<Longrightarrow> length (fillrow_fun i j W xs) = length xs"
  apply (induct j arbitrary: xs i) apply auto
  by (metis length_list_update) 

lemma fillrow_fun_length_i:
  "i < length xs \<Longrightarrow> length (fillrow_fun i j W xs ! ii) = length (xs ! ii)"
  apply(induct j arbitrary: xs i) apply auto
  by (metis fillrow_fun_length_o length_list_update nth_list_update) 

lemma fillrow_fun_correct:
  "i < length xs \<Longrightarrow>
   \<forall>ii\<le>i. length (xs!ii) = W \<Longrightarrow>   \<comment> \<open> rows have correct length \<close>
   \<forall>ii<i. \<forall>jj<W. (xs!ii)!jj = knapsack (ii,jj) \<Longrightarrow>
   j\<le>W \<Longrightarrow> (ii<i\<and>jj<W) \<or> (ii=i\<and>jj<j) \<Longrightarrow> ((fillrow_fun i j W xs) ! ii) ! jj = knapsack (ii,jj)"
proof (induct j arbitrary: ii jj xs)
  case 0
  then show ?case by auto
next
  case (Suc j)
  let ?xs' = "fillrow_fun i j W xs"
  let ?V = "kna' i j W ?xs'"
  have V: "?V = knapsack (i,j)" apply(rule kna'_correct)
    subgoal using fillrow_fun_length_o Suc(2) by auto
    subgoal using fillrow_fun_length_i Suc(2,3) by auto
    subgoal apply safe apply (rule Suc(1)) using Suc(2-5) by auto
    subgoal using Suc(5) by auto done
  have F: "fillrow_fun i (Suc j) W xs = ?xs'[i:=((?xs'!i)[j:=?V])]"
    apply auto by metis
  show ?case
  proof(cases "ii<i")
    case True
    then show ?thesis unfolding F apply simp apply(rule Suc(1)[OF Suc(2,3,4), of ii jj])
          using Suc(5) Suc(6) by auto
  next
    case False
    with Suc(6) have I: "ii=i" "jj<Suc j" by auto
    show ?thesis 
    proof(cases "jj<j")  
      case True
      with I show ?thesis unfolding F using fillrow_fun_length_o Suc(2) apply auto
          using Suc(1)[OF Suc(2,3,4), of ii jj] Suc(5) by auto
    next
      case False 
      with I have t: "jj=j" "ii=i" by auto
      have rw: "list_update (fillrow_fun i j W xs)
                 i (list_update (fillrow_fun i j W xs ! i) j ?V) ! i ! j
            = knapsack (i,j)" unfolding V using Suc(6) Suc(2,3,5) using fillrow_fun_length_o 
        using fillrow_fun_length_i[OF Suc(2)] by auto 
      show ?thesis unfolding F t rw by simp
    qed 
  qed 
qed
 
fun knapsack''_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "knapsack''_fun 0 W xs = xs"
| "knapsack''_fun (Suc i) W xs =
   (let xs' = knapsack''_fun i W xs in
      fillrow_fun i W W xs')"
declare knapsack''_fun.simps [rewrite]

lemma knapsack''_fun_length_o [rewrite]:
  "i \<le> length xs \<Longrightarrow> length (knapsack''_fun i W xs) = length xs"
  apply (induct i arbitrary: xs) by (auto simp: fillrow_fun_length_o)

lemma knapsack''_fun_length_i:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> length (knapsack''_fun i W xs ! j) = length (xs ! j)"
  apply(induct i arbitrary: xs j) apply (auto)  
  apply(subst fillrow_fun_length_i) by (auto simp: knapsack''_fun_length_o)

lemma knapsack''_fun_correct:
  "i \<le> length xs \<Longrightarrow>
   \<forall>ii<i. length (xs!ii) = W \<Longrightarrow>  \<comment> \<open>rows have correct length\<close>
   jj<W \<Longrightarrow> ii<i \<Longrightarrow> ((knapsack''_fun i W xs) ! ii) ! jj = knapsack (ii,jj)"
proof (induct i arbitrary: xs ii jj) 
  case (Suc i) 
  let ?xs' = "knapsack''_fun i W xs"
  have i: "i < length ?xs'" using knapsack''_fun_length_o Suc(2) by auto
  have A: "\<forall>ii\<le>i. length (knapsack''_fun i W xs ! ii) = W"
    using Suc(2,3) knapsack''_fun_length_i by auto
  thm Suc(1) 
  have B: "\<forall>ii<i. \<forall>jj<W. knapsack''_fun i W xs ! ii ! jj = knapsack (ii, jj)"
    apply safe apply(rule Suc(1)) using Suc(2-5) by auto
  thm fillrow_fun_correct[OF i A B, of W ii jj] 
  show ?case apply simp
    apply(rule fillrow_fun_correct)
        apply (rule i A B)+ using Suc(4,5) by auto
qed simp

definition knapsack_full_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat" where [rewrite]:
  "knapsack_full_fun i W = (let 
      xs = empty_matrix (Suc i) (Suc W) (undefined::nat);
      xs' = knapsack''_fun (Suc i) (Suc W) xs
     in 
       (xs' ! i) ! W
    )"

lemma knapsack_full_fun_correct:
  "knapsack_full_fun i W = knapsack (i,W)"
  unfolding knapsack_full_fun_def apply (simp del: knapsack''_fun.simps)
  apply(rule knapsack''_fun_correct) unfolding empty_matrix_def 
  by (simp_all del: replicate.simps) 

section \<open>functional hybrid version using list of lists\<close>

definition kna'_impl :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat matrix \<Rightarrow> nat Heap" where
  "kna'_impl i j W a = (case i of
     0 \<Rightarrow> return 0
   | Suc i' \<Rightarrow> 
     (if j < w (Suc i')
      then \<comment> \<open> cant be added \<close>
        nth_matrix i' j a
      else do {  \<comment> \<open> can be added \<close>
        x \<leftarrow> nth_matrix i' j a;
        y \<leftarrow> nth_matrix i' (j - w (Suc i')) a;
        return (max x (v (Suc i') + y))
      }))"

lemma kna'_impl_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j < n \<Longrightarrow>
   <matrix_assn n xs p * $3>
    kna'_impl i j W p
   <\<lambda>r. matrix_assn n xs p * \<up>(r = kna' i j W xs)>\<^sub>t"
@proof @cases i @qed

setup \<open>del_prfstep_thm @{thm kna'_def}\<close>  

fun fillrow_impl :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat matrix \<Rightarrow> unit Heap" where
  "fillrow_impl i 0 W p = return ()"
| "fillrow_impl i (Suc j) W p = do {
     fillrow_impl i j W p;
     V \<leftarrow> kna'_impl i j W p;
     upd_matrix  i j V p
   }"

fun fill_impl_time :: "nat \<Rightarrow> nat" where
  "fill_impl_time 0 = 1"
| "fill_impl_time (Suc n) = fill_impl_time n + 5"
declare fill_impl_time.simps [rewrite]

lemma fill_impl_time_closedform: "fill_impl_time n = 1 + 5 * n"
  by (induct n) auto

lemma fill_impl_time_bound [asym_bound]:  "(\<lambda>n. fill_impl_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: fill_impl_time_closedform) auto2

lemma fill_impl_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j \<le> n \<Longrightarrow>
   <matrix_assn n xs p * $(fill_impl_time j)>
    fillrow_impl i j W p 
   <\<lambda>_. matrix_assn n (fillrow_fun i j W xs) p>\<^sub>t"
@proof @induct j @qed

setup \<open>fold del_prfstep_thm @{thms fill_impl_time.simps}\<close>

fun knapsack''_impl :: "nat \<Rightarrow> nat \<Rightarrow> nat matrix \<Rightarrow> unit Heap" where
  "knapsack''_impl 0 W p = return ()"
| "knapsack''_impl (Suc i) W p = do {
     knapsack''_impl i W p;
     fillrow_impl i W W p
   }"

fun knapsack''_impl_time :: "nat \<times> nat \<Rightarrow> nat" where
  "knapsack''_impl_time (0, W) = 1"
| "knapsack''_impl_time (Suc n, W) = knapsack''_impl_time (n,W) + fill_impl_time W"
declare knapsack''_impl_time.simps [rewrite]

lemma knapsack''_impl_time_bound [asym_bound]: "knapsack''_impl_time \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (n * m))"
  apply (rule bivariateTheta[where N=0])
  using fill_impl_time_bound by (auto simp: eventually_nonneg_def eventually_prod_sequentially) 

lemma knapsack''_impl_rule [hoare_triple]:
  "i \<le> length xs \<Longrightarrow>
   <matrix_assn W xs p * $(knapsack''_impl_time (i,W))>
    knapsack''_impl i W p
   <\<lambda>_. matrix_assn W (knapsack''_fun i W xs) p >\<^sub>t"
@proof @induct i @qed

setup \<open>fold del_prfstep_thm @{thms knapsack''_impl_time.simps}\<close>

definition knapsack_full_impl :: "nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "knapsack_full_impl i W = do {
     p \<leftarrow> init_matrix (Suc i) (Suc W) undefined;
     knapsack''_impl (Suc i) (Suc W) p;
     nth_matrix i W p 
   }"
 
fun knapsack_full_impl_time :: "nat \<times> nat \<Rightarrow> nat" where
  "knapsack_full_impl_time (i,W) =
     init_matrix_time (i+1,W+1) +
     knapsack''_impl_time (i+1,W+1) + 1"
declare knapsack_full_impl_time.simps [rewrite]

lemma knapsack_full_impl_time_asym [asym_bound]:
  "knapsack_full_impl_time \<in> \<Theta>\<^sub>2(\<lambda>x. real (fst x * snd x))"
  apply (subst surjective_pairing) unfolding knapsack_full_impl_time.simps by auto2

lemma knapsack_full_impl_rule':
  "<$(knapsack_full_impl_time (i,W))>
    knapsack_full_impl i W
   <\<lambda>r. \<up>(r = knapsack_full_fun i W)>\<^sub>t" by auto2

lemma knapsack_full_impl_rule [hoare_triple]:
  "<$(knapsack_full_impl_time (i,W))>
    knapsack_full_impl i W
   <\<lambda>r. \<up>(r = OPT i W)>\<^sub>t"
  using knapsack_full_impl_rule' knapsack_full_fun_correct knapsack_correct by metis

end (* Theory *)
