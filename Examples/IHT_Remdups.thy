theory IHT_Remdups 
  imports IHT_Red_Black_Tree IHT_Dynamic_Array_More
    "../Asymptotics/Asymptotics_Recurrences"
    IHT_Reverse
    "HOL-Library.Code_Target_Numeral"
begin

fun remdups2 :: "'a list \<Rightarrow> ('a list * 'a set)" where
  "remdups2 [] = ([],{})"
| "remdups2 (x#xs) = (let (rxs,S) = remdups2 xs in
                    (if x\<in>S then (rxs , S) else (rxs @ [x], S \<union> {x}) ))"

lemma Z: "remdups2 xs = (rev (remdups xs), set xs)"
  by (induct xs, auto)

lemma "remdups2 (rev xs) = (remdups xs, set xs)" oops


fun remdups3 :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list * 'a set)" where
  "remdups3 xs 0 = ([],{})"
| "remdups3 xs (Suc n) = (let (rxs,S) = remdups3 xs n; x = (xs ! (length xs - Suc n)) in
                    (if x \<in> S then (rxs , S) else (rxs @ [x], S \<union> {x}) ))"

                                                      
lemma kl: "Suc n \<le> length xs \<Longrightarrow>  drop (length xs - Suc n) xs = xs ! (length xs - Suc n) # drop (length xs - n) xs"
proof -
  assume a: "Suc n \<le> length xs" then
  have g: "Suc (length xs - Suc n) = length xs - n" by auto
  from a have "length xs - Suc n < length xs" by auto
  with Cons_nth_drop_Suc[of "length xs - Suc n" xs] 
  have "xs ! (length xs - Suc n) # drop (Suc (length xs - Suc n)) xs = drop (length xs - Suc n) xs"
    by blast 
  then show ?thesis using g by auto
qed


lemma z: "rev xs @ [x] = rev (x # xs)" by simp
lemma zz: "x = y \<Longrightarrow> rev x = rev y" by simp

lemma remdups3: "n\<le>length xs \<Longrightarrow> remdups3 xs n = remdups2 (drop (length xs - n) xs)"
  apply(induct n)
   apply simp apply simp unfolding Z apply (simp only: Let_def)
  apply(auto)    apply(auto intro!: zz simp add: z simp del: rev.simps)
        apply(simp_all only: kl)  by auto

lemma remdups3_correct[rewrite]: "fst (remdups3 xs (length xs)) = rev (remdups xs)"
  by (simp add: remdups3 Z)
  


fun remdups'_impl :: "('a::{zero,heap,linorder}) array \<Rightarrow> nat \<Rightarrow> (('a, unit) rbt_node ref option \<times> 'a dynamic_array) Heap"  where
  "remdups'_impl p 0 = do { 
            M \<leftarrow> tree_empty;
            A \<leftarrow> dyn_array_new;
          return (M,A) }   "
| "remdups'_impl p (Suc n) = do {
      X \<leftarrow> remdups'_impl p n;
      M \<leftarrow> return (fst X);
      A \<leftarrow> return (snd X);
      l \<leftarrow> Array_Time.len p;
      x \<leftarrow> Array_Time.nth p (l - Suc n);
      b \<leftarrow> rbt_search x M;
      (if b = None then do {
              M' \<leftarrow> rbt_insert x () M  ; A' \<leftarrow> push_array x A; return (M',A') }
               else  return (M,A) )    
    }"

fun remdups'_impl_time :: "nat \<Rightarrow> nat" where
  "remdups'_impl_time 0 = 9"
| "remdups'_impl_time (Suc n) = remdups'_impl_time n + rbt_search_time_logN (Suc n)
                                      + rbt_insert_logN (Suc n) + 28"  
 

lemma remdups'_impl_time_bound[asym_bound]: "remdups'_impl_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  apply(rule bigTheta_linear_recurrence_log[where g = "(\<lambda>n. rbt_search_time_logN (1 + n)
                                      + rbt_insert_logN (1 + n) + 28)" and N=11])
       apply simp  apply auto2
  by auto


setup \<open>fold add_rewrite_rule @{thms remdups'_impl_time.simps}\<close>
setup \<open>fold add_rewrite_rule @{thms remdups3.simps}\<close>


definition setmap where [rewrite]: "setmap S = Map (%x. if x\<in>S then Some () else None)"

lemma t: "{x. (if x \<in> set (drop (length xs - n) xs) then Some () else None) = Some ()}
      =  set (drop (length xs - n) xs)" by auto

lemma sizeofmap_ub: "n\<le>length xs \<Longrightarrow> sizeM1 (setmap (snd (remdups3 xs n))) \<le> Suc n"
  unfolding sizeM1_def setmap_def apply (auto simp: remdups3 Z)
  apply(induct n) apply (auto simp: keys_of_def) apply(simp only: kl)
  apply auto subgoal for n apply(cases "xs ! (length xs - Suc n) \<in> (set (drop (length xs - n) xs))")
     apply auto by (simp_all only: t card_insert_le_m1)  done

lemma rbt_search_time_logN_ub[resolve]: "n\<le>length xs \<Longrightarrow> rbt_search_time_logN (sizeM1 (setmap (snd (remdups3 xs n)))) \<le>  rbt_search_time_logN (Suc n) "
  apply(auto simp: sizeofmap_ub  intro!: rbt_search_time_logN_mono) by(auto simp: sizeM1_def)

lemma rbt_insert_logN_ub[resolve]: "n\<le>length xs \<Longrightarrow> rbt_insert_logN (sizeM1 (setmap (snd (remdups3 xs n)))) \<le>  rbt_insert_logN (Suc n) "
  apply(auto simp: sizeofmap_ub  intro!: rbt_insert_logN_mono) by (auto simp: sizeM1_def)

setup \<open>del_prfstep_thm @{thm rbt_map_def}\<close>
setup \<open>del_prfstep_thm @{thm rbt_in_traverse_fst}\<close>
setup \<open>del_prfstep_thm @{thm rbt_map_assn_def}\<close>

lemma remdups'_impl_rule[hoare_triple]: 
  "n\<le>length xs \<Longrightarrow> <p \<mapsto>\<^sub>a xs * $(remdups'_impl_time n)>
    remdups'_impl p n
   <\<lambda>(M,A). p \<mapsto>\<^sub>a xs * dyn_array (fst (remdups3 xs n)) A * rbt_map_assn (setmap (snd (remdups3 xs n))) M >\<^sub>t"
@proof @fun_induct "remdups3 xs n" @with
  @subgoal "(xs = xs, n = 0)"
    @have "setmap (snd (remdups3 xs 0)) = empty_map"
  @endgoal
  @subgoal "(xs = xs, n = Suc n)" 
    @have "rbt_search_time_logN (Suc n) \<ge>\<^sub>t rbt_search_time_logN (sizeM1 (setmap (snd (remdups3 xs n))))"
    @case "setmap (snd (remdups3 xs n)) \<langle>xs ! (length xs - Suc n) \<rangle> = None" @with
      @have "rbt_insert_logN (Suc n) \<ge>\<^sub>t rbt_insert_logN (sizeM1 (setmap (snd (remdups3 xs n))))"
      @have "setmap (snd (remdups3 xs n)) { xs ! (length xs - Suc n) \<rightarrow> () } = setmap (snd (remdups3 xs (Suc n)))"
    @end  
  @endgoal
  @end
@qed


definition remdups_impl :: "('a::{zero,heap,linorder}) array \<Rightarrow> 'a array Heap"  where [rewrite]:
    "remdups_impl p = do {
        len \<leftarrow> Array_Time.len p;
        (_,A) \<leftarrow> remdups'_impl p len;
        r \<leftarrow> destroy A;
        rev_impl r
    }"
 
lemma rev_impl_time_absch[resolve]: "rev_time (length xs) \<ge> rev_time (length (remdups xs))"
  by(rule rev_impl_time_mono, simp)
  

definition remdups_impl_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "remdups_impl_time n = 4 + remdups'_impl_time n + rev_time n"

lemma remdups_impl_time_bound[asym_bound]: 
    "remdups_impl_time \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding remdups_impl_time_def by auto2

lemma rev_rev[rewrite]: "rev (rev xs) = xs" by simp

lemma remdups_impl_rule[hoare_triple]: "<p \<mapsto>\<^sub>a xs * $(remdups_impl_time (length xs))>
    remdups_impl p
   <\<lambda>r. p \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a remdups xs>\<^sub>t"
@proof 
  @have "rev_time (length xs) \<ge>\<^sub>t rev_time (length (remdups xs))" 
@qed


declare rbt_ins.simps[code]
declare IHT_Red_Black_Tree.rbt_search.simps[code]

definition "remdups_int_impl \<equiv> remdups_impl :: int array \<Rightarrow> _"

export_code integer_of_int int_of_integer remdups_int_impl
  in "SML_imp"  module_name REMDUPS (* does not work properly! *)

end
