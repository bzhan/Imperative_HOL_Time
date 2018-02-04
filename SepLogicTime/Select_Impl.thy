(* Author: Max P.L. Haslbeck, Bohua Zhan
*)
section \<open>Imperative Implementation of the Median-of-Medians Selection Algorithm with Runtime Analysis\<close>
theory Select_Impl
  imports Select DynamicArray2 LinkedList
begin

subsection {* Choose the nth element by insertion sort *}

definition select_small :: "'a::{ord,heap} list \<Rightarrow> nat \<Rightarrow> 'a Heap" where [sep_proc]:
  "select_small xs n = do {
     p \<leftarrow> os_insert_sort xs;
     return (p ! n)
    }"

definition select_small_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "select_small_time n = os_insert_sort_time n + 1"

lemma select_small_rule [hoare_triple]:
  "length xs \<le> B \<Longrightarrow> n < length xs \<Longrightarrow>
   <$(select_small_time B)>
   select_small xs n
   <\<lambda>r. \<up>(r = sort xs ! n)>\<^sub>t"
@proof
  @have "os_insert_sort_time B \<ge>\<^sub>t os_insert_sort_time (length xs)"
@qed
setup {* del_prfstep_thm @{thm select_small_time_def} *}

subsection {* Extract sublist from l to r *}

function extract_sublist :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list Heap" where
  "extract_sublist a l r = (if r \<le> l then return [] else do {
     xs \<leftarrow> extract_sublist a (l+1) r;
     x \<leftarrow> Array.nth a l;
     return (x#xs)
   })"
by auto
termination apply (relation "Wellfounded.measure (\<lambda>(a, l, r). (r - l))")  by auto

declare extract_sublist.simps [sep_proc]
setup {* add_fun_induct_rule (@{term extract_sublist}, @{thm extract_sublist.induct}) *}

definition extract_sublist_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "extract_sublist_time n = 2 * n + 1"

lemma extract_sublist_time_monotonic [backward]:
  "n \<le> m \<Longrightarrow> extract_sublist_time n \<le> extract_sublist_time m" by auto2

lemma extract_sublist_correct [hoare_triple]:
  "r \<le> length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs * $(extract_sublist_time (r - l))> 
   extract_sublist a l r
   <\<lambda>rs. a \<mapsto>\<^sub>a xs * \<up>(rs = sublist l r xs)>\<^sub>t"
@proof @fun_induct "extract_sublist a l r" @with
  @subgoal "(a = a, l = l, r = r)"
    @case "r \<le> l"
    @have "2 * (r - l) \<ge>\<^sub>t 2 * (r - (l + 1)) + 2"
  @end
@qed

setup {* del_prfstep_thm @{thm extract_sublist_time_def} *}

subsection {* nth term of chop *}

setup {* register_wellform_data ("chop n xs", ["n > 0"]) *}
setup {* fold add_rewrite_rule @{thms chop.simps(1,3)} *}

lemma nth_chop:
  "i < length (chop 5 xs) \<Longrightarrow> chop 5 xs ! i = take 5 (drop (5*i) xs)"
@proof @induct i arbitrary xs @with
  @subgoal "i = 0" @case "xs = []" @endgoal
  @subgoal "i = Suc i"
    @case "xs = []"
    @have "tl (chop 5 xs) = chop 5 (drop 5 xs)"
    @have "chop 5 xs ! (Suc i) = chop 5 (drop 5 xs) ! i"
    @have "chop 5 (drop 5 xs) ! i = take 5 (drop (5 * i) (drop 5 xs))"
  @endgoal @end
@qed

lemma nth_chop_length [resolve]:
  "i < length (chop 5 xs) \<Longrightarrow> chop 5 xs ! i \<noteq> []"
  by (metis chop_elem_not_Nil in_set_conv_nth)

lemma take_drop_to_sublist [rewrite]:
  "i < length (chop 5 xs) \<Longrightarrow> chop 5 xs ! i = sublist (5*i) (5*i+(min 5 (length xs-5*i))) xs"
  by (simp add: add.commute min_def sublist_def take_drop nth_chop)

setup {* fold del_prfstep_thm @{thms chop.simps(1,3)} *}

subsection {* Array-based refinement of medians of chop *}

fun chopmed5_aux_fun :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a::linorder list" where 
  "chopmed5_aux_fun xs ys 0 = ys"
| "chopmed5_aux_fun xs ys (Suc n) =
    (let l = min 5 (length xs-5*n);
         m = median (sublist (5*n) (5*n+l) xs) in
       list_update (chopmed5_aux_fun xs ys n) n m)"
setup {* fold add_rewrite_rule @{thms chopmed5_aux_fun.simps} *}

lemma length_chopmed5_aux_fun [rewrite_arg]:
  "length (chopmed5_aux_fun xs ys n) = length ys"
@proof @induct n @qed

lemma chopmed5_aux_fun_ind [rewrite]:
  "n \<le> length ys \<Longrightarrow> length ys = length (chop 5 xs) \<Longrightarrow>
   i < n \<Longrightarrow> chopmed5_aux_fun xs ys n ! i = map median (chop 5 xs) ! i"        
@proof @induct n @qed

lemma chopmed5_aux_fun_correct [rewrite]:
  "length ys = length (chop 5 xs) \<Longrightarrow> chopmed5_aux_fun xs ys (length ys) = map median (chop 5 xs)"
@proof
  @have "length (chopmed5_aux_fun xs ys (length ys)) = length (map median (chop 5 xs))"
@qed

subsection {* Imperative version of chopmed5 *}

definition medchop :: "'a::{linorder,heap} array \<Rightarrow> nat \<Rightarrow> 'a Heap" where [sep_proc]:
  "medchop a n = do {
     l \<leftarrow> Array.len a;
     ls \<leftarrow> extract_sublist a (5*n) (5*n+(min 5 (l-5*n)));
     select_small ls (((min 5 (l-5*n))-1) div 2)
   }"

definition medchop_time :: nat where [rewrite]:
  "medchop_time = extract_sublist_time 5 + select_small_time 5 + 1"

lemma medchop_time81: "medchop_time = 81" 
  unfolding medchop_time_def extract_sublist_time_def
    extract_sublist_time_def select_small_time_def os_insert_sort_time_def by simp


lemma helper2 [backward]: "(n::nat) > 0 \<Longrightarrow> (n-1) div 2 < n" by simp

lemma median_sort [backward]: "xs \<noteq> [] \<Longrightarrow> median xs = sort xs ! ((length xs - 1) div 2)"
  by (simp add: Select.select_def median_def)

lemma chop_length_prop [resolve]: "n < length (chop 5 xs) \<Longrightarrow> 5 * n \<le> length xs"
  using nth_chop nth_chop_length by fastforce

lemma medchop_rule' [hoare_triple]:
  "n < length (chop 5 xs) \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * $medchop_time>
    medchop a n
   <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = median (chop 5 xs ! n) )>\<^sub>t"
@proof
  @let "l = length xs" "sz = min 5 (l - 5*n)"
  @have "5*n + sz \<le> length xs" @with
    @have "5*n + sz \<le> 5*n + (l - 5*n)"
  @end
  @have "extract_sublist_time 5 \<ge>\<^sub>t extract_sublist_time ((5*n+sz)-5*n)"
@qed

fun chopmed5_aux :: "'a::{linorder,heap} array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> ('a array) Heap" where
  "chopmed5_aux a b 0 = (return b)"
| "chopmed5_aux a b (Suc n) = do {
     x \<leftarrow> medchop a n;
     b' \<leftarrow> chopmed5_aux a b n;
     Array.upd n x b'
   }"
declare chopmed5_aux.simps [sep_proc]

lemma chopmed5_aux_ind [hoare_triple]:
  "length ys = length (chop 5 xs) \<Longrightarrow> i \<le> length ys \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys * $(i*(medchop_time+1) + 1)>
    chopmed5_aux a b i
   <\<lambda>r. a \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a chopmed5_aux_fun xs ys i>\<^sub>t" 
@proof @induct i @qed

definition chop5_length :: "nat \<Rightarrow> nat" where
  "chop5_length n = nat \<lceil>n / real 5\<rceil>"


lemma chop_length_rel [rewrite_back]: "chop5_length n = (n + 4) div 5" 
  unfolding chop5_length_def by linarith
 
lemma chop5_length_bound [asym_bound]: "(\<lambda>n. chop5_length n) \<in> \<Theta>(\<lambda>n. n)" 
  unfolding chop_length_rel by auto2

lemma chop5_length_mono: "n \<le> m \<Longrightarrow> chop5_length n \<le> chop5_length m"
  unfolding chop5_length_def by linarith

lemma chop_length_rule [rewrite_back]:
  "length (chop 5 xs) = chop5_length (length xs)"
  by (simp add: length_chop chop5_length_def)

definition chopmed5_aux_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "chopmed5_aux_time n = chop5_length n * (medchop_time + 1) + 1"

lemma chopmed5_aux_correct [hoare_triple]:
  "length ys = length (chop 5 xs) \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys * $(chopmed5_aux_time (length xs))>
    chopmed5_aux a b (length ys)
   <\<lambda>r. a \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a map median (chop 5 xs)>\<^sub>t" by auto2

lemma chopmed5_aux_time_bound [asym_bound]: "(\<lambda>n. chopmed5_aux_time n) \<in> \<Theta>(\<lambda>n. n)"
  unfolding chopmed5_aux_time_def medchop_time81 apply simp by auto2 

setup {* del_prfstep_thm @{thm chopmed5_aux_time_def} *}
 
definition chopmed5 :: "'a::{linorder,heap} array \<Rightarrow> 'a array Heap" where [sep_proc]:
  "chopmed5 a = do {
     len \<leftarrow> Array.len a;
     b \<leftarrow> Array.new ((len + 4) div 5) undefined;
     chopmed5_aux a b ((len + 4) div 5)
   }"

definition chopmed5_time :: "nat \<Rightarrow> nat" where [unfold]:
  "chopmed5_time l = 2 + ((l + 4) div 5) + chopmed5_aux_time l"

lemma chopmed5_runtime_mono: "n \<le> m \<Longrightarrow> chopmed5_time n \<le> chopmed5_time m"
  unfolding chopmed5_aux_time_def chopmed5_time_def medchop_time_def extract_sublist_time_def
      select_small_time_def
  by (simp add: add_le_mono os_insert_sort_time_monotonic chop5_length_mono) 

lemma chopmed5_rule [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * $(chopmed5_time (length xs))>
    chopmed5 a
   <\<lambda>r. a \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a (map median (chop 5 xs))>\<^sub>t"
@proof @unfold "chopmed5_time (length xs)" @qed

lemma chopmed5_time_bound [asym_bound]: "(\<lambda>n. chopmed5_time n) \<in> \<Theta>(\<lambda>n. n)"
  unfolding chopmed5_time_def by auto2

definition filter_impl :: "'a::heap array \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a array Heap" where [sep_proc]:
  "filter_impl a P = do {
     d <- dfilter_impl a P;
     destroy d
   }"  

definition filter_impl_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "filter_impl_time n = dfilter_impl_time n + 3"

lemma filter_impl_rule [hoare_triple]:
  "<a \<mapsto>\<^sub>a as * $(filter_impl_time (length as))>
   filter_impl a P
   <\<lambda>r. a \<mapsto>\<^sub>a as * r \<mapsto>\<^sub>a filter P as>\<^sub>t" by auto2

lemma filter_impl_time_bound [asym_bound]: "(\<lambda>n. filter_impl_time n) \<in> \<Theta>(\<lambda>n. n)"
  unfolding filter_impl_time_def by auto2

setup {* del_prfstep_thm @{thm filter_impl_time_def} *}

definition threeway_partition_impl :: "'a \<Rightarrow> ('a::{heap,linorder}) array \<Rightarrow> ('a array * 'a array * 'a array) Heap" where [sep_proc]:
 "threeway_partition_impl med a = do {
      ls \<leftarrow> filter_impl a (\<lambda>x. x < med);
      es \<leftarrow> filter_impl a (\<lambda>x. x = med);
      gs \<leftarrow> filter_impl a (\<lambda>x. x > med);
      return (ls, es, gs)
    }"

definition [rewrite]: "threeway_partition_impl_time l = 1 + 3 * filter_impl_time l"

lemma threeway_partition_impl_time_mono:
  "n \<le> m \<Longrightarrow> threeway_partition_impl_time n \<le> threeway_partition_impl_time m"
  unfolding filter_impl_time_def dfilter_impl_time_def threeway_partition_impl_time_def by auto

lemmas [rewrite] = threeway_partition_def

lemma threeway_partition_impl_rule [hoare_triple]: 
  "<a \<mapsto>\<^sub>a as * $ (threeway_partition_impl_time (length as))>
    threeway_partition_impl med a
   <\<lambda>r. a \<mapsto>\<^sub>a as * fst r \<mapsto>\<^sub>a fst (threeway_partition med as)
                 * fst (snd r) \<mapsto>\<^sub>a fst (snd (threeway_partition med as))
                 * snd (snd r) \<mapsto>\<^sub>a snd (snd (threeway_partition med as))>\<^sub>t" by auto2

lemma threeway_partition_impl_time_bound [asym_bound]:
  "(\<lambda>n. threeway_partition_impl_time n) \<in> \<Theta>(\<lambda>n. n)"
  unfolding threeway_partition_impl_time_def by auto2

setup {* del_prfstep_thm @{thm threeway_partition_impl_time_def} *}

subsection \<open>The deterministic linear-time selection algorithm\<close>               

function select_time :: "nat \<Rightarrow> nat" where
  "n \<le> 23 \<Longrightarrow> select_time n = n + 1 + 1 + select_small_time n"
| "n > 23 \<Longrightarrow> select_time n = chopmed5_time n + threeway_partition_impl_time n + 5 +
                (select_time ((n + 4) div 5) +
                 select_time (((7*n) + 9) div 10 + 6))" (* recursive call *)
  by force simp_all
  termination by (relation "Wellfounded.measure (\<lambda>n. n)") auto

definition select_time' :: "nat \<Rightarrow> real" where
  "select_time' n = real (select_time n)"

lemma c: "((7*n) + 9) div 10 = nat \<lceil>0.7 * n\<rceil>"
         "(n + 4) div 5 = nat \<lceil>n / 5\<rceil>" by linarith+

lemma select_time_Theta: "select_time' \<in> \<Theta>(\<lambda>n. real n)"
  apply (master_theorem2 3 recursion: select_time.simps(2) rew: select_time'_def c)
  prefer 4 apply auto2
  by (simp_all add: select_time'_def filter_impl_time_def)

lemma select_time_mono[backward]: "n \<le> m \<Longrightarrow> select_time n \<le> select_time m" 
proof(induct m arbitrary: n rule: less_induct)
  case (less m)
  show ?case
  proof(cases "m\<le>23")
    case True
    with less(2) show ?thesis
      by (auto simp add: select_small_time_def os_insert_sort_time_monotonic add_le_mono)
  next
    case False
    note m23 = this
    show ?thesis
    proof(cases "n\<le>23")
      case True
      have a: "((7*m) +9) div 10 + 6 < m"
          "23 \<le> ((7*m) +9) div 10 + 6" apply(simp add: c) using m23 by linarith+
      have "select_time n \<le> select_time 23" apply(rule less(1))
        using m23 True by auto
      also from less(1)[OF a] have "\<dots> \<le> select_time (((7*m) +9) div 10 + 6)" .
      also from m23 have "\<dots> \<le> select_time m" by simp
      finally show ?thesis .
    next
      case False
      from m23 False less(2) have "(m + 4) div 5 < m"
              "(n + 4) div 5 \<le> (m + 4) div 5" by linarith+
      note 1 = less(1)[OF this]
      from m23 False less(2) have "((7*m) +9) div 10 + 6 < m"
              "((7*n) +9) div 10 + 6 \<le> ((7*m) +9) div 10 + 6" by linarith+
      note 2 = less(1)[OF this]
      note 3 = chopmed5_runtime_mono[OF less(2)] 
      note 4 = threeway_partition_impl_time_mono[OF less(2)]
      from m23 False show ?thesis apply simp
        using 1 2 3 4 by auto
    qed
  qed
qed

partial_function (heap) select :: "nat \<Rightarrow> ('a::{heap,linorder}) array \<Rightarrow> 'a Heap" where [sep_proc]:
  "select k a = do {
     len \<leftarrow> Array.len a;
     if len \<le> 23 then do {
       alist \<leftarrow> Array.freeze a;
       select_small alist k
     }
     else do {
       medlist \<leftarrow> chopmed5 a;
       med \<leftarrow> select (((len + 4) div 5 - 1) div 2) medlist;
       (ls, es, gs) \<leftarrow> threeway_partition_impl med a;
       ls_len \<leftarrow> Array.len ls;
       es_len \<leftarrow> Array.len es;
       gs_len \<leftarrow> Array.len gs;
       if k < ls_len then
         select k ls
       else if k < ls_len + es_len then
         return med
       else
         select (k - ls_len - es_len) gs
     }
   }"

setup {* add_fun_induct_rule (@{term fast_select}, @{thm fast_select.induct}) *}

lemma estim' [backward]:
  "xs \<noteq> [] \<Longrightarrow>
   length [y\<leftarrow>xs. y < fast_select (((length xs + 4) div 5 - 1) div 2) (map median (chop 5 xs))] \<le> (7 * (length xs) + 9) div 10 + 6"
  apply(rule size_less_greater_median_of_medians_5[where med=median, unfolded c[symmetric]])
  subgoal by blast
  subgoal apply(subst fast_select_correct) apply (simp add: length_chop) apply linarith 
    using median_def[where xs="map median (chop 5 xs)", simplified length_map length_chop, simplified, symmetric]
    by (auto simp: c)
  done

lemma estim'' [backward]:
  "xs \<noteq> [] \<Longrightarrow>
   length [y\<leftarrow>xs . y > fast_select (((length xs + 4) div 5 - 1) div 2)  (map median (chop 5 xs))] \<le> (7 * (length xs) + 9) div 10 + 6"
  apply(rule size_less_greater_median_of_medians_5[where med=median, unfolded c[symmetric]])
  subgoal by blast
  subgoal apply(subst fast_select_correct) apply (simp add: length_chop) apply linarith 
    using median_def[where xs="map median (chop 5 xs)", simplified length_map length_chop, simplified, symmetric] 
    by (auto simp: c)
  done

lemma length_filter_split:
  fixes xs :: "'a::linorder list"
  shows "length xs = length (filter (\<lambda>y. y < x) xs) + length (filter (\<lambda>y. y = x) xs) + length (filter (\<lambda>y. y > x) xs)"
proof -
  have i: "\<And>xa. (\<not> xa < x \<and> xa = x) = (xa = x)"
          "\<And>xa. (\<not> xa < x \<and> xa \<noteq> x) = (xa > x)" by auto
  have "mset xs = mset (filter (\<lambda>y. y < x) xs)
         + (mset (filter (\<lambda>y. y = x) (filter (\<lambda>y. ~ y < x) xs)) + mset (filter (\<lambda>y. ~ y = x) (filter (\<lambda>y. ~ y < x) xs)))"
    by (auto simp del: filter_filter) 
  also have "\<dots> = mset (filter (\<lambda>y. y < x) xs) + mset (filter (\<lambda>y. y = x) xs)
         + mset (filter (\<lambda>y. y > x) xs)"
    apply(subst filter_filter)+ apply auto by (auto simp add: i) 
  finally have a: "mset xs = mset (filter (\<lambda>y. y < x) xs) + mset (filter (\<lambda>y. y = x) xs)
         + mset (filter (\<lambda>y. y > x) xs)" by auto
  have "length xs = size (mset xs)" by auto
  also have "\<dots> = size (mset (filter (\<lambda>y. y < x) xs) + mset (filter (\<lambda>y. y = x) xs)
         + mset (filter (\<lambda>y. y > x) xs))" using a by auto
  finally show ?thesis by simp
qed

lemma k_inbounds [backward2]:
  fixes x :: "'a::linorder"
  shows "k \<ge> length (filter (\<lambda>y. y < x) xs) + length (filter (\<lambda>y. y = x) xs) \<Longrightarrow>
         k < length xs \<Longrightarrow>
         k - length (filter (\<lambda>y. y < x) xs) - length (filter (\<lambda>y. y = x) xs) < length (filter (\<lambda>y. y > x) xs)"
  by (simp add: length_filter_split[of xs x])

setup {* add_unfolding_rule @{thm fast_select.simps} *}
setup {* fold add_rewrite_rule @{thms select_time.simps} *}
  
lemma n_div_5_pos [backward]: "(n::nat) > 0 \<Longrightarrow> (n + 4) div 5 > 0" by linarith

declare [[hoare_shadowing]]
lemma select_rule_aux [hoare_triple]:
  "k < length as \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * $(select_time (length as))>
    select k a
   <\<lambda>r. a \<mapsto>\<^sub>a as * \<up>(r = fast_select k as)>\<^sub>t"
@proof @fun_induct "fast_select k as" arbitrary a @with
  @subgoal "(k = k, as = as)"
  @unfold "fast_select k as"
  @let "n = length as"
  @case "n \<le> 23"
  @let "x = fast_select (((n + 4) div 5 - 1) div 2) (map median (chop 5 as))"
  @let "ls = filter (\<lambda>y. y < x) as"
  @let "es = filter (\<lambda>y. y = x) as"
  @let "gs = filter (\<lambda>y. y > x) as"

  @have "((n + 4) div 5 - 1) div 2 < (n + 4) div 5"
  @case "k < length ls" @with  (* Recursive call on ls *)
    @have "select_time ((7 * n + 9) div 10 + 6) \<ge>\<^sub>t select_time (length ls)"
  @end
  @case "k < length ls + length es"
  @case "k \<ge> length ls + length es" @with  (* Recursive call on gs *)
    @have "select_time ((7 * n + 9) div 10 + 6) \<ge>\<^sub>t select_time (length gs)"
    @have "k - length ls - length es < length gs"
  @end @end
@qed
declare [[hoare_shadowing = false]]

setup {* add_rewrite_rule @{thm fast_select_correct} *}
lemma select_rule [hoare_triple]:
  "k < length as \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * $(select_time (length as))>
    select k a
   <\<lambda>r. a \<mapsto>\<^sub>a as * \<up>(r = Select.select k as)>\<^sub>t" by auto2
setup {* del_prfstep_thm @{thm fast_select_correct} *}

corollary select_time_bound [asym_bound]:
  "(\<lambda>n. select_time n) \<in> \<Theta>(\<lambda>n. n)"
  using select_time_Theta unfolding select_time'_def by blast

end
