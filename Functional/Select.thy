section \<open>The Median-of-Medians Selection Algorithm\<close>
theory Select
  imports "Median_Of_Medians_Selection.Median_Of_Medians_Selection"
begin

subsection \<open>Median-of-medians selection algorithm\<close>

text \<open>
  The fast selection function now simply computes the median-of-medians of the chopped-up list
  as a pivot, partitions the list into with respect to that pivot, and recurses into one of 
  the resulting sublists.
\<close>
function fast_select where
  "fast_select l k xs = (
     if length xs \<le> max l 2 then
       sort xs ! k
     else
       let x = fast_select l (((length xs + 4) div 5 - 1) div 2) (map median (chop 5 xs));
           (ls, es, gs) = threeway_partition x xs
       in
         if k < length ls then fast_select l k ls 
         else if k < length ls + length es then x
         else fast_select l (k - length ls - length es) gs
      )"
  by auto

text \<open>
  The correctness of this is obvious from the above theorems, but the proof is still
  somewhat complicated by the fact that termination depends on the correctness of the
  function.
\<close>
lemma fast_select_correct_aux:
  assumes "fast_select_dom (l, k, xs)" "k < length xs"
  shows   "fast_select l k xs = select k xs"
  using assms
proof induction
  case (1 l k xs)
  show ?case
  proof (cases "length xs \<le> max l 2")
    case True
    thus ?thesis using "1.prems" "1.hyps"
      by (subst fast_select.psimps) (auto simp: select_def)
  next
    case False
    define x where
      "x = fast_select l (((length xs + 4) div 5 - Suc 0) div 2) (map median (chop 5 xs))"
    define ls where "ls = filter (\<lambda>y. y < x) xs"
    define es where "es = filter (\<lambda>y. y = x) xs"
    define gs where "gs = filter (\<lambda>y. y > x) xs"
    define nl ne where "nl = length ls" and "ne = length es"
    note defs = nl_def ne_def x_def ls_def es_def gs_def
    have tw: "(ls, es, gs) = threeway_partition (fast_select l (((length xs + 4) div 5 - 1) div 2)
                               (map median (chop 5 xs))) xs"
      unfolding threeway_partition_def defs One_nat_def ..
    have tw': "(ls, es, gs) = threeway_partition x xs"
      by (simp add: tw x_def)

    have "fast_select l k xs = (if k < nl then fast_select l k ls else if k < nl + ne then x
                                else fast_select l (k - nl - ne) gs)" using "1.hyps" False
      apply (subst fast_select.psimps) 
      by (simp_all add: threeway_partition_def defs [symmetric])
    also have "\<dots> = (if k < nl then select k ls else if k < nl + ne then x 
                       else select (k - nl - ne) gs)"
    proof (intro if_cong refl)
      assume *: "k < nl"
      show "fast_select l k ls = select k ls"
        by (rule 1; (rule refl tw)?) 
           (insert *, auto simp: False threeway_partition_def ls_def x_def nl_def)+
    next
      assume *: "\<not>k < nl" "\<not>k < nl + ne"
      have **: "length xs = length ls + length es + length gs"
        unfolding ls_def es_def gs_def by (induction xs) auto
      show "fast_select l (k - nl - ne) gs = select (k - nl - ne) gs"
        unfolding nl_def ne_def
        by (rule 1; (rule refl tw)?) (insert False * ** \<open>k < length xs\<close>, auto simp: nl_def ne_def)
    qed
    also have "\<dots> = select k xs" using \<open>k < length xs\<close>
      by (subst (3) select_rec_threeway_partition[of "5::nat" _ _ x])
         (unfold Let_def nl_def ne_def ls_def gs_def es_def x_def threeway_partition_def, simp_all)
    finally show ?thesis .
  qed
qed

text \<open>
  Termination of the algorithm is reasonably obvious because the lists that are recursed into
  never contain the pivot (the median-of-medians), while the original list clearly does.
  The proof is still somewhat technical though.
\<close>
lemma fast_select_termination: "All fast_select_dom"
proof (relation "measure (length \<circ> snd \<circ> snd)"; (safe)?, goal_cases)
  case (1 l k xs)
  thus ?case
    by (auto simp: length_chop nat_less_iff ceiling_less_iff)
next
  fix l k :: nat and xs ls es gs :: "'a list"
  define x where "x = fast_select l (((length xs + 4) div 5 - 1) div 2) (map median (chop 5 xs))"
  assume A: "\<not> length xs \<le> max l 2" 
            "(ls, es, gs) = threeway_partition x xs"
            "fast_select_dom (l, ((length xs + 4) div 5 - 1) div 2, 
                             map median (chop 5 xs))"
  from A have eq: "ls = filter (\<lambda>y. y < x) xs" "gs = filter (\<lambda>y. y > x) xs"
    by (simp_all add: x_def threeway_partition_def)
  have len: "(length xs + 4) div 5 = nat \<lceil>length xs / 5\<rceil>" by linarith
  have less: "(nat \<lceil>real (length xs) / 5\<rceil> - Suc 0) div 2 < nat \<lceil>real (length xs) / 5\<rceil>"
    using A(1) by linarith
  have "x = select (((length xs + 4) div 5 - 1) div 2) (map median (chop 5 xs))"
    using less unfolding x_def by (intro fast_select_correct_aux A) (auto simp: length_chop len)
  also have "\<dots> = median (map median (chop 5 xs))" by (simp add: median_def len length_chop)
  finally have x: "x = \<dots>" .
  moreover {
    have "x \<in> set (map median (chop 5 xs))"
      using A(1) unfolding x by (intro median_in_set) auto
    also have "\<dots> \<subseteq> (\<Union>ys\<in>set (chop 5 xs). {median ys})" by auto
    also have "\<dots> \<subseteq> (\<Union>ys\<in>set (chop 5 xs). set ys)" using A(1)
      by (intro UN_mono) (auto simp: median_in_set length_chop_part_le)
    also have "\<dots> = set xs" by (subst UN_sets_chop) auto
    finally have "x \<in> set xs" .
  }  
  ultimately show "((l, k, ls), l, k, xs) \<in> measure (length \<circ> snd \<circ> snd)"
              and "((l, k - length ls - length es, gs), l, k, xs) \<in> measure (length \<circ> snd \<circ> snd)"
    using A(1) by (auto simp: eq intro!: length_filter_less[of x])
qed

termination by (rule fast_select_termination)
lemma max23_2: "max 23 (2::nat) = 23" by simp
lemma fast_select_code [code]:
  "fast_select 23 k xs = (
     if length xs \<le> 23 then
       fold insort xs [] ! k
     else
       let x = fast_select 23 (((length xs + 4) div 5 - 1) div 2) (map median (chop 5 xs));
           (ls, es, gs) = threeway_partition x xs;
           nl = length ls; ne = nl + length es
       in
         if k < nl then fast_select 23 k ls 
         else if k < ne then x
         else fast_select 23 (k - ne) gs
      )"
  by (subst fast_select.simps) (simp_all only: Let_def algebra_simps sort_conv_fold max23_2)

theorem fast_select_correct: "k < length xs \<Longrightarrow> fast_select l k xs = select k xs"
  using fast_select_termination by (intro fast_select_correct_aux) auto

lemma select_code [code]: 
  "select k xs = (if k < length xs then fast_select 23 k xs 
                    else Code.abort (STR ''Selection index out of bounds.'') (\<lambda>_. select k xs))"
proof (cases "k < length xs")
  case True
  thus ?thesis by (simp only: if_True fast_select_correct)
qed (simp_all only: Code.abort_def if_False)

end
