(* Author: Max P.L. Haslbeck, Bohua Zhan
*)

theory MergeSort
  imports "Auto2_HOL.Auto2_Main"
begin

section \<open>Simple functional version\<close>

fun merge_list :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_list xs ys = (
     if xs = [] then ys else if ys = [] then xs
     else if last xs \<ge> last ys then merge_list (butlast xs) ys @ [last xs]
     else merge_list xs (butlast ys) @ [last ys])"
setup \<open>add_rewrite_rule @{thm merge_list.simps}\<close>

lemma merge_list_simps' [rewrite]:
  "merge_list [] ys = ys"
  "merge_list xs [] = xs"
  "merge_list (xs @ [x]) (ys @ [y]) =
    (if x \<ge> y then merge_list xs (ys @ [y]) @ [x]
               else merge_list (xs @ [x]) ys @ [y])" by auto2+
setup \<open>del_prfstep_thm @{thm merge_list.simps}\<close>

lemma merge_list_length [rewrite]:
  "length (merge_list xs ys) = length xs + length ys"
@proof @fun_induct "merge_list xs ys"
  @case "xs = []" @case "ys = []"
  @have "xs = butlast xs @ [last xs]"
  @have "ys = butlast ys @ [last ys]"
@qed

lemma merge_list_correct_mset [rewrite]:
  "mset (merge_list xs ys) = mset xs + mset ys"
@proof @fun_induct "merge_list xs ys"
  @case "xs = []" @case "ys = []"
  @have "xs = butlast xs @ [last xs]"
  @have "ys = butlast ys @ [last ys]"
@qed

lemma merge_list_correct_set [rewrite]:
  "set (merge_list xs ys) = set xs \<union> set ys"
@proof
  @have "set (merge_list xs ys) = set_mset (mset (merge_list xs ys))"
@qed

lemma merge_list_sorted [forward]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_list xs ys)"
@proof @fun_induct "merge_list xs ys"
  @case "xs = []" @case "ys = []"
  @have "xs = butlast xs @ [last xs]"
  @have "ys = butlast ys @ [last ys]"
@qed

fun merge_sort_fun :: "'a::linorder list \<Rightarrow> 'a list" where
  "merge_sort_fun xs =
     (let n = length xs in
      (if n \<le> 1 then xs
       else
        let as = take (n div 2) xs;
            bs = drop (n div 2) xs;
            as' = merge_sort_fun as;
            bs' = merge_sort_fun bs;
            r = merge_list as' bs'
        in r))"

lemma sort_length_le1 [rewrite]: "length xs \<le> 1 \<Longrightarrow> sort xs = xs"
@proof
  @case "xs = []" @have "xs = hd xs # tl xs" @case "tl xs = []"
@qed

lemma mergesort_fun_correct [rewrite]:
  "merge_sort_fun xs = sort xs"
@proof @fun_induct "merge_sort_fun xs"
  @unfold "merge_sort_fun xs"
  @case "length xs \<le> 1"
  @let "l1 = length xs div 2"
  @have "mset (take l1 xs) + mset (drop l1 xs) = mset xs" @with
    @have "take l1 xs @ drop l1 xs = xs"
  @end
@qed

lemma mergesort_fun_length [rewrite]:
  "length (merge_sort_fun xs) = length xs" by auto2

section \<open>Actual functional version\<close>

function mergeinto_fun :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "mergeinto_fun 0 0 a b c = c"
| "mergeinto_fun (Suc la) 0 a b c = list_update (mergeinto_fun la 0 a b c) la (a ! la)"
| "mergeinto_fun 0 (Suc lb) a b c = list_update (mergeinto_fun 0 lb a b c) lb (b ! lb)"
| "mergeinto_fun (Suc la) (Suc lb) a b c =
    (if a ! la \<ge> b ! lb then
       list_update (mergeinto_fun la (Suc lb) a b c) (Suc (la+lb)) (a ! la)
     else
       list_update (mergeinto_fun (Suc la) lb a b c) (Suc (la+lb)) (b ! lb))"
by pat_completeness auto
termination by (relation "Wellfounded.measure (\<lambda>(la, lb, a, b, c). la + lb)") auto

setup \<open>fold add_rewrite_rule @{thms mergeinto_fun.simps}\<close>

lemma mergeinto_fun_length [rewrite]:
  "length (mergeinto_fun la lb a b c) = length c"
@proof @fun_induct "mergeinto_fun la lb a b c" @qed

lemma mergeinto_fun_to_merge_list_induct [backward]:
  "length c = length a + length b \<Longrightarrow>
  la \<le> length a \<Longrightarrow> lb \<le> length b \<Longrightarrow>
  take (la + lb) (mergeinto_fun la lb a b c) = merge_list (take la a) (take lb b)"
@proof @fun_induct "mergeinto_fun la lb a b c" @with
  @subgoal "(la = Suc la, lb = Suc lb, a = a, b = b, c = c)"
    @have "Suc (la + Suc lb) \<le> length c" @with
      @have "Suc (la + lb) < length c"
    @end
    @case "a ! la \<ge> b ! lb"
  @endgoal @end
@qed

lemma mergeinto_fun_to_merge_list [rewrite]:
  "length c = length a + length b \<Longrightarrow>
   mergeinto_fun (length a) (length b) a b c = merge_list a b"
@proof
  @let "res = mergeinto_fun (length a) (length b) a b c"
  @have "take (length a + length b) res = merge_list (take (length a) a) (take (length b) b)"
@qed

end
