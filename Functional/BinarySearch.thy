theory BinarySearch
  imports Auto2_HOL.Auto2_Main
begin

fun avg :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "avg l r = (l + r) div 2"

function binarysearch_fun :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a list \<Rightarrow> bool" where
  "binarysearch_fun l r x xs =
   (if l \<ge> r then False
    else if l + 1 \<ge> r then xs ! l = x
    else let m = avg l r in
      if xs ! m = x then True
      else if xs ! m < x then binarysearch_fun (m + 1) r x xs
      else binarysearch_fun l m x xs)"
by pat_completeness auto
termination by (relation "Wellfounded.measure (\<lambda>(l,r,a,f). r-l)") auto

setup \<open>register_wellform_data ("binarysearch_fun l r x xs", ["l \<le> r", "r \<le> length xs"])\<close>
setup \<open>add_prfstep_check_req ("binarysearch_fun l r x xs", "l \<le> r \<and> r \<le> length xs")\<close>

lemma avg_between [backward]:
  "l + 1 < r \<Longrightarrow> r > avg l r"
  "l + 1 < r \<Longrightarrow> avg l r > l" by auto

lemma binarysearch_fun_correct [rewrite]:
  "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   binarysearch_fun l r x xs \<longleftrightarrow> (\<exists>i. l \<le> i \<and> i < r \<and> xs ! i = x)"
@proof @fun_induct "binarysearch_fun l r x xs"
  @unfold "binarysearch_fun l r x xs"
  @case "l \<ge> r" @case "l + 1 \<ge> r"
  @have "avg l r + 1 \<le> r"
@qed

end
