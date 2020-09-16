theory IHT_Reverse
imports "../SepLogicTime/SLTC_Main" "../Asymptotics/Asymptotics_Recurrences"
begin

fun rev'_fun :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "rev'_fun xs ys 0 = ys"
| "rev'_fun xs ys (Suc n) = (let ys' = rev'_fun xs ys n 
                              in 
                                ys'[n:=(xs!(length xs - Suc n))])"
setup \<open>fold add_rewrite_rule @{thms rev'_fun.simps}\<close>

lemma length_rev'_fun[rewrite]: "length xs = length ys \<Longrightarrow> n\<le>length xs \<Longrightarrow> length (rev'_fun xs ys n) = length ys"
  by(induct n, auto) 

setup \<open>add_rewrite_rule @{thm rev_nth}\<close> 

lemma rev'_fun_rev_aux: "length xs = length ys \<Longrightarrow> n \<le> length xs \<Longrightarrow> 
    i < n  \<Longrightarrow> rev'_fun xs ys n ! i = rev xs ! i"
@proof @induct n arbitrary i @qed

lemma rev'_fun_correct[rewrite]: "length xs = length ys \<Longrightarrow> rev'_fun xs ys (length ys) = rev xs"
  by(auto simp add: rev'_fun_rev_aux list_eq_iff_nth_eq length_rev'_fun) 

fun rev_impl' :: "('a::heap) array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap"  where 
  "rev_impl' p q 0 = return ()"
| "rev_impl' p q (Suc n) = do {
        rev_impl' p q n;
        len \<leftarrow> Array_Time.len p;
        e \<leftarrow> Array_Time.nth p (len - Suc n);
        Array_Time.upd n e q;
        return ()
      }"

fun rev'_time :: "nat \<Rightarrow> nat" where
  "rev'_time 0 = 1"
| "rev'_time (Suc n) = rev'_time n + 4"
setup \<open>fold add_rewrite_rule @{thms rev'_time.simps}\<close>

lemma rev'_time_closed: "rev'_time n = 1 + n*4" 
  by(induct n, auto)

lemma "rev'_time \<in> \<Theta>(\<lambda>n. n)"
  unfolding rev'_time_closed by auto2

lemma rev'_time_bound[asym_bound]: "rev'_time \<in> \<Theta>(\<lambda>n. n)"
  by(rule bigTheta_linear_recurrence_const[where g="\<lambda>_.4" and N=3], auto)

lemma rev'_rule[hoare_triple]:
    "length xs = length ys \<Longrightarrow> n \<le> length xs \<Longrightarrow> 
          <p \<mapsto>\<^sub>a xs * q \<mapsto>\<^sub>a ys * $(rev'_time n)>
            rev_impl' p q n
          <%_. p \<mapsto>\<^sub>a xs * q \<mapsto>\<^sub>a rev'_fun xs ys n>\<^sub>t"
@proof @fun_induct "rev'_fun xs ys n" @qed


definition rev_impl where
  "rev_impl p = do {
      len \<leftarrow> Array_Time.len p;
      q \<leftarrow> Array_Time.new len undefined;
      rev_impl' p q len; 
      return q
    }"

definition rev_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "rev_time n = n + rev'_time n + 3"

lemma rev_impl_time_mono: "x\<le>y \<Longrightarrow> rev_time x \<le> rev_time y"
  unfolding rev_time_def rev'_time_closed by auto   

lemma rev_impl_time_bound[asym_bound]: "rev_time \<in> \<Theta>(\<lambda>n. n)"
  unfolding rev_time_def by auto2

lemma rev_impl_rule[hoare_triple]:
    "length xs = length ys \<Longrightarrow>
          <p \<mapsto>\<^sub>a xs * $(rev_time (length xs))>
            rev_impl p
          <%r. p \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a rev xs>\<^sub>t"
  by auto2

setup \<open>del_prfstep_thm @{thm rev_time_def}\<close> 

end
