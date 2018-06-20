theory Rev_Impl
imports SepAuto Asymptotics_Recurrences
begin

fun rev_fun :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "rev_fun xs ys 0 = ys"
| "rev_fun xs ys (Suc n) = (let ys' = rev_fun xs ys n 
                              in 
                                ys'[n:=(xs!(length xs - Suc n))])"
setup {* fold add_rewrite_rule @{thms rev_fun.simps} *}

lemma length_rev_fun[rewrite]: "length xs = length ys \<Longrightarrow> n\<le>length xs \<Longrightarrow> length (rev_fun xs ys n) = length ys"
  apply(induct n) by auto

lemma rev_fun_rev_aux: "length xs = length ys \<Longrightarrow> n \<le> length xs \<Longrightarrow> \<forall>i<n. rev_fun xs ys n ! i = rev xs ! i"
  apply(induct n)
  apply (auto) subgoal for n i by(cases "i=n", simp_all add: length_rev_fun rev_nth) done

lemma rev_fun_correct[rewrite]: "length xs = length ys \<Longrightarrow> rev_fun xs ys (length xs) = rev xs"
  apply(simp add: list_eq_iff_nth_eq length_rev_fun)
  using rev_fun_rev_aux[where n="length xs"] by force

fun rev_impl' :: "('a::heap) array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap"  where 
  "rev_impl' p q 0 = return ()"
| "rev_impl' p q (Suc n) = do {
        rev_impl' p q n;
        len \<leftarrow> Array.len p;
        e \<leftarrow> Array.nth p (len - Suc n);
        Array.upd n e q;
        return ()
      }"

fun rev_impl'_time :: "nat \<Rightarrow> nat" where
  "rev_impl'_time 0 = 1"
| "rev_impl'_time (Suc n) = rev_impl'_time n + 4"
setup {* fold add_rewrite_rule @{thms rev_impl'_time.simps} *}

lemma rev_impl'_time_closed: "rev_impl'_time n = (if n=0 then 1 else 1 + n*4)" 
  by(induct n, auto)

lemma rev_impl'_time_bound[asym_bound]: "rev_impl'_time \<in> \<Theta>(\<lambda>n. n)"
  by(rule bigTheta_linear_recurrence_const[where g="\<lambda>_.4" and N=3], auto)

lemma rev_impl'_rule'[hoare_triple]:
    "length xs = length ys \<Longrightarrow> n \<le> length xs \<Longrightarrow> 
          <p \<mapsto>\<^sub>a xs * q \<mapsto>\<^sub>a ys * $(rev_impl'_time n)>
            rev_impl' p q n
          <%_. p \<mapsto>\<^sub>a xs * q \<mapsto>\<^sub>a rev_fun xs ys n>\<^sub>t"
@proof @fun_induct "rev_fun xs ys n" @qed
 
definition rev_impl where
  "rev_impl p = do {
      len \<leftarrow> Array.len p;
      q \<leftarrow> Array.new len undefined;
      rev_impl' p q len; 
      return q
    }"

definition rev_impl_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "rev_impl_time n = n + rev_impl'_time n + 3"

lemma rev_impl_time_mono: "x\<le>y \<Longrightarrow> rev_impl_time x \<le> rev_impl_time y"
  unfolding rev_impl_time_def rev_impl'_time_closed by auto   

lemma rev_impl_time_bound[asym_bound]: "rev_impl_time \<in> \<Theta>(\<lambda>n. n)"
  unfolding rev_impl_time_def by auto2

lemma rev_impl_rule[hoare_triple]:
    "length xs = length ys \<Longrightarrow>
          <p \<mapsto>\<^sub>a xs * $(rev_impl_time (length xs))>
            rev_impl p
          <%r. p \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a rev xs>\<^sub>t"
  by auto2

setup {* del_prfstep_thm @{thm rev_impl_time_def} *} 

end