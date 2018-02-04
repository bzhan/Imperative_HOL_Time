theory Asymptotics_Recurrences
imports Asymptotics_2D
begin
 
section {* Linear recurrences in the one variable case *}

lemma fixes a b c :: real
  shows K: "a \<ge> 0 \<Longrightarrow> b \<ge> 1 \<Longrightarrow> c \<ge> 1 \<Longrightarrow> a \<le> a * b * c"  
  by (metis mult.right_neutral mult_left_mono order_trans)

lemma bigO_linear_recurrence:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i" and g: "g \<in> O(\<lambda>n. n)"
  shows "f \<in> O(\<lambda>n. n * n)"
proof -
  from g have "\<exists>c>0. \<forall>\<^sub>F x in at_top. norm (g x) \<le> c * norm (x)"
    unfolding bigo_def by auto
  then obtain cg Ng where nncg: "cg > 0" and b: "\<forall>n\<ge>Ng. norm (g n) \<le> cg * norm (n)"
    using eventually_sequentially by auto
  let ?cg = "max cg 1"
  from nncg b have nncg2: "?cg \<ge> 1" and b2: "\<forall>n\<ge>Ng. norm (g n) \<le> ?cg * norm (n)"
    apply auto
    by (meson max.cobounded1 mult_le_cancel_right of_nat_less_0_iff order_trans)

  let ?N = "max Ng (N+1)"
  let ?nfN = "max (norm (f ?N)) 1"

  show ?thesis apply(rule bigoI[where c="?nfN * ?cg"])
    apply(rule eventually_sequentiallyI[where c="?N"])
    subgoal for x
      proof (induction rule: Nat.dec_induct)
        case base
        have nn2: "norm (real ((?N) * (?N))) \<ge> 1"
          by (metis le_add2 le_square le_trans max.bounded_iff norm_of_nat real_of_nat_ge_one_iff)
        have "norm (f (max Ng (N + 1))) \<le> ?nfN" by auto
        also have "\<dots> \<le> ?nfN * ?cg * norm (real ?N * real ?N)" apply(rule K) using nn2 nncg2 by auto 
        finally show ?case . 
      next
        case (step n)
        from step(1) assms(1) have i: "f (Suc n) = f n + g n" by auto
        have z: "?nfN \<ge> 1" by auto
        from step(1) b2 have ii: "norm (g n) \<le> ?cg * norm (n)" by auto
        also have "\<dots> \<le> ?nfN * ?cg * norm (n)" using z
          by (metis (no_types, hide_lams) less_eq_real_def max_def mult.commute mult.left_neutral mult_left_mono nncg norm_of_nat of_nat_0_le_iff)  
        finally have ii: "norm (g n) \<le> ?nfN * ?cg * norm (real n) " . 
        have "norm (f (Suc n)) = norm (f n + g n)" using i by auto
        also have "\<dots> \<le> norm (f n) + norm (g n)" by simp
        also have "\<dots> \<le> (?nfN * ?cg * norm (real (n * n))) + norm (g n)" using step(3) by simp
        also have "\<dots> \<le> (?nfN * ?cg * norm (real (n * n))) + ?nfN * ?cg * norm (real n) " using ii by simp
        also have "\<dots> = ?nfN * ?cg * (norm (real (n * n)) + norm (real n))" by algebra
        also have "\<dots> \<le> ?nfN * ?cg * norm (real (Suc n * Suc n))" by fastforce
        also have "\<dots> = ?nfN * ?cg * norm (real (Suc n) * real (Suc n))"
          by (metis of_nat_mult)  
        finally show ?case .
      qed
      done
qed

lemma bigOmega_linear_recurrence:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i"
      and g: "g \<in> \<Omega>(\<lambda>n. n)" and "\<And>n. f n \<ge> 0" "\<And>n. g n \<ge> 0"
  shows "f \<in> \<Omega>(\<lambda>n. n * n)"
proof -
  from g have "\<exists>c>0. \<forall>\<^sub>F x in at_top. norm (g x) \<ge> c * norm (x)"
    unfolding bigomega_def by auto
  then obtain cg Ng where nncg: "cg > 0" and b: "\<forall>n\<ge>Ng. norm (g n) \<ge> cg * norm (n)"
    using eventually_sequentially by auto
  let ?cg = "max (1/cg) 1"
  have nncg2: "?cg \<ge> 1" by auto
  have b2: "\<And>n. n\<ge>Ng \<Longrightarrow>  n  \<le> ?cg * norm (g n)"
  proof -
    fix n assume "n\<ge>Ng"
    then have "n \<le> norm (g n) / cg" using b nncg
      by (simp add: linordered_field_class.sign_simps(24) pos_le_divide_eq)  
    also have "\<dots> = (1/cg) * norm (g n)" by auto
    also have "\<dots> \<le> ?cg * norm (g n)" apply(rule mult_right_mono) by auto 
    finally show "n \<le> max (1 / cg) 1 * norm (g n)" .
  qed

  let ?N' = "max Ng (N+1)"
  let ?N = "2*?N'"
  have n: "norm (f ?N) > 0"
  proof -
    have "?N>0" by auto then
    obtain N' where f: "?N=Suc N'" using gr0_implies_Suc by blast
    then have p: "N' \<ge> N"
      by (metis Suc_eq_plus1 Suc_le_mono max.cobounded2 nat_le_prod_with_le zero_neq_numeral) 
    from f have gN: "N'>0"
      using gr0I by force  
    have n: "N'\<ge>Ng" using f
      by (metis add_le_cancel_left antisym_conv le_add_same_cancel1 le_simps(3) linorder_not_le max.bounded_iff nat_mult_2 zero_order(1)) 
    have "0 < cg * norm (real N')" using gN nncg by auto
    also have "\<dots> \<le>  norm (g N')" using b n  by auto
    also have "\<dots> \<le> norm (f N' + g N')" using assms(3,4) by auto
    also have "\<dots> = norm (f ?N)" unfolding f using p assms(1) by auto 
    finally show ?thesis .
  qed
  let ?nfN = "norm (real ?N * real ?N)/(norm (f ?N))"
  define nfN' where "nfN' = max ?nfN 4"

  show ?thesis apply(rule bigomegaI[where c="?cg * nfN'"])
    apply(rule eventually_sequentiallyI[where c="?N"])
    subgoal for x
      proof(induction rule: Nat.dec_induct)
        case base
        have "norm (real ?N * real ?N) = 1 * (?nfN * (norm (f ?N)))" using n by auto      
        also have "\<dots> \<le> ?cg * (?nfN * (norm (f ?N)))" apply(rule mult_right_mono) using nncg2 by auto 
        also have "\<dots> = (?cg * ?nfN) * (norm (f ?N))" by auto
        also have "\<dots> \<le> (?cg * nfN') * (norm (f ?N))" unfolding nfN'_def apply(rule mult_right_mono) apply(rule mult_left_mono) by auto
        finally show ?case by auto
      next
        case (step n)
        then have nN: "n\<ge>N"
          by (metis Suc_eq_plus1 Suc_leD le_trans max.cobounded2 nat_le_prod_with_le zero_neq_numeral) 
        from step(1) have nNg: "n\<ge>Ng"
          by (metis le_trans max.cobounded1 nat_le_prod_with_le zero_neq_numeral) 
        from nN assms(1) have i: "f (Suc n) = f n + g n" by auto
        from nNg b2 have b3: "n \<le> ?cg * norm (g n)" by auto 
        from step(1) have "n\<ge>1"
          by (metis One_nat_def Suc_eq_plus1 gr0I le_0_eq le_simps(3) max.cobounded2 mult_is_0 nat.simps(3) numeral_eq_Suc) 
        then have ii: "n+1\<le>2*n" by auto
        have 4: "4\<le>nfN'" unfolding nfN'_def by auto
        have "norm (real (Suc n) * real (Suc n)) = (n+1)*(n+1)" by (metis Suc_eq_plus1 norm_of_nat of_nat_mult) 
        also have "\<dots> \<le> n*n + 2*(n + 1)"  by auto
        also have "\<dots> \<le> ?cg * nfN' * norm (f n) + 4*n" using ii step(3) by auto
        also have "\<dots> \<le> ?cg * nfN' * norm (f n) + 4*(?cg * norm (g n))" using b3 by auto
        also have "\<dots> \<le> ?cg * nfN' * norm (f n) + nfN'*(?cg * norm (g n))" using 4 apply auto apply(rule mult_right_mono) by auto
        also have "\<dots> = (?cg * nfN') * norm (f n) + (?cg * nfN') * norm (g n)" by auto
        also have "\<dots> = (?cg * nfN') * (norm (f n) + norm (g n))" by argo
        also have "\<dots> = (?cg* nfN') * (norm (f n + g n))" using assms(3,4) by auto
        also have "\<dots> = (?cg* nfN') * norm (f (Suc n))" using i by auto
        finally    
        show "norm (real (Suc n) * real (Suc n)) \<le> (?cg * nfN') * norm (f (Suc n))" . 
      qed
      done
qed

lemma bigTheta_linear_recurrence:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i"
      and g: "g \<in> \<Theta>(\<lambda>n. n)" and "\<And>n. f n \<ge> 0" "\<And>n. g n \<ge> 0"
  shows "f \<in> \<Theta>(\<lambda>n. n * n)"
proof
  show "f \<in> O(\<lambda>n. n * n)" 
    apply (rule bigO_linear_recurrence)
    using assms by auto
  show "f \<in> \<Omega>(\<lambda>n. n * n)"
    apply (rule bigOmega_linear_recurrence)
    using assms by auto
qed

section {* Example *}

fun bla_time :: "nat \<Rightarrow> real" where
   "bla_time 0 = 1"
|  "bla_time (Suc n) = bla_time n + n"

lemma bla_time_nneg:
  "bla_time n \<ge> 0" by (induct n) auto

lemma "bla_time \<in> \<Theta>(\<lambda>n. real n * real n)"
  apply (rule bigTheta_linear_recurrence[where N=0 and g="(\<lambda>n. n)"])
  by (auto simp: bla_time_nneg)

section {* Linear recurrence in the two variable case *}

lemma bivariate:
  assumes "\<And>n m. n\<ge>N \<Longrightarrow>  f (Suc n,m) = f (n,m) + g m"  
    and "\<And>n m. n \<le> N \<Longrightarrow> f (n,m) \<le> C"
    and g: "g \<in> O(\<lambda>m. m)"
    and fpos: "eventually_nonneg (at_top\<times>\<^sub>Fat_top) f"
    and Cpos: "C \<ge> 0"
  shows "f \<in> O\<^sub>2(\<lambda>(n,m). real (n * m))"
proof -
  { fix n m
    have "f (N+n, m) \<le> C + n * g m"
    proof (induct n)
      case 0
      then show ?case using assms(2) by simp
    next
      case (Suc n)
      have "f (N + Suc n, m) = f (N + n, m) + g m" using assms(1) by simp
      also have "\<dots> \<le> C + real n * g m + g m" using Suc by auto
      also have "\<dots> = C + (real (n+1)) * g m"
        by (metis Suc_eq_plus1 add.assoc add.commute of_nat_Suc semiring_normalization_rules(3)) 
      finally show ?case by simp
    qed 
  } then have k: "\<And>n m. n\<ge>N \<Longrightarrow> f (n,m)\<le> C + (n-N) * g m"
    by (metis le_add_diff_inverse) 

  from g have "\<exists>c>0. \<forall>\<^sub>F x in at_top. norm (g x) \<le> c * norm (x)"
    unfolding bigo_def by auto
  then obtain cg Ng where nncg: "cg > 0" and b: "\<forall>m\<ge>Ng. norm (g m) \<le> cg * norm (m)"
    using eventually_sequentially by auto
  let ?cg = "max cg 1"
  from nncg b have nncg2: "?cg \<ge> 1" and b2: "\<forall>m\<ge>Ng. norm (g m) \<le> ?cg * norm (m)"
    apply auto
    by (meson max.cobounded1 mult_le_cancel_right of_nat_less_0_iff order_trans)

  from fpos obtain npos where fpos': "\<And>n m. n\<ge>npos \<Longrightarrow> m\<ge>npos \<Longrightarrow> f (n,m) \<ge> 0"
    unfolding eventually_nonneg_def eventually_prod_sequentially by blast

  let ?N = "max (max Ng npos) (N+1)"
  let ?nfN = "max (norm (f (?N,?N))) 1"

  show ?thesis apply(rule bigoI[where c="(C / (?N*?N) + ?cg)"])
    apply(simp only: eventually_prod_sequentially) 
    apply(rule exI[where x="?N"])
    proof safe
      fix m n 
      have "norm (n-N) = n-N" by auto
      assume pf: "?N \<le> m"  "?N \<le> n"
      with fpos' have fpos'': "f (n,m) \<ge> 0" by auto
      have NN: "?N*?N > 0" by auto
      from pf have "?N > 0" by auto
      with pf have nm: "n*m\<ge>?N*?N" using mult_le_mono by blast
      then   have urghs: "C / (n*m) \<le> C / (?N*?N)" using NN
        by (meson Cpos frac_le linordered_semidom_class.of_nat_le_iff of_nat_0_less_iff order_refl)  
      from pf have Nn: "N \<le> n " and mNg: "m \<ge> Ng" and nm0: "n*m>0"  by auto
      then have "norm (f (n, m)) \<le> norm (C + (n-N) * g m)" using k[of "n"] fpos''
        by (smt real_norm_def) 
      also have "\<dots> \<le> norm C + norm (n-N) * norm(g m)"
        using  Cpos unfolding real_norm_def by (metis abs_mult abs_triangle_ineq)
      also have "\<dots> = C + (n-N) * norm (g m)" using Cpos  by auto
      also have "\<dots> \<le> C + n * norm (g m)"
        by (simp add: mult_right_mono)  
      also have "\<dots> \<le>   C + n * ( ?cg * norm (m))" using mNg b2 
        by (simp add: mult_left_mono)
      also have "\<dots> \<le> C + ?cg * n * m" by auto
      also 
        have "\<dots> = (C / (n*m) + ?cg) * n * m" using nm0
        proof -
          have "0 < m * n"
          using nm0 by force
            then have "real m * (real n * (C / (real m * real n))) + real m * (real n * max 1 cg) = C + real m * (real n * max 1 cg)"
              by simp
            then show ?thesis
              by (metis (no_types) distrib_right max.commute mult.commute of_nat_mult)
          qed   
      also have "\<dots> \<le> (C / (?N*?N) + ?cg) * n * m" using urghs
        by (simp add: mult_right_mono) 
      also have "\<dots> \<le> (C / real (?N*?N) + ?cg) * norm (real (n * m))" by auto
      finally show i: "norm (f (n, m)) \<le> (C / real (?N*?N) + ?cg) * norm (real (n * m))" .
    qed 
  qed

lemma bivariateOmega:
  assumes "\<And>n m. n\<ge>N \<Longrightarrow>  f (Suc n,m) = f (n,m) + g m"  
    and "\<And>n m. n \<le> N \<Longrightarrow> f (n,m) \<le> C"
    and g: "g \<in> \<Omega>(\<lambda>m. m)"
    and fpos: "eventually_nonneg (at_top\<times>\<^sub>Fat_top) f"
    and gpos: "\<And>n m. g n \<ge> 0"
    and Cpos: "C \<ge> 0"
  shows "f \<in> \<Omega>\<^sub>2(\<lambda>(n,m). real (n * m))"
proof -
  from fpos obtain npos where fpos': "\<And>n m. n\<ge>npos \<Longrightarrow> m\<ge>npos \<Longrightarrow> f (n,m) \<ge> 0"
    unfolding eventually_nonneg_def eventually_prod_sequentially by blast

  let ?N = "max N npos"
  { fix n m
    assume m: "m\<ge>?N"
    then have "f (?N+n, m) \<ge> n * g m"
    proof (induct n)
      case 0
      then show ?case using m fpos' by simp
    next
      case (Suc n)
      have "(real (n+1)) * g m = real n * g m + g m"
        by (metis Suc_eq_plus1 add.commute of_nat_Suc semiring_normalization_rules(3)) 
      also have "\<dots> \<le>  f (?N + n, m) + g m" using  Suc by auto
      also have "\<dots> = f (?N + Suc n, m)"  using assms(1) by simp 
      finally show ?case by simp
    qed 
  } then have k: "\<And>n m. n\<ge>?N \<Longrightarrow> m\<ge>?N \<Longrightarrow> f (n,m) \<ge> (n-?N) * g m"
    by (metis le_add_diff_inverse) 

  have ka: "\<And>n. n\<ge>2*?N \<Longrightarrow> n \<le> 2 * (n-?N)" by auto

  from g obtain cg Ng where nncg: "cg > 0" and b: "\<forall>m\<ge>Ng. norm (g m) \<ge> cg * norm (m)"
    using bigOmegaE by blast
  from nncg have pff: "\<And>m. m \<ge> Ng \<Longrightarrow> m \<le> (1/cg) * g m " using gpos b apply auto
    by (simp add: linordered_field_class.sign_simps(24) pos_le_divide_eq)

  let ?N' = "max (max Ng npos) (2*?N)" 
 
  let ?C = "2*(1/cg)"
  show ?thesis apply(rule bigomegaI[where c="?C"])
    apply(simp only: eventually_prod_sequentially) 
    apply(rule exI[where x="?N'"])
    proof safe
      fix m n 
      have "norm (n-?N) = n-?N" by auto
      assume pf: "?N' \<le> m"  "?N' \<le> n" 
      then have t: "n \<ge> 2*?N" and l: "Ng \<le> m" by auto
      from pf fpos' have fpos'': "0 \<le> f (n, m)" by auto
      from pf have tl: "n\<ge>?N" "m\<ge>?N" by auto

      have " norm (real (n * m)) = real n * real m" by simp
      also have "\<dots> \<le> n * ( (1/cg) * g m)" apply(rule mult_left_mono) apply(rule pff) apply (fact l) by simp
      also have "\<dots> \<le> (1/cg) * (n * g m)" by auto
      also have "\<dots> \<le> (1/cg) * (2*(n-?N) * g m)" apply(rule mult_left_mono)
            apply(rule mult_right_mono) using nncg gpos ka[OF t] by auto
      also have "\<dots> = ?C * ((n-?N) * g m)" by auto
      also have "\<dots> \<le> ?C * (f (n, m))" apply(rule mult_left_mono) using k[of n m] nncg pf tl by auto
      also have "\<dots> \<le> ?C * norm (f (n,m))" apply(rule mult_left_mono) using nncg fpos by auto
      finally show "norm (real (n * m)) \<le> ?C * norm (f (n, m))" .
  qed 
qed

lemma bivariateTheta:
  assumes "\<And>n m. n\<ge>N \<Longrightarrow>  f (Suc n,m) = f (n,m) + g m"  
    and "\<And>n m. n \<le> N \<Longrightarrow> f (n,m) \<le> C"
    and g: "g \<in> \<Theta>(\<lambda>m. m)"
    and fpos: "eventually_nonneg (at_top\<times>\<^sub>Fat_top) f"
    and gpos: "\<And>n m. g n \<ge> 0"
    and Cpos: "C \<ge> 0"
  shows "f \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (n * m))"
proof -
  from g have "g \<in> \<Omega>(\<lambda>m. m)" "g \<in> O(\<lambda>m. m)" by auto
  have "f \<in> O\<^sub>2(\<lambda>(n,m). real (n * m))"
    apply(rule bivariate[where N=N and C=C]) using assms by auto
  moreover
  have "f \<in> \<Omega>\<^sub>2(\<lambda>(n,m). real (n * m))"
    apply(rule bivariateOmega[where N=N and C=C and g=g]) using assms by auto
  ultimately show ?thesis by auto
qed

section {* Examples in the bivariate case *}

fun ex :: "nat \<times> nat \<Rightarrow> real" where
  "ex (0,m) = 1"
| "ex (Suc n, m) = ex (n,m) + m"

lemma ex_pos[simp]: "0 \<le> ex (n, m)" by (induct n) auto

lemma "ex \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (n * m))"
  apply (rule bivariateTheta[where N=0 and C=1])
  by (auto simp: eventually_prod_sequentially eventually_nonneg_def)
 
end
