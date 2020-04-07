theory Asymptotics_Recurrences
imports Asymptotics_2D
begin
 
section \<open>Linear recurrences in the one variable case\<close>

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

lemma bigO_linear_recurrence':
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i" and g: "g \<in> O(G)"
    and monoG: "\<And>x y. x\<ge>N \<Longrightarrow> x\<le> y \<Longrightarrow> G x \<le> G y"
    and posG: "\<And>x. x\<ge>N \<Longrightarrow> G x > 0" 
  shows "f \<in> O(\<lambda>n. n * G n)"
proof -
  from g have "\<exists>c>0. \<forall>\<^sub>F x in at_top. norm (g x) \<le> c * norm (G x)"
    unfolding bigo_def by auto
  then obtain cg Ng where nncg: "cg > 0" and b: "\<forall>n\<ge>Ng. norm (g n) \<le> cg * norm (G n)"
    using eventually_sequentially by auto
  let ?cg = "max cg 1"
  from nncg b have nncg2: "?cg \<ge> 1" and b2: "\<forall>n\<ge>Ng. norm (g n) \<le> ?cg * norm (G n)"
    apply auto
    by (metis (no_types) abs_not_less_zero b comm_monoid_mult_class.mult_1 landau_omega.R_trans max_def mult_le_cancel_right2 real_norm_def)

  define K where  "K = max (nat (ceiling (1 / G N))) N"
  have KK: "\<And>x. x\<ge>K \<Longrightarrow> norm (((x) * (G x))) \<ge> 1"
  proof -
    fix x assume "K \<le> x"
    then have x: "x \<ge> N" and xi: "x \<ge> 1 / G N" apply (auto simp: K_def) done
    have i: "norm (((x) * (G x))) = x * G x" using x posG apply auto
      by (meson abs_of_nonneg less_eq_real_def mult_nonneg_nonneg not_le of_nat_0_le_iff of_nat_less_iff) 
    have p: "G (real N) > 0" using posG by auto
    have o: "G N \<le> G x" using x monoG by auto
    have "1 = (1/G N) * G N" using p by auto
    also have "\<dots> \<le> x * G N" using xi p apply auto
      by (metis calculation mult.commute real_mult_le_cancel_iff2) 
    also have "\<dots> \<le> x * G x" using o  by (simp add:  mult_left_mono) 
    finally show "norm (((x) * (G x))) \<ge> 1"
      unfolding i .
  qed

  let ?N = "max Ng (max (N+1) K)"
  define nfN  where "nfN = (max (norm (f ?N)) 1)"

  show ?thesis apply(rule bigoI[where c="nfN * ?cg"])
    apply(rule eventually_sequentiallyI[where c="?N"])
    subgoal for x
      proof (induction rule: Nat.dec_induct)
        case base
        have nn2: "norm (((?N) * (G ?N))) \<ge> 1"
          apply(rule KK) by auto
        have "norm (f ?N) \<le> nfN" by (auto simp: nfN_def)
        also have "\<dots> \<le> nfN * ?cg * norm (real ?N * G ?N)" apply(rule K) 
            subgoal by (auto simp: nfN_def) apply(rule nncg2)  apply(rule nn2) done 
        finally show ?case . 
      next
        case (step n)
        from step(1) have nN: "n\<ge>N" by auto
        with assms(1) posG have i: "f (Suc n) = f n + g n" and ii: "G (real n) > 0" by auto
        have z: "nfN \<ge> 1" by (auto simp: nfN_def)
        from ii have zz: "norm (G (real n)) > 0"  by auto
        from step(1) b2 have ii: "norm (g n) \<le> ?cg * norm (G n)" by auto
        also have "\<dots> \<le> nfN * ?cg * norm (G n)" using z nncg zz
          by (simp add: mult_le_cancel_right1) 
        finally have ii: "norm (g n) \<le> nfN * ?cg * norm (G n) " .
        have kl: "G n \<le> G (Suc n)" using monoG nN by auto
        have t: "norm (real n * G n) + norm (G n) = (n * G n) + (G n)" using   ii
          by (metis abs_of_nonneg less_eq_real_def of_nat_le_iff nN norm_mult norm_of_nat posG real_norm_def) 
        also have "\<dots> \<le> (Suc n * G (Suc n))" using kl
          by (metis add.commute distrib_right mult.left_neutral mult_left_mono of_nat_0_le_iff of_nat_Suc)  
        also have "\<dots> = norm (Suc n * G (Suc n))" using kl ii
          using less_eq_real_def nN posG by fastforce 
        finally have pf: "norm (real n * G n) + norm (G n) \<le>norm (Suc n * G (Suc n))" .

        have "norm (f (Suc n)) = norm (f n + g n)" using i by auto
        also have "\<dots> \<le> norm (f n) + norm (g n)" by simp
        also have "\<dots> \<le> (nfN * ?cg * norm (real n * G n)) + norm (g n)" using step(3) by simp
        also have "\<dots> \<le> (nfN * ?cg * norm (real n * G n)) + nfN * ?cg * norm (G n) " using ii by simp
        also have "\<dots> = nfN * ?cg * (norm (real n * G n) + norm (G n))" by algebra
        also have "\<dots> \<le>  nfN * ?cg * norm (real (Suc n) * G (Suc n))" using pf z by auto 
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
      by (simp add: mult.commute pos_le_divide_eq)  
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


lemma bigOmega_linear_recurrence':
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i"
      and g: "g \<in> \<Omega>(G)" and "\<And>n. f n \<ge> 0" "\<And>n. g n \<ge> 0"
    and posG: "\<And>x. x\<ge>N \<Longrightarrow> G x > 0" 
    and C: "\<And>n. n\<ge>N \<Longrightarrow> (n+1) * G (n+1) \<le> n * G n + C * G n"
      (* conjecture: proposition C always holds for G being polylog, or even stablebigO *)
    and Cpos: "C\<ge>0"
    shows "f \<in> \<Omega>(\<lambda>n. n * G n)"
proof -
  from g have "\<exists>c>0. \<forall>\<^sub>F x in at_top. norm (g x) \<ge> c * norm (G x)"
    unfolding bigomega_def by auto
  then obtain cg Ng where nncg: "cg > 0" and b: "\<forall>n\<ge>Ng. norm (g n) \<ge> cg * norm (G n)"
    using eventually_sequentially by auto
  let ?cg = "max (1/cg) 1"
  have nncg2: "?cg \<ge> 1" by auto
  have b2: "\<And>n. n\<ge>max Ng N \<Longrightarrow>  G n  \<le> ?cg * norm (g n)"
  proof -
    fix n assume n:"n\<ge>max Ng N"
    then have n: "n\<ge> Ng" and nl: "n\<ge> N" by auto
    from nl posG have "G n \<ge> 0"
      using less_eq_real_def of_nat_le_iff by blast 
    then have "G n = norm (G n)" by auto
    also from n have "norm (G n) \<le> norm (g n) / cg" using b nncg
      by (simp add: mult.commute pos_le_divide_eq)  
    also have "\<dots> = (1/cg) * norm (g n)" by auto
    also have "\<dots> \<le> ?cg * norm (g n)" apply(rule mult_right_mono) by auto 
    finally show "G n \<le> max (1 / cg) 1 * norm (g n)" .
  qed

  let ?N' = "max Ng (N+1)"
  let ?N = "2*?N'"
  have n: "norm (f ?N) > 0"
  proof -
    have "?N>0" by auto then
    obtain N' where f: "?N=Suc N'" using gr0_implies_Suc by blast
    then have p: "N' \<ge> N"
      by (metis Suc_eq_plus1 Suc_le_mono max.cobounded2 nat_le_prod_with_le zero_neq_numeral) 
    have gN: "G N' > 0" apply(rule posG) using p by simp
    have n: "N'\<ge>Ng" using f
      by (metis add_le_cancel_left antisym_conv le_add_same_cancel1 le_simps(3) linorder_not_le max.bounded_iff nat_mult_2 zero_order(1)) 
    have "0 < cg * norm (G N')" using gN nncg by auto
    also have "\<dots> \<le>  norm (g N')" using b n  by auto
    also have "\<dots> \<le> norm (f N' + g N')" using assms(3,4) by auto
    also have "\<dots> = norm (f ?N)" unfolding f using p assms(1) by auto 
    finally show ?thesis .
  qed
  let ?nfN = "norm (?N * G ?N)/(norm (f ?N))"
 
  define nfN' where "nfN' = max ?nfN C" 

  show ?thesis apply(rule bigomegaI[where c="?cg * nfN'"])
    apply(rule eventually_sequentiallyI[where c="?N"])
    subgoal for x
      proof(induction rule: Nat.dec_induct)
        case base
        have "norm (?N * G ?N) = 1 * (?nfN * (norm (f ?N)))" using n by auto      
        also have "\<dots> \<le> ?cg * (?nfN * (norm (f ?N)))" apply(rule mult_right_mono) using nncg2 by auto 
        also have "\<dots> = (?cg * ?nfN) * (norm (f ?N))" by auto
        also have "\<dots> \<le> (?cg * nfN') * (norm (f ?N))" unfolding nfN'_def apply(rule mult_right_mono) apply(rule mult_left_mono) by auto
        finally show ?case by auto
      next
        case (step n)
        then have nN: "n\<ge>N"
          by (metis Suc_eq_plus1 Suc_leD le_trans max.cobounded2 nat_le_prod_with_le zero_neq_numeral) 
        then have rNN: "real N \<le> n" by auto
        from step(1) have nNg: "n\<ge>Ng"
          by (metis le_trans max.cobounded1 nat_le_prod_with_le zero_neq_numeral) 
        from nN assms(1) have i: "f (Suc n) = f n + g n" by auto
         have b3: "G n \<le> ?cg * norm (g n)" apply(rule b2) using nN nNg by auto
        have Gm: "G (n+1) > 0" apply(rule posG)  using nN by auto
        from step(1) have "n\<ge>1"
          by (metis One_nat_def Suc_eq_plus1 gr0I le_0_eq le_simps(3) max.cobounded2 mult_is_0 nat.simps(3) numeral_eq_Suc) 

        have 4: "C\<le>nfN'" unfolding nfN'_def by auto
        have "norm ((Suc n) * G (Suc n)) = (n+1)*(G (n+1))" using Gm by auto
        also have "\<dots> \<le>  n*G n + C * G n" using 
            C(1)[OF rNN]
          by (metis Suc_eq_plus1 add.commute of_nat_Suc) 
        also have "\<dots> \<le> ?cg * nfN' * norm (f n) + C * G n" using  step(3) by auto
        also have "\<dots> \<le> ?cg * nfN' * norm (f n) + C*(?cg * norm (g n))" using b3 Cpos apply auto apply(rule mult_left_mono) by auto 
        also have "\<dots> \<le> ?cg * nfN' * norm (f n) + nfN'*(?cg * norm (g n))" using 4 apply auto apply(rule mult_right_mono) by auto
        also have "\<dots> = (?cg * nfN') * norm (f n) + (?cg * nfN') * norm (g n)" by auto
        also have "\<dots> = (?cg * nfN') * (norm (f n) + norm (g n))" by argo
        also have "\<dots> = (?cg* nfN') * (norm (f n + g n))" using assms(3,4) by auto
        also have "\<dots> = (?cg* nfN') * norm (f (Suc n))" using i by auto
        finally    
        show "norm ((Suc n) * G (Suc n)) \<le> (?cg * nfN') * norm (f (Suc n))" . 
      qed
      done
qed


lemma chara_ln: "(x::real)\<ge>3 \<Longrightarrow> (x + 1) * ln (x + 1) \<le> x * ln x +  3 * ln x"
proof -
 { fix x :: real
    assume e: "x\<ge>exp 1"
    then have x1: "ln x\<ge>1"
      using exp_gt_zero less_le_trans ln_ge_iff by blast  
    from e have x2: "1/x \<le> ln x"
      by (metis (mono_tags) landau_o.R_linear landau_o.R_trans ln_less_self mult.left_neutral not_exp_le_zero not_less pos_le_divide_eq x1) 
     
    have x0: "x>0"
      using e exp_gt_zero less_le_trans by blast
    then  have "x+1 = x * (1+ 1/x)"
      by (metis distrib_left divide_self_if less_numeral_extra(3) mult.commute mult.left_neutral times_divide_eq_right)  
    then have"ln (x+1) = ln (x * (1+1/x))" by auto
    also have "\<dots> = ln x + ln (1+ 1/x)" 
      using x0 by(auto intro: ln_mult simp add: add_pos_pos) 
    also have "ln (1+ 1/x) \<le> 1/x" apply(rule ln_add_one_self_le_self) 
      using x0 by auto
    finally have lnx1:  "ln (x + 1) \<le> ln x + 1 / x " by auto
    then have "x * ln (x+1) \<le> x * (ln x + 1 / x)" apply(rule mult_left_mono) using x0 by simp
    also have "\<dots> = x*ln x + 1" using x0
      by (metis distrib_left nonzero_mult_div_cancel_left not_le order_refl times_divide_eq_right)
    also have "\<dots> \<le> x*ln x + ln x" using x1 by auto 
    finally have i: "x * ln (x + 1) \<le> x * ln x + ln x " .

    
    from lnx1 x2 have ii: "ln (x+1) \<le> ln x + ln x" by auto

    have "(x+1)*ln(x+1) = x*ln(x+1) + ln(x+1)" 
      by (simp add: add.commute semiring_normalization_rules(3))
    also have "\<dots> \<le> x * ln x + ln x + ln (x+1)" using i by auto
    also have "\<dots> \<le> x * ln x + ln x + ln x + ln x" using ii by auto
    also have "\<dots> = x*ln x + 3*ln x" by auto
    finally have "(x + 1) * ln (x + 1) \<le> x * ln x +  3 * ln x" .
  } note p=this  
  assume "x\<ge>3"
  then show ?thesis using exp_le by(auto intro!: p)
qed


lemma bigTheta_linear_recurrence_const:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i"  
      and g: "g \<in> \<Theta>(\<lambda>n. 1)" and "\<And>n. f n \<ge> 0" "\<And>n. g n \<ge> 0"
  shows "f \<in> \<Theta>(\<lambda>n. n )" 
proof 
  have "f \<in> O(\<lambda>n. n * 1)" 
    apply (rule bigO_linear_recurrence'[where g=g and N="max N 3"])
    using assms by auto
  thus "f \<in> O(\<lambda>n. n )" by simp

  have "f \<in> \<Omega>(\<lambda>n. n * 1)"
    apply (rule bigOmega_linear_recurrence'[where g=g and N="max N 3" and C=3])
    using assms by (auto)
  thus "f \<in> \<Omega>(\<lambda>n. n)" by simp
qed


lemma bigTheta_linear_recurrence_log:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<ge>N \<Longrightarrow> f (Suc i) = f i + g i"  
      and g: "g \<in> \<Theta>(ln)" and "\<And>n. f n \<ge> 0" "\<And>n. g n \<ge> 0"
  shows "f \<in> \<Theta>(\<lambda>n. n * ln n)" 
proof
  show "f \<in> O(\<lambda>n. n * ln n)" 
    apply (rule bigO_linear_recurrence'[where g=g and N="max N 3"])
    using assms by auto

  show "f \<in> \<Omega>(\<lambda>n. n * ln n)"
    apply (rule bigOmega_linear_recurrence'[where g=g and N="max N 3" and C=3])
    using assms by (auto intro!: chara_ln)  
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

section \<open>Example\<close>

fun bla_time :: "nat \<Rightarrow> real" where
   "bla_time 0 = 1"
|  "bla_time (Suc n) = bla_time n + n"

lemma bla_time_nneg:
  "bla_time n \<ge> 0" by (induct n) auto

lemma "bla_time \<in> \<Theta>(\<lambda>n. real n * real n)"
  apply (rule bigTheta_linear_recurrence[where N=0 and g="(\<lambda>n. n)"])
  by (auto simp: bla_time_nneg)

section \<open>Linear recurrence in the two variable case\<close>

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
        by (meson Cpos frac_le of_nat_le_iff of_nat_0_less_iff order_refl)  
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
    by (simp add: mult.commute pos_le_divide_eq)

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

section \<open>Examples in the bivariate case\<close>

fun ex :: "nat \<times> nat \<Rightarrow> real" where
  "ex (0,m) = 1"
| "ex (Suc n, m) = ex (n,m) + m"

lemma ex_pos[simp]: "0 \<le> ex (n, m)" by (induct n) auto

lemma "ex \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (n * m))"
  apply (rule bivariateTheta[where N=0 and C=1])
  by (auto simp: eventually_prod_sequentially eventually_nonneg_def)
 
end
