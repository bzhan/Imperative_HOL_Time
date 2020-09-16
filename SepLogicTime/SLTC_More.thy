theory SLTC_More
imports SLTC
begin



subsection \<open>models rules\<close>

declare mod_ex_dist [simp] 
lemma [simp]: "pHeap h {} 0 \<Turnstile> emp" by(simp add: one_assn_rule)

lemma mod_star_trueI: "h\<Turnstile>P \<Longrightarrow> h\<Turnstile>P*true"  
  by (metis assn_times_comm entailsD' entails_true mult.left_neutral) 

lemma mod_false[simp]: "\<not> h\<Turnstile>false"  
  by (simp add: pure_assn_rule)

lemmas mod_pure_star_dist[simp] = mod_pure_star_dist

lemma mod_pure_star_dist'[simp]: "h\<Turnstile>\<up>b*P \<longleftrightarrow> h\<Turnstile>P \<and> b"
  using mod_pure_star_dist  
  by (simp add: mult.commute) 


lemma mod_starD: "h\<Turnstile>A*B \<Longrightarrow> \<exists>h1 h2. h1\<Turnstile>A \<and> h2\<Turnstile>B" 
  by (metis assn_ext mod_star_convE)


subsection \<open>entailment rules\<close>

lemmas ent_true[simp] = entails_true

declare entails_triv [simp]

lemma inst_ex_assn: "A \<Longrightarrow>\<^sub>A B x \<Longrightarrow> A \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. B x)"
  using entails_ex_post by blast 

lemma ent_iffI:
  assumes "A\<Longrightarrow>\<^sub>AB"
  assumes "B\<Longrightarrow>\<^sub>AA"
  shows "A=B"
  apply(rule assn_ext)
  using assms  
  using entails_def by blast  

lemma ent_star_mono: "\<lbrakk> P \<Longrightarrow>\<^sub>A P'; Q \<Longrightarrow>\<^sub>A Q'\<rbrakk> \<Longrightarrow> P*Q \<Longrightarrow>\<^sub>A P'*Q'" 
  using  entails_trans2 entails_frame  by blast


lemma merge_true_star_ctx: "true * (true * P) = true * P"
  by (metis assn_times_assoc top_assn_reduce)

lemma ent_true_drop: 
  "P\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R\<Longrightarrow>\<^sub>AQ*true"
  "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ*true"
  apply (metis assn_times_comm ent_star_mono ent_true merge_true_star_ctx)
  apply (metis assn_one_left ent_star_mono ent_true mult.commute)
  done

lemma ent_true_drop_fst: 
  "R\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R\<Longrightarrow>\<^sub>AQ*true" 
  apply (metis assn_times_comm ent_star_mono ent_true merge_true_star_ctx) 
  done

lemma ent_true_drop_fstf: 
  "R\<Longrightarrow>\<^sub>Atrue*Q \<Longrightarrow> P*R\<Longrightarrow>\<^sub>Atrue*Q" 
  apply (metis ent_star_mono ent_true merge_true_star_ctx) 
  done


lemma ent_ex_preI: "(\<And>x. P x \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> \<exists>\<^sub>Ax. P x \<Longrightarrow>\<^sub>A Q"  
  by (meson entails_ex) 

lemma ent_ex_postI: "Q \<Longrightarrow>\<^sub>A P x \<Longrightarrow> Q \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. P x "  
  using entails_ex_post by blast


lemma entailsI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> h\<Turnstile>Q"
  shows "P \<Longrightarrow>\<^sub>A Q" 
  using assms unfolding entails_def by auto

lemma ent_trans[trans]: "\<lbrakk> P \<Longrightarrow>\<^sub>A Q; Q \<Longrightarrow>\<^sub>AR \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>A R"
  by (auto intro: entailsI dest: entailsD)

lemma ent_frame_fwd:
  assumes R: "P \<Longrightarrow>\<^sub>A R"
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes I: "R*F \<Longrightarrow>\<^sub>A Q"
  shows "Ps \<Longrightarrow>\<^sub>A Q"
  using assms
  by (metis entails_triv ent_star_mono ent_trans)


lemma ent_pure_pre_iff[simp]: "(P*\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (b \<longrightarrow> (P \<Longrightarrow>\<^sub>A Q))"
  unfolding entails_def
  by (auto   )


lemma ent_pure_pre_iff_sng[simp]: 
  "(\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (b \<longrightarrow> (emp \<Longrightarrow>\<^sub>A Q))"
  using ent_pure_pre_iff[where P=emp]
  by simp

lemma ent_pure_post_iff[simp]: 
  "(P \<Longrightarrow>\<^sub>A Q*\<up>b) \<longleftrightarrow> ((\<forall>h. h\<Turnstile>P \<longrightarrow> b) \<and> (P \<Longrightarrow>\<^sub>A Q))"
  unfolding entails_def
  by (auto)

lemma ent_pure_post_iff_sng[simp]: 
  "(P \<Longrightarrow>\<^sub>A \<up>b) \<longleftrightarrow> ((\<forall>h. h\<Turnstile>P \<longrightarrow> b) \<and> (P \<Longrightarrow>\<^sub>A emp))"
  using ent_pure_post_iff[where Q=emp]
  by simp 

lemma ent_false: "false \<Longrightarrow>\<^sub>A P" by simp  


lemma ex_assn_cases: "(Q x \<Longrightarrow>\<^sub>A P) \<or> \<not> (\<exists>\<^sub>A y. Q y \<Longrightarrow>\<^sub>A P)"
  using entails_ex by blast


lemma fr_refl': "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> C * A \<Longrightarrow>\<^sub>A C * B"
  by (blast intro: ent_star_mono entails_triv)

subsection \<open>assertion normalization rules\<close>

lemmas [simp] = zero_time

lemmas merge_true_star[simp] = top_assn_reduce


lemma false_absorb[simp]: "false * R = false" 
  by (simp add: assn_ext mod_false') 


lemma star_false_right[simp]: "P * false = false"
  using false_absorb by (simp add: assn_times_comm)


lemma pure_true[simp]: "\<up>True = emp" 
  by (auto intro: assn_ext simp: one_assn_rule pure_assn_rule)  

lemma pure_assn_eq_conv[simp]: "\<up>P = \<up>Q \<longleftrightarrow> P=Q" 
  by (metis (full_types) assn_times_comm empty_iff in_range.simps mod_false' mod_pure_star_dist top_assn_rule)




lemma ex_distrib_star': "Q * (\<exists>\<^sub>Ax. P x ) = (\<exists>\<^sub>Ax. Q * P x)"
proof -
  have "Q * (\<exists>\<^sub>Ax. P x ) = (\<exists>\<^sub>Ax. P x ) * Q"  
    by (simp add: assn_times_comm)  
  also have "\<dots> = (\<exists>\<^sub>Ax. P x * Q )"
    unfolding ex_distrib_star by simp
  also have "\<dots> = (\<exists>\<^sub>Ax. Q * P x )" 
    by (simp add: assn_times_comm)  
  finally show ?thesis .
qed


lemma ex_false_iff_false[simp]: "(\<exists>\<^sub>A x. false) = false" by (simp add: ent_ex_preI ent_iffI)



subsection "for relH"

text "Transitivity"
lemma relH_trans[trans]: "\<lbrakk>relH as h1 h2; relH as h2 h3\<rbrakk> \<Longrightarrow> relH as h1 h3"
  unfolding relH_def
  by auto

lemma in_range_subset: 
  "\<lbrakk>as \<subseteq> as'; in_range (h,as')\<rbrakk> \<Longrightarrow> in_range (h,as)"
  by auto

lemma relH_subset:
  assumes "relH bs h h'"
  assumes "as \<subseteq> bs"
  shows "relH as h h'"
  using assms unfolding relH_def by (auto intro: in_range_subset)

subsection "new_addrs"

lemma new_addrs_id[simp]: "(new_addrs h as h) = as" unfolding new_addrs_def by auto

subsection "entailst"

definition entailst :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>t" 10)
  where "entailst A B \<equiv> A \<Longrightarrow>\<^sub>A B * true"
lemma enttI: "A\<Longrightarrow>\<^sub>AB*true \<Longrightarrow> A\<Longrightarrow>\<^sub>tB" unfolding entailst_def .
lemma enttD: "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB*true" unfolding entailst_def .



lemma entt_refl': "P\<Longrightarrow>\<^sub>A P * true" 
  by (simp add: entailsI mod_star_trueI) 



lemma entt_fr_drop: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'"
  using ent_true_drop(1) enttD enttI by blast 

lemma entt_trans:
  "entailst A B \<Longrightarrow> entailst B C \<Longrightarrow> entailst A C"
  unfolding entailst_def
  apply (erule ent_trans)
  by (metis assn_times_assoc ent_star_mono ent_true merge_true_star)  

lemma ent_imp_entt: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ" 
  apply (rule enttI)
  apply (erule ent_trans)
  by (simp add: entailsI mod_star_trueI)  


lemma entt_refl[simp, intro!]: "P\<Longrightarrow>\<^sub>t P " 
  by (simp add: entailst_def entailsI mod_star_trueI) 



lemma entt_star_mono: "\<lbrakk>entailst A B; entailst C D\<rbrakk> \<Longrightarrow> entailst (A*C) (B*D)"
  unfolding entailst_def
proof -
  assume a1: "A \<Longrightarrow>\<^sub>A B * true"
  assume "C \<Longrightarrow>\<^sub>A D * true"
  then have "A * C \<Longrightarrow>\<^sub>A true * B * (true * D)"
    using a1 assn_times_comm ent_star_mono by force
  then show "A * C \<Longrightarrow>\<^sub>A B * D * true"
    by (simp add: ab_semigroup_mult_class.mult.left_commute assn_times_comm)
qed  


lemma entt_emp[simp, intro!]:
  "entailst A emp"
  unfolding entailst_def by simp

lemma entt_star_true_simp[simp]:
  "entailst A (B*true) \<longleftrightarrow> entailst A B"
  "entailst (A*true) B \<longleftrightarrow> entailst A B"
  unfolding entailst_def 
  subgoal by (auto simp: assn_times_assoc)
  subgoal
    apply (intro iffI)
    subgoal using entails_def mod_star_trueI by blast  
    subgoal by (metis assn_times_assoc entails_triv ent_star_mono merge_true_star)  
    done
  done

lemma entt_def_true: "(P\<Longrightarrow>\<^sub>tQ) \<equiv> (P*true \<Longrightarrow>\<^sub>A Q*true)"
  unfolding entailst_def
  apply (rule eq_reflection)
  using entailst_def entt_star_true_simp(2) by auto  


lemma entt_frame_fwd:
  assumes "entailst P Q"
  assumes "entailst A (P*F)"
  assumes "entailst (Q*F) B"
  shows "entailst A B"
  using assms
  by (metis entt_refl entt_star_mono entt_trans)

subsection "Heap Or"
  

declare or_assn_conv [simp]
  
lemma ex_distrib_or: "(\<exists>\<^sub>Ax. Q x) \<or>\<^sub>A P = (\<exists>\<^sub>Ax. Q x \<or>\<^sub>A P)"
  by (auto intro!: assn_ext simp: mod_ex_dist)  

lemma sup_commute: "P \<or>\<^sub>A Q = Q \<or>\<^sub>A P"
  by (meson assn_ext or_assn_conv)
 
lemma ent_disjI1:
  assumes "P \<or>\<^sub>A Q \<Longrightarrow>\<^sub>A R" 
  shows "P \<Longrightarrow>\<^sub>A R" using assms unfolding entails_def by simp

lemma ent_disjI2:
  assumes "P \<or>\<^sub>A Q \<Longrightarrow>\<^sub>A R" 
  shows "Q \<Longrightarrow>\<^sub>A R" using assms unfolding entails_def by simp

lemma ent_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entailsI)  

lemma ent_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"     
  by (simp add: entailsI)  

lemma entt_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI1_direct])

lemma entt_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI2_direct])

lemma entt_disjI1': "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC" 
  using entt_disjI1_direct entt_trans by blast  

lemma entt_disjI2': "A\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC" 
  using entt_disjI2_direct entt_trans by blast  

lemma ent_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>AC; B\<Longrightarrow>\<^sub>AC \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>AC"
  by (simp add: entails_def)  

lemma entt_disjD1: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tC"
  using entt_disjI1_direct entt_trans by blast

lemma entt_disjD2: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> B\<Longrightarrow>\<^sub>tC"
  using entt_disjI2_direct entt_trans by blast

lemma mod_star_conv: "h\<Turnstile>A*B 
  \<longleftrightarrow> (\<exists>hr as1 as2 n1 n2. h=pHeap hr (as1\<union>as2) (n1+n2) \<and> as1\<inter>as2={} \<and> pHeap hr as1 n1\<Turnstile>A \<and> pHeap hr as2 n2\<Turnstile>B)"
  apply (cases h)
  apply rule 
  by(auto dest!: mod_star_convE intro!: mod_star_convI) 


lemma star_or_dist1: 
  "(A \<or>\<^sub>A B)*C = (A*C \<or>\<^sub>A B*C)"  
  apply (rule ent_iffI) 
  unfolding entails_def 
  by (fastforce simp: mod_star_conv )+ 
  
lemma star_or_dist2: 
  "C*(A \<or>\<^sub>A B) = (C*A \<or>\<^sub>A C*B)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (fastforce simp: mod_star_conv )+ 

lemmas star_or_dist = star_or_dist1 star_or_dist2  

lemma ent_disjI1': "A\<Longrightarrow>\<^sub>AB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma ent_disjI2': "A\<Longrightarrow>\<^sub>AC \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)


lemma merge_pure_or[simp]:
  "\<up>a \<or>\<^sub>A \<up>b = \<up>(a\<or>b)"
  by(auto intro!: assn_ext simp add: and_assn_conv pure_assn_rule)  



lemma or_assn_false[simp]: 
  "R \<or>\<^sub>A false = R"
  "false \<or>\<^sub>A R = R"
  by (simp_all add: ent_disjE ent_iffI)

subsection \<open>New command ureturn\<close>

definition ureturn :: "'a \<Rightarrow> 'a Heap" where
  [code del]: "ureturn x = Heap_Time_Monad.heap (\<lambda>h. (x,h,0))"

lemma execute_ureturn [execute_simps]:
  "execute (ureturn x) = Some \<circ> (\<lambda>h. (x,h,0))"
  by (simp add: ureturn_def execute_simps)

lemma success_ureturnI [success_intros]:
  "success (ureturn x) h"
  by (rule successI) (simp add: execute_simps)

lemma effect_ureturnI [effect_intros]:
  "h = h' \<Longrightarrow> effect (ureturn x) h h' x 0"
  by (rule effectI) (simp add: execute_simps)

lemma effect_ureturnE [effect_elims]:
  assumes "effect (ureturn x) h h' r n"
  obtains "r = x" "h' = h" "n=0"
  using assms by (rule effectE) (simp add: execute_simps)

lemma ureturn_bind [simp]: "ureturn x \<bind> f =   f x"
  apply (rule Heap_eqI)
  by (auto simp add: execute_simps )


lemma bind_ureturn [simp]: "f \<bind> ureturn =   f"
  by (rule Heap_eqI) (simp add: bind_def execute_simps split: option.splits)



lemma execute_ureturn' [rewrite]: "execute (ureturn x) h = Some (x, h, 0)" by (metis comp_eq_dest_lhs execute_ureturn)

lemma run_ureturnD: "run (ureturn x) (Some h) \<sigma> r t \<Longrightarrow> \<sigma> = Some h \<and> r = x \<and> t = 0"
  by (auto simp add: execute_ureturn' run.simps)


lemma return_rule:
  "<$0> ureturn x <\<lambda>r. \<up>(r = x)>" 
  unfolding hoare_triple_def by (auto dest!: run_ureturnD simp: relH_def timeCredit_assn_rule)



subsection "Heap And"
 

lemma mod_and_dist: "h\<Turnstile>P\<and>\<^sub>AQ \<longleftrightarrow> h\<Turnstile>P \<and> h\<Turnstile>Q"
  by (rule and_assn_conv) 

lemma [simp]: "false\<and>\<^sub>AQ = false"
  apply(rule assn_ext)
  by(simp add: mod_and_dist)
lemma [simp]: "Q\<and>\<^sub>Afalse = false"
  apply(rule assn_ext)
  by(simp add: mod_and_dist)

lemma ent_conjI: "\<lbrakk> A\<Longrightarrow>\<^sub>AB; A\<Longrightarrow>\<^sub>AC \<rbrakk> \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<and>\<^sub>A C"  
  unfolding entails_def by (auto simp: mod_and_dist)

lemma ent_conjE1: "\<lbrakk>A\<Longrightarrow>\<^sub>AC\<rbrakk> \<Longrightarrow> A\<and>\<^sub>AB\<Longrightarrow>\<^sub>AC"
  unfolding entails_def by (auto simp: mod_and_dist)
lemma ent_conjE2: "\<lbrakk>B\<Longrightarrow>\<^sub>AC\<rbrakk> \<Longrightarrow> A\<and>\<^sub>AB\<Longrightarrow>\<^sub>AC"
  unfolding entails_def by (auto simp: mod_and_dist)


lemma true_conj: "true \<and>\<^sub>A P = P"
  using ent_conjE2 ent_conjI ent_iffI by auto


lemma hand_commute[simp]: "A \<and>\<^sub>A B = B \<and>\<^sub>A A"
using ent_conjE1 ent_conjE2 ent_conjI ent_iffI by auto



lemma and_extract_pure_left_iff[simp]: "\<up>b \<and>\<^sub>A Q = (emp\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma and_extract_pure_left_ctx_iff[simp]: "P*\<up>b \<and>\<^sub>A Q = (P\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma and_extract_pure_right_iff[simp]: "P \<and>\<^sub>A \<up>b = (emp\<and>\<^sub>AP)*\<up>b"
  by (cases b) (auto simp: hand_commute)  
  

lemma and_extract_pure_right_ctx_iff[simp]: "P \<and>\<^sub>A Q*\<up>b = (P\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma [simp]: "(x \<and>\<^sub>A y) \<and>\<^sub>A z = x \<and>\<^sub>A y \<and>\<^sub>A z" 
  using assn_ext and_assn_conv by presburger 

 
lemma emp_and [simp]: "emp \<and>\<^sub>A emp = emp"
  unfolding and_assn_def 
  apply (subst (3) one_assn_def)
  by (auto simp: one_assn_rule)

lemma pure_and: "\<up>P \<and>\<^sub>A \<up>Q = \<up>(P \<and> Q)"
  by (auto simp add: pure_conj)


lemma "h \<Turnstile> r \<mapsto>\<^sub>r x \<and>\<^sub>A r' \<mapsto>\<^sub>r y \<Longrightarrow> (r = r' \<and> x = y \<and> card (addrOf h) = 1)"
  by (cases h) (auto simp: and_assn_conv sngr_assn_rule)

subsection \<open>Precision\<close>
text \<open>
  Precision rules describe that parts of an assertion may depend only on the
  underlying heap. For example, the data where a pointer points to is the same
  for the same heap.
\<close>
text \<open>Precision rules should have the form: 
  @{text [display] "\<forall>x y. (h\<Turnstile>(P x * F1) \<and>\<^sub>A (P y * F2)) \<longrightarrow> x=y"}\<close>
definition "precise R \<equiv> \<forall>a a' h p F F'. 
  h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F' \<longrightarrow> a = a'"

lemma preciseI[intro?]: 
  assumes "\<And>a a' h p F F'. h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F' \<Longrightarrow> a = a'"
  shows "precise R"
  using assms unfolding precise_def by blast

lemma preciseD:
  assumes "precise R"
  assumes "h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F'"
  shows "a=a'"
  using assms unfolding precise_def by blast

lemma preciseD':
  assumes "precise R"
  assumes "h \<Turnstile> R a p * F" 
  assumes "h \<Turnstile> R a' p * F'"
  shows "a=a'"
  apply (rule preciseD)
  apply (rule assms)
  apply (simp only: mod_and_dist)
  apply (blast intro: assms)
  done


lemma precise_extr_pure[simp]: 
  "precise (\<lambda>x y. \<up>P * R x y) \<longleftrightarrow> (P \<longrightarrow> precise R)"
  "precise (\<lambda>x y. R x y * \<up>P) \<longleftrightarrow> (P \<longrightarrow> precise R)"
   subgoal apply (cases P) by (auto intro!: preciseI)  
   subgoal apply (cases P) by (auto intro!: preciseI simp: assn_times_comm and_assn_conv)  
   done   
  

lemma sngr_prec: "precise (\<lambda>x p. p\<mapsto>\<^sub>rx)"  
  apply rule
  apply (clarsimp simp: mod_and_dist)
  subgoal for a a' h
    apply(cases h)
    by(auto dest!: mod_star_convE simp: sngr_assn_rule)   
  done

lemma snga_prec: "precise (\<lambda>x p. p\<mapsto>\<^sub>ax)" 
  apply rule
  apply (clarsimp simp: mod_and_dist)
  subgoal for a a' h
    apply(cases h)
    by(auto dest!: mod_star_convE simp: snga_assn_rule)   
  done
  
text \<open>Apply precision rule with frame inference.\<close>
lemma prec_frame:
  assumes PREC: "precise P"
  assumes M1: "h\<Turnstile>(R1 \<and>\<^sub>A R2)"
  assumes F1: "R1 \<Longrightarrow>\<^sub>A P x p * F1"
  assumes F2: "R2 \<Longrightarrow>\<^sub>A P y p * F2"
  shows "x=y"
  using preciseD[OF PREC] M1 F1 F2  
  by (meson mod_and_dist entailsD)



subsection \<open>is_pure_assn\<close>

definition "is_pure_assn a \<equiv> \<exists>P. a=\<up>P"
lemma is_pure_assnE: assumes "is_pure_assn a" obtains P where "a=\<up>P"
  using assms
  by (auto simp: is_pure_assn_def)

lemma is_pure_assn_pure[simp, intro!]: "is_pure_assn (\<up>P)" 
  by (auto simp add: is_pure_assn_def)

lemma is_pure_assn_basic_simps[simp]:
  "is_pure_assn false"
  "is_pure_assn emp"
proof -
  have "is_pure_assn (\<up>False)" by rule thus "is_pure_assn false" by simp
  have "is_pure_assn (\<up>True)" by rule thus "is_pure_assn emp" by simp
qed  

lemma is_pure_assn_starI[simp,intro!]: 
  "\<lbrakk>is_pure_assn a; is_pure_assn b\<rbrakk> \<Longrightarrow> is_pure_assn (a*b)" 
    by (auto simp: pure_conj[symmetric] elim!: is_pure_assnE)

subsection "some automation"


text \<open>Move existential quantifiers to the front of assertions\<close>
lemma ex_assn_move_out[simp]:
  "\<And>Q R. (\<exists>\<^sub>Ax. Q x) * R = (\<exists>\<^sub>Ax. (Q x * R))"
  "\<And>Q R. R * (\<exists>\<^sub>Ax. Q x) = (\<exists>\<^sub>Ax. (R * Q x))"

  "\<And>P Q. (\<exists>\<^sub>Ax. Q x) \<or>\<^sub>A P = (\<exists>\<^sub>Ax. (Q x \<or>\<^sub>A P))"
  "\<And>P Q. Q \<or>\<^sub>A (\<exists>\<^sub>Ax. P x) = (\<exists>\<^sub>Ax. (Q \<or>\<^sub>A P x))"
  apply -
  apply (simp add: ex_distrib_star)
  apply (subst mult.commute)
  apply (subst (2) mult.commute)
  apply (simp add: ex_distrib_star)

  apply (simp add: ex_distrib_or)  
  apply (subst sup_commute)
  apply (subst (2) sup_commute)
  apply (simp add: ex_distrib_or)
  done  
 
lemmas star_aci = 
  mult.assoc[where 'a=assn] mult.commute[where 'a=assn] mult.left_commute[where 'a=assn]
  assn_one_left mult_1_right[where 'a=assn]
  merge_true_star merge_true_star_ctx



declare pure_assn_rule [simp] 

subsection \<open>two references pointing to same address\<close>

text \<open>Two disjoint parts of the heap cannot be pointed to by the 
  same pointer\<close>
lemma sngr_same_false_aux: "p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y \<Longrightarrow>\<^sub>A false"
  unfolding entails_def 
  apply clarify
  apply (case_tac h)
  apply clarify
  apply (drule mod_star_convE)
  apply (clarsimp simp add: sngr_assn_rule)
  done

lemma snga_same_false_aux: "p \<mapsto>\<^sub>a x * p \<mapsto>\<^sub>a y \<Longrightarrow>\<^sub>A false"
  unfolding entails_def
  apply clarify
  apply (case_tac h)
  apply clarify
  apply (drule mod_star_convE)
  apply clarify
  apply (subst (asm) snga_assn_rule)
  apply (subst (asm) snga_assn_rule)
  apply clarify
  apply (clarsimp simp add: snga_assn_rule)
  done

lemma sngr_same_false[simp]: 
  "p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y = false"
by (intro sngr_same_false_aux ent_false ent_iffI)

lemma snga_same_false[simp]: 
  "p \<mapsto>\<^sub>a x * p \<mapsto>\<^sub>a y = false"
  by (intro snga_same_false_aux ent_false ent_iffI)



subsection \<open>Hoare consequence rules\<close>


lemmas fi_rule = pre_rule''

lemma cons_post_rule: "<P> c <Q> \<Longrightarrow> (\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x) \<Longrightarrow> <P> c <Q'>"
  using post_rule by blast

lemma cons_rule:
  assumes "<P> c <Q>" "P' \<Longrightarrow>\<^sub>A P" "\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x"
  shows "<P'> c <Q'>"
  using assms pre_rule cons_post_rule by blast

lemma cons_rulet:
  assumes T: "<P> c <Q>\<^sub>t" and PRE: "P' \<Longrightarrow>\<^sub>t P" and POST:"\<And>x. Q x \<Longrightarrow>\<^sub>t Q' x"
  shows "<P'> c <Q'>\<^sub>t"
proof -
  have "<P'> c <\<lambda>a. Q a * true>\<^sub>t"
    using PRE \<open><P> c <Q>\<^sub>t\<close> fi_rule entailst_def by blast
  then show ?thesis
    using POST by (meson entailst_def cons_post_rule ent_true_drop(1))
qed



end
