(*  Title:      Imperative_HOL_Time/SepLogicTime/SLTC.thy
    Author:     Maximilian P. L. Haslbeck & Bohua Zhan, TU Muenchen
*)

text \<open>The development here follows Separation_Logic_Imperative_HOL
   (by Lammich and Meis) in the AFP \<close>

theory SLTC
  imports Auto2_Imperative_HOL.SepLogic_Base "../Imperative_HOL_Time"
begin                         

section \<open>Partial Heaps\<close>

datatype pheap = pHeap (heapOf: heap) (addrOf: "addr set") (timeOf: nat)
setup \<open>add_simple_datatype "pheap"\<close>

fun in_range :: "(heap \<times> addr set) \<Rightarrow> bool" where
  "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup \<open>add_rewrite_rule @{thm in_range.simps}\<close>

(* Two heaps agree on a set of addresses. *)
definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" where [rewrite]:
  "relH as h h' = (in_range (h, as) \<and> in_range (h', as) \<and>
     (\<forall>t. \<forall>a\<in>as. refs h t a = refs h' t a \<and> arrays h t a = arrays h' t a))"

lemma relH_D [forward]:
  "relH as h h' \<Longrightarrow> in_range (h, as) \<and> in_range (h', as)" by auto2

lemma relH_D2 [rewrite]:
  "relH as h h' \<Longrightarrow> a \<in> as \<Longrightarrow> refs h t a = refs h' t a"
  "relH as h h' \<Longrightarrow> a \<in> as \<Longrightarrow> arrays h t a = arrays h' t a" by auto2+
setup \<open>del_prfstep_thm_eqforward @{thm relH_def}\<close>

lemma relH_dist_union [forward]:
  "relH (as \<union> as') h h' \<Longrightarrow> relH as h h' \<and> relH as' h h'" by auto2

lemma relH_ref [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_ref r \<in> as \<Longrightarrow> Ref_Time.get h r = Ref_Time.get h' r"
  by (simp add: Ref_Time.get_def relH_def)

lemma relH_array [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_array r \<in> as \<Longrightarrow> Array_Time.get h r = Array_Time.get h' r"
  by (simp add: Array_Time.get_def relH_def)

lemma relH_set_ref [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_ref r}} h (Ref_Time.set r x h)"
  by (simp add: Ref_Time.set_def relH_def)

lemma relH_set_array [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_array r}} h (Array_Time.set r x h)"
  by (simp add: Array_Time.set_def relH_def)

section \<open>Assertions\<close>

datatype assn_raw = Assn (assn_fn: "pheap \<Rightarrow> bool")

fun aseval :: "assn_raw \<Rightarrow> pheap \<Rightarrow> bool" where
  "aseval (Assn f) h = f h"
setup \<open>add_rewrite_rule @{thm aseval.simps}\<close>

definition proper :: "assn_raw \<Rightarrow> bool" where [rewrite]:
  "proper P = (
    (\<forall>h as n. aseval P (pHeap h as n) \<longrightarrow> in_range (h,as)) \<and>
    (\<forall>h h' as n. aseval P (pHeap h as n) \<longrightarrow> relH as h h' \<longrightarrow> in_range (h',as) \<longrightarrow> aseval P (pHeap h' as n)))"

fun in_range_assn :: "pheap \<Rightarrow> bool" where
  "in_range_assn (pHeap h as n) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup \<open>add_rewrite_rule @{thm in_range_assn.simps}\<close> 

typedef assn = "Collect proper"
@proof @have "Assn in_range_assn \<in> Collect proper" @qed

setup \<open>add_rewrite_rule @{thm Rep_assn_inject}\<close>
setup \<open>register_wellform_data ("Abs_assn P", ["proper P"])\<close>
setup \<open>add_prfstep_check_req ("Abs_assn P", "proper P")\<close>

lemma Abs_assn_inverse' [rewrite]: "proper y \<Longrightarrow> Rep_assn (Abs_assn y) = y"
  by (simp add: Abs_assn_inverse)

lemma proper_Rep_assn [forward]: "proper (Rep_assn P)" using Rep_assn by auto

definition models :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Turnstile>" 50) where [rewrite_bidir]:
  "h \<Turnstile> P \<longleftrightarrow> aseval (Rep_assn P) h"

lemma models_in_range [resolve]: "pHeap h as n \<Turnstile> P \<Longrightarrow> in_range (h,as)" by auto2

lemma mod_relH [forward]: "relH as h h' \<Longrightarrow> pHeap h as n \<Turnstile> P \<Longrightarrow> pHeap h' as n \<Turnstile> P" by auto2

instantiation assn :: one begin
definition one_assn :: assn where [rewrite]:
  "1 \<equiv> Abs_assn (Assn (\<lambda>h. timeOf h = 0 \<and> addrOf h = {}))"
instance .. end

abbreviation one_assn :: assn ("emp") where "one_assn \<equiv> 1"

lemma one_assn_rule [rewrite]: "h \<Turnstile> emp \<longleftrightarrow> timeOf h = 0 \<and> addrOf h = {}" by auto2
setup \<open>del_prfstep_thm @{thm one_assn_def}\<close>

section \<open>Definition of $\<close>
  
definition timeCredit_assn :: "nat \<Rightarrow> assn" ("$") where [rewrite]:
  "timeCredit_assn n = Abs_assn (Assn (\<lambda>h. timeOf h = n \<and> addrOf h = {}))"
    
lemma timeCredit_assn_rule [rewrite]: "h \<Turnstile> $n \<longleftrightarrow> timeOf h = n \<and> addrOf h = {}" by auto2
setup \<open>del_prfstep_thm @{thm timeCredit_assn_def}\<close>

instantiation assn :: times begin
definition times_assn where [rewrite]:
  "P * Q = Abs_assn (Assn (
    \<lambda>h. (\<exists>as1 as2 n1 n2. addrOf h = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and> timeOf h = n1 + n2 \<and>
         aseval (Rep_assn P) (pHeap (heapOf h) as1 n1) \<and> aseval (Rep_assn Q) (pHeap (heapOf h) as2 n2))))"
instance .. end

lemma mod_star_convE [backward]:
  "pHeap h as n \<Turnstile> A * B \<Longrightarrow>
   \<exists>as1 as2 n1 n2. as = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and> n = n1 + n2 \<and> pHeap h as1 n1 \<Turnstile> A \<and> pHeap h as2 n2 \<Turnstile> B" by auto2

lemma mod_star_convI [backward]:
  "as1 \<inter> as2 = {} \<Longrightarrow> pHeap h as1 n1 \<Turnstile> A \<Longrightarrow> pHeap h as2 n2 \<Turnstile> B \<Longrightarrow>
   pHeap h (as1 \<union> as2) (n1 + n2) \<Turnstile> A * B" by auto2
setup \<open>del_prfstep_thm @{thm times_assn_def}\<close>

lemma aseval_ext [backward]: "\<forall>h. aseval P h = aseval P' h \<Longrightarrow> P = P'"
  apply (cases P) apply (cases P') by auto

lemma assn_ext: "\<forall>h as n. pHeap h as n \<Turnstile> P \<longleftrightarrow> pHeap h as n \<Turnstile> Q \<Longrightarrow> P = Q"
@proof @have "Rep_assn P = Rep_assn Q" @qed
setup \<open>add_backward_prfstep_cond @{thm assn_ext} [with_filt (order_filter "P" "Q")]\<close>

setup \<open>del_prfstep_thm @{thm aseval_ext}\<close>

lemma assn_one_left: "emp * P = (P::assn)"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> P \<longleftrightarrow> pHeap h as n \<Turnstile> emp * P" @with
    @case "pHeap h as n \<Turnstile> P" @with
      @have "as = {} \<union> as"
      @have "n = 0 + n"
    @end
    @case "pHeap h as n \<Turnstile> 1 * P" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> emp" "pHeap h as2 n2 \<Turnstile> P"
    @end
  @end
@qed

lemma assn_times_comm: "P * Q = Q * (P::assn)"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> P * Q \<longleftrightarrow> pHeap h as n \<Turnstile> Q * P" @with
    @case "pHeap h as n \<Turnstile> P * Q" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P" "pHeap h as2 n2 \<Turnstile> Q"
      @have "as = as2 \<union> as1" @have "n = n2 + n1"
    @end
    @case "pHeap h as n \<Turnstile> Q * P" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> Q" "pHeap h as2 n2 \<Turnstile> P"
      @have "as = as2 \<union> as1" @have "n = n2 + n1"
    @end
  @end
@qed

lemma assn_times_assoc: "(P * Q) * R = P * (Q * (R::assn))"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> (P * Q) * R \<longleftrightarrow> pHeap h as n \<Turnstile> P * (Q * R)" @with
    @case "pHeap h as n \<Turnstile> (P * Q) * R" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P * Q" "pHeap h as2 n2 \<Turnstile> R"
      @obtain as11 as12 n11 n12 where
        "as1 = as11 \<union> as12" "as11 \<inter> as12 = {}" "n1 = n11 + n12" "pHeap h as11 n11 \<Turnstile> P" "pHeap h as12 n12 \<Turnstile> Q"
      @have "pHeap h (as12 \<union> as2) (n12 + n2) \<Turnstile> Q * R"
      @have "as = as11 \<union> (as12 \<union> as2)" @have "n = n11 + (n12 + n2)"
    @end
    @case "pHeap h as n \<Turnstile> P * (Q * R)" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P" "pHeap h as2 n2 \<Turnstile> (Q * R)"
      @obtain as21 as22 n21 n22 where
        "as2 = as21 \<union> as22" "as21 \<inter> as22 = {}" "n2 = n21 + n22" "pHeap h as21 n21 \<Turnstile> Q" "pHeap h as22 n22 \<Turnstile> R"
      @have "pHeap h (as1 \<union> as21) (n1 + n21) \<Turnstile> P * Q"
      @have "as = (as1 \<union> as21) \<union> as22" @have "n = (n1 + n21) + n22"
    @end
  @end
@qed

instantiation assn :: comm_monoid_mult begin
  instance apply standard
  apply (rule assn_times_assoc) apply (rule assn_times_comm) by (rule assn_one_left)
end

subsection \<open>Existential Quantification\<close>

definition ex_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>A" 11) where [rewrite]:
  "(\<exists>\<^sub>Ax. P x) = Abs_assn (Assn (\<lambda>h. \<exists>x. h \<Turnstile> P x))"

lemma mod_ex_dist [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x)) \<longleftrightarrow> (\<exists>x. h \<Turnstile> P x)" by auto2
setup \<open>del_prfstep_thm @{thm ex_assn_def}\<close>

lemma ex_distrib_star: "(\<exists>\<^sub>Ax. P x * Q) = (\<exists>\<^sub>Ax. P x) * Q"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q \<longleftrightarrow> pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
    @case "pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> (\<exists>\<^sub>Ax. P x)" "pHeap h as2 n2 \<Turnstile> Q"
      @obtain x where "pHeap h as1 n1 \<Turnstile> P x"
      @have "pHeap h as n \<Turnstile> P x * Q"
    @end
    @case "pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
      @obtain x where "pHeap h as n \<Turnstile> P x * Q"
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P x" "pHeap h as2 n2 \<Turnstile> Q"      
    @end
  @end
@qed

subsection \<open>Disjunction\<close>

definition or_assn :: "assn \<Rightarrow> assn \<Rightarrow> assn" (infixr "\<or>\<^sub>A" 61)  where [rewrite]:
  "A \<or>\<^sub>A B = Abs_assn (Assn (\<lambda>h. h\<Turnstile>A \<or> h\<Turnstile>B ) )"

lemma or_assn_conv: "h \<Turnstile> A \<or>\<^sub>A B \<longleftrightarrow> (h \<Turnstile> A \<or> h \<Turnstile> B)" by auto2

subsection \<open>Conjunction\<close>

definition and_assn :: "assn \<Rightarrow> assn \<Rightarrow> assn" (infixr "\<and>\<^sub>A" 61)  where [rewrite]:
  "A \<and>\<^sub>A B = Abs_assn (Assn (\<lambda>h. h\<Turnstile>A \<and> h\<Turnstile>B ) )"

lemma and_assn_conv: "h \<Turnstile> A \<and>\<^sub>A B \<longleftrightarrow> (h \<Turnstile> A \<and> h \<Turnstile> B)" by auto2

subsection \<open>Pointers\<close>

definition sngr_assn :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn" (infix "\<mapsto>\<^sub>r" 82) where [rewrite]:
  "r \<mapsto>\<^sub>r x = Abs_assn (Assn (
    \<lambda>h. timeOf h = 0 \<and> Ref_Time.get (heapOf h) r = x \<and> addrOf h = {addr_of_ref r} \<and> addr_of_ref r < lim (heapOf h)))"

lemma sngr_assn_rule [rewrite]:
  "pHeap h as n \<Turnstile> r \<mapsto>\<^sub>r x \<longleftrightarrow>
      n = 0 \<and> Ref_Time.get h r = x \<and> as = {addr_of_ref r} \<and> addr_of_ref r < lim h" by auto2
setup \<open>del_prfstep_thm @{thm sngr_assn_def}\<close>

definition snga_assn :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>a" 82) where [rewrite]:
  "r \<mapsto>\<^sub>a x = Abs_assn (Assn (
    \<lambda>h. timeOf h = 0 \<and> Array_Time.get (heapOf h) r = x \<and> addrOf h = {addr_of_array r} \<and> addr_of_array r < lim (heapOf h)))"

lemma snga_assn_rule [rewrite]:
  "pHeap h as n \<Turnstile> r \<mapsto>\<^sub>a x \<longleftrightarrow>
      (n = 0 \<and> Array_Time.get h r = x \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h)" by auto2
setup \<open>del_prfstep_thm @{thm snga_assn_def}\<close>

subsection \<open>Pure Assertions\<close>

definition pure_assn :: "bool \<Rightarrow> assn" ("\<up>") where [rewrite]:
  "\<up>b = Abs_assn (Assn (\<lambda>h. addrOf h = {} \<and> timeOf h = 0 \<and> b))"

lemma pure_assn_rule [rewrite]: "h \<Turnstile> \<up>b \<longleftrightarrow> (addrOf h = {} \<and> timeOf h = 0 \<and> b)" by auto2
setup \<open>del_prfstep_thm @{thm pure_assn_def}\<close>

definition top_assn :: assn ("true") where [rewrite]:
  "top_assn = Abs_assn (Assn in_range_assn)"

lemma top_assn_rule [rewrite]: "pHeap h as n \<Turnstile> true \<longleftrightarrow> in_range (h, as)" by auto2
setup \<open>del_prfstep_thm @{thm top_assn_def}\<close>

setup \<open>del_prfstep_thm @{thm models_def}\<close>

subsection \<open>Properties of assertions\<close>

abbreviation bot_assn :: assn ("false") where "bot_assn \<equiv> \<up>False"

setup \<open>add_forward_prfstep @{thm mod_star_convE}\<close>

lemma mod_false' [resolve]: "\<not>(h \<Turnstile> false * R)" by auto2

lemma top_assn_reduce: "true * true = true"
@proof
  @have "\<forall>h. h \<Turnstile> true * true \<longleftrightarrow> h \<Turnstile> true" @with
    @have "addrOf h = addrOf h \<union> {}"
    @have "timeOf h = timeOf h + 0"
  @end
@qed

lemma mod_pure_star_dist [rewrite]:
  "h \<Turnstile> P * \<up>b \<longleftrightarrow> h \<Turnstile> P \<and> b"
@proof
  @case "h \<Turnstile> P \<and> b" @with
    @have "addrOf h = addrOf h \<union> {}"
    @have "timeOf h = timeOf h + 0"
  @end
@qed
    
lemma mod_timeCredit_dest [rewrite]:
  "pHeap h as n \<Turnstile> P * $m \<longleftrightarrow> pHeap h as (n - m) \<Turnstile> P \<and> n \<ge> m"
@proof
  @case "pHeap h as (n - m) \<Turnstile> P \<and> n \<ge> m" @with
    @have "as = as \<union> {}"
    @have "n = (n - m) + m"
  @end  
@qed

lemma pure_conj:  "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2

subsection \<open>Theorems for time credits\<close>

lemma time_credit_add [resolve]: "$(m + n) = $m * $n" by auto2

subsection \<open>Entailment and its properties\<close>

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>A" 10) where [rewrite]:
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>h. h \<Turnstile> P \<longrightarrow> h \<Turnstile> Q)"

lemma entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
lemma entails_true: "A \<Longrightarrow>\<^sub>A true" by auto2
lemma entails_frame [backward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> P * R \<Longrightarrow>\<^sub>A Q * R" by auto2
lemma entails_frame': "\<not> (A * F \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not> (B * F \<Longrightarrow>\<^sub>A Q)" by auto2
lemma entails_frame'': "\<not> (P \<Longrightarrow>\<^sub>A B * F) \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not> (P \<Longrightarrow>\<^sub>A A * F)" by auto2
lemma entails_equiv_forward: "P = Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q" by auto2
lemma entails_equiv_backward: "P = Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A P" by auto2
lemma entailsD [forward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P \<Longrightarrow> h \<Turnstile> Q" by auto2
lemma entailsD': "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P * R \<Longrightarrow> h \<Turnstile> Q * R" by auto2
lemma entails_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C" by auto2

lemma gc_time: "a\<ge>b \<Longrightarrow> $a \<Longrightarrow>\<^sub>A $b * true"
@proof @have "$a = $b * $(a-b)" @qed

lemma entails_pure': "\<not>(\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<not>(emp \<Longrightarrow>\<^sub>A Q) \<and> b)" by auto2
lemma entails_pure: "\<not>(P * \<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<not>(P \<Longrightarrow>\<^sub>A Q) \<and> b)" by auto2
lemma entails_ex: "\<not>((\<exists>\<^sub>Ax. P x) \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<exists>x. \<not>(P x \<Longrightarrow>\<^sub>A Q))" by auto2
lemma entails_ex_post: "\<not>(P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. Q x)) \<Longrightarrow> \<forall>x. \<not>(P \<Longrightarrow>\<^sub>A Q x)" by auto2
lemma entails_pure_post: "\<not>(P \<Longrightarrow>\<^sub>A Q * \<up>b) \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<not>b" by auto2

setup \<open>del_prfstep_thm @{thm entails_def}\<close>

definition time_credit_ge :: "nat \<Rightarrow> nat \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 60) where
  "a \<ge>\<^sub>t b \<longleftrightarrow> a \<ge> b"
setup \<open>add_backward_prfstep (equiv_backward_th @{thm time_credit_ge_def})\<close>

lemma gc_time': "a \<ge>\<^sub>t b \<Longrightarrow> R * $(a + p) \<Longrightarrow>\<^sub>A R * $(b + p) * true"
  by (smt assn_times_assoc assn_times_comm entails_frame gc_time time_credit_add time_credit_ge_def)

lemma gc_time'': "a \<ge>\<^sub>t b \<Longrightarrow> $(a + p) \<Longrightarrow>\<^sub>A $(b + p) * true"
  by (smt add.commute add.right_neutral gc_time' time_credit_add)

section \<open>Setup for timeFrame\<close>
    
setup \<open>fold add_rewrite_rule @{thms timeFrame.simps}\<close>

lemma timeFrame_reduceNone [forward]: "timeFrame n f = None \<Longrightarrow> f = None" by auto2

lemma timeFrame_reduceSome [forward]: "timeFrame n f = (Some (r,h,t)) \<Longrightarrow> f = Some (r,h,t-n) \<and> t\<ge>n"
@proof @case "f = None" @qed

lemma zero_time: "$0 = emp" by auto2

section \<open>Definition of the run predicate\<close>

inductive run :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "run c None None r n"
| "execute c h = None \<Longrightarrow> run c (Some h) None r n"
| "execute c h = Some (r, h', n) \<Longrightarrow> run c (Some h) (Some h') r n"
setup \<open>add_case_induct_rule @{thm run.cases}\<close>
setup \<open>fold add_resolve_prfstep @{thms run.intros(1,2)}\<close>
setup \<open>add_forward_prfstep @{thm run.intros(3)}\<close>

lemma run_complete [resolve]:
  "\<exists>\<sigma>' r n. run c \<sigma> \<sigma>' (r::'a) n"
@proof
  @obtain "r::'a" where "r = r"
  @case "\<sigma> = None" @with @have "run c None None r 0" @end
  @case "execute c (the \<sigma>) = None" @with @have "run c \<sigma> None r 0" @end
@qed

lemma run_to_execute [forward]:
  "run c (Some h) \<sigma>' r n \<Longrightarrow> if \<sigma>' = None then execute c h = None else execute c h = Some (r, the \<sigma>', n)"
@proof @case_induct "run c (Some h) \<sigma>' r n" @qed

setup \<open>add_rewrite_rule @{thm execute_bind(1)}\<close>
lemma runE [forward]:
  "run f (Some h) (Some h') r' t1 \<Longrightarrow> run (f \<bind> g) (Some h) \<sigma> r t \<Longrightarrow> run (g r') (Some h') \<sigma> r (t-t1)" by auto2

setup \<open>add_rewrite_rule @{thm Array_Time.get_alloc}\<close>
setup \<open>add_rewrite_rule @{thm Ref_Time.get_alloc}\<close>
setup \<open>add_rewrite_rule_bidir @{thm Array_Time.length_def}\<close>

section \<open>Definition of hoare triple, and the frame rule.\<close>

definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where [rewrite]:
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

definition hoare_triple :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>") where [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h as \<sigma> r n t. pHeap h as n \<Turnstile> P \<longrightarrow> run c (Some h) \<sigma> r t \<longrightarrow> 
    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n-t) \<Turnstile> Q r \<and> n\<ge>t \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>)))"

lemma hoare_tripleD [forward]:
  "<P> c <Q> \<Longrightarrow> run c (Some h) \<sigma> r t \<Longrightarrow> \<forall>as n. pHeap h as n \<Turnstile> P \<longrightarrow>
    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n-t) \<Turnstile> Q r \<and> n\<ge>t \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>))" by auto2
setup \<open>del_prfstep_thm_eqforward @{thm hoare_triple_def}\<close>

abbreviation hoare_triple' :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") where
  "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

lemma frame_rule [backward]:
  "<P> c <Q> \<Longrightarrow> <P * R> c <\<lambda>x. Q x * R>"
@proof
  @have "\<forall>h as \<sigma> r n t. pHeap h as n \<Turnstile> P * R \<longrightarrow> run c (Some h) \<sigma> r t \<longrightarrow> 
                    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n-t) \<Turnstile> Q r * R \<and> n\<ge>t \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    @obtain as1 as2 n1 n2 where
      "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P" "pHeap h as2 n2 \<Turnstile> R"
    @have "relH as2 h (the \<sigma>)"
    @have "new_addrs h as (the \<sigma>) = new_addrs h as1 (the \<sigma>) \<union> as2"
    @have "n - t = (n1 - t) + n2"
  @end
@qed

(* This is the last use of the definition of separating conjunction. *)
setup \<open>fold del_prfstep_thm [@{thm mod_star_convI}, @{thm mod_star_convE}]\<close>

lemma bind_rule:
  "<P> f <Q> \<Longrightarrow> \<forall>x. <Q x> g x <R> \<Longrightarrow> <P> f \<bind> g <R>"
@proof
  @have "\<forall>h as \<sigma> r n t. pHeap h as n \<Turnstile> P \<longrightarrow> run (f \<bind> g) (Some h) \<sigma> r t \<longrightarrow>
                    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n-t) \<Turnstile> R r \<and> n\<ge>t \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    (* First step from h to h' *)
    @obtain \<sigma>' r' t' where "run f (Some h) \<sigma>' r' t'"
    @obtain h' where "\<sigma>' = Some h'"
    @let "as' = new_addrs h as h'"
    @have "pHeap h' as' (n-t') \<Turnstile> Q r'"

    (* Second step from h' to h'' *)
    @obtain h'' where "\<sigma> = Some h''"
    @let "as'' = new_addrs h' as' h''"
    @have "pHeap h'' as'' (n-t) \<Turnstile> R r \<and> n\<ge>t"
    @have "as'' = new_addrs h as h''"
  @end
@qed

(* Actual statement used: *)
lemma bind_rule':
  "<P> f <Q> \<Longrightarrow> \<not> <P> f \<bind> g <R> \<Longrightarrow> \<exists>x. \<not> <Q x> g x <R>" using bind_rule by blast

lemma pre_rule':
  "\<not> <P * R> f <Q> \<Longrightarrow> P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> \<not> <P' * R> f <Q>"
@proof @have "P * R \<Longrightarrow>\<^sub>A P' * R" @qed


lemma pre_rule:
  "P'\<Longrightarrow>\<^sub>A P \<Longrightarrow> <P> f <Q> \<Longrightarrow> <P' > f <Q>"
@proof @qed

lemma pre_rule'':
  "<P> f <Q> \<Longrightarrow> P' \<Longrightarrow>\<^sub>A P * R \<Longrightarrow> <P'> f <\<lambda>x. Q x * R>"
@proof @have "<P * R> f <\<lambda>x. Q x * R>" @qed

lemma pre_ex_rule:
  "\<not> <\<exists>\<^sub>Ax. P x> f <Q> \<longleftrightarrow> (\<exists>x. \<not> <P x> f <Q>)" by auto2

lemma pre_pure_rule:
  "\<not> <P * \<up>b> f <Q> \<longleftrightarrow> \<not> <P> f <Q> \<and> b" by auto2

lemma pre_pure_rule':
  "\<not> <\<up>b> f <Q> \<longleftrightarrow> \<not> <emp> f <Q> \<and> b" by auto2

lemma post_rule:
  "<P> f <Q> \<Longrightarrow> \<forall>x. Q x \<Longrightarrow>\<^sub>A R x \<Longrightarrow> <P> f <R>" by auto2

declare gc_time' [backward]
declare gc_time'' [backward]
lemma gc_time_hoare': "a \<ge>\<^sub>t b \<Longrightarrow> \<not><R * $(a + p)> c <Q> \<Longrightarrow> \<not><R * $(b + p) * true> c <Q>"
@proof @have "R * $(a+p) \<Longrightarrow>\<^sub>A R * $(b+p) * true" @qed

lemma gc_time_hoare'': "a \<ge>\<^sub>t b \<Longrightarrow> \<not><$(a + p)> c <Q> \<Longrightarrow> \<not><$(b + p) * true> c <Q>"
@proof @have "$(a+p) \<Longrightarrow>\<^sub>A $(b+p) * true" @qed
setup \<open>del_prfstep_thm @{thm gc_time'}\<close>
setup \<open>del_prfstep_thm @{thm gc_time''}\<close>

setup \<open>fold del_prfstep_thm [@{thm entailsD}, @{thm entails_frame}, @{thm frame_rule}]\<close>

(* Actual statement used: *)
lemma post_rule':
  "<P> f <Q> \<Longrightarrow> \<not> <P> f <R> \<Longrightarrow> \<exists>x. \<not> (Q x \<Longrightarrow>\<^sub>A R x)" using post_rule by blast

lemma norm_pre_pure_iff: "<P * \<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <P> c <Q>)" by auto2
lemma norm_pre_pure_iff2: "<\<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <emp> c <Q>)" by auto2

section \<open>Hoare triples for atomic commands\<close>

(* First, those that do not modify the heap. *)
setup \<open>add_rewrite_rule @{thm execute_assert(1)}\<close>
lemma assert_rule:
  "<\<up>(R x) * $1> assert R x <\<lambda>r. \<up>(r = x)>" by auto2

lemma execute_return' [rewrite]: "execute (return x) h = Some (x, h, 1)" by (metis comp_eq_dest_lhs execute_return)
lemma return_rule:
  "<$1> return x <\<lambda>r. \<up>(r = x)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_nth(1)}\<close>
lemma nth_rule:
  "<a \<mapsto>\<^sub>a xs * $1 * \<up>(i < length xs)> Array_Time.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_len}\<close>
lemma length_rule:
  "<a \<mapsto>\<^sub>a xs * $1> Array_Time.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_lookup}\<close>
lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x * $1> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
    
setup \<open>add_rewrite_rule @{thm execute_freeze}\<close>
lemma freeze_rule:
  "<a \<mapsto>\<^sub>a xs * $(1 + length xs)> Array_Time.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>" by auto2

(* Next, the update rules. *)
setup \<open>add_rewrite_rule @{thm Ref_Time.lim_set}\<close>
lemma Array_lim_set [rewrite]: "lim (Array_Time.set p xs h) = lim h" by (simp add: Array_Time.set_def)

setup \<open>fold add_rewrite_rule [@{thm Ref_Time.get_set_eq}, @{thm Array_Time.get_set_eq}]\<close>
setup \<open>add_rewrite_rule @{thm Array_Time.update_def}\<close>

setup \<open>add_rewrite_rule @{thm execute_upd(1)}\<close>
lemma upd_rule:
  "<a \<mapsto>\<^sub>a xs * $1 * \<up>(i < length xs)> Array_Time.upd i x a <\<lambda>r. a \<mapsto>\<^sub>a list_update xs i x * \<up>(r = a)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_update}\<close>
lemma update_rule:
  "<p \<mapsto>\<^sub>r y * $1> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>" by auto2

(* Finally, the allocation rules. *)
lemma lim_set_gen [rewrite]: "lim (h\<lparr>lim := l\<rparr>) = l" by simp

lemma Array_alloc_def' [rewrite]: 
  "Array_Time.alloc xs h = (let l = lim h; r = Array l in (r, (Array_Time.set r xs (h\<lparr>lim := l + 1\<rparr>))))"
  by (simp add: Array_Time.alloc_def)

setup \<open>fold add_rewrite_rule [
  @{thm addr_of_array.simps}, @{thm addr_of_ref.simps}, @{thm Ref_Time.alloc_def}]\<close>

lemma refs_on_Array_set [rewrite]: "refs (Array_Time.set p xs h) t i = refs h t i"
  by (simp add: Array_Time.set_def)

lemma arrays_on_Ref_set [rewrite]: "arrays (Ref_Time.set p x h) t i = arrays h t i"
  by (simp add: Ref_Time.set_def)

lemma refs_on_Array_alloc [rewrite]: "refs (snd (Array_Time.alloc xs h)) t i = refs h t i"
  by (metis (no_types, lifting) Array_Time.alloc_def refs_on_Array_set select_convs(2) snd_conv surjective update_convs(3))

lemma arrays_on_Ref_alloc [rewrite]: "arrays (snd (Ref_Time.alloc x h)) t i = arrays h t i"
  by (metis (no_types, lifting) Ref_Time.alloc_def arrays_on_Ref_set select_convs(1) sndI surjective update_convs(3))

lemma arrays_on_Array_alloc [rewrite]: "i < lim h \<Longrightarrow> arrays (snd (Array_Time.alloc xs h)) t i = arrays h t i"
  by (smt Array_Time.alloc_def Array_Time.set_def addr_of_array.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less simps(1) snd_conv surjective update_convs(1) update_convs(3))

lemma refs_on_Ref_alloc [rewrite]: "i < lim h \<Longrightarrow> refs (snd (Ref_Time.alloc x h)) t i = refs h t i"
  by (smt Ref_Time.alloc_def Ref_Time.set_def addr_of_ref.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less select_convs(2) simps(6) snd_conv surjective update_convs(3))

setup \<open>add_rewrite_rule @{thm execute_new}\<close>
lemma new_rule:
  "<$(n+1)> Array_Time.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>" by auto2


setup \<open>add_rewrite_rule @{thm execute_make}\<close>
lemma make_rule:
  "<$(n+1)> Array_Time.make n f <\<lambda>r. r \<mapsto>\<^sub>a map f [0 ..< n]>" by auto2

setup \<open>add_rewrite_rule @{thm execute_of_list}\<close>
lemma of_list_rule:
  "<$ (1+length xs)> Array_Time.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>" by auto2

setup \<open>add_rewrite_rule @{thm execute_ref}\<close>
lemma ref_rule:
  "<$1> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2

setup \<open>fold del_prfstep_thm [
  @{thm sngr_assn_rule}, @{thm snga_assn_rule}, @{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm mod_pure_star_dist}, @{thm one_assn_rule}, @{thm hoare_triple_def}, @{thm mod_ex_dist},
  @{thm mod_timeCredit_dest}, @{thm timeCredit_assn_rule}]\<close>
setup \<open>del_simple_datatype "pheap"\<close>

subsection \<open>Definition of procedures\<close>

(* ASCII abbreviations for ML files. *)
abbreviation (input) ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation (input) models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

ML_file "rings.ML"
ML_file "rings_test.ML"
ML_file "sep_time_util.ML"
ML_file "sep_util.ML"
ML_file "sep_time_steps.ML"

ML \<open>
structure AssnMatcher = AssnMatcher(SepUtil)
structure SepLogic = SepLogic(SepUtil)
structure SepTimeSteps = SepTimeSteps(SepUtil)
val add_assn_matcher = AssnMatcher.add_assn_matcher
val add_entail_matcher = AssnMatcher.add_entail_matcher
val add_forward_ent_prfstep = SepLogic.add_forward_ent_prfstep
val add_rewrite_ent_rule = SepLogic.add_rewrite_ent_rule
val add_hoare_triple_prfstep = SepLogic.add_hoare_triple_prfstep
\<close>

(* Make sure to add time proofsteps first (execute time_credit_ge first) *)
setup \<open>SepTimeSteps.add_time_proofsteps\<close>
setup \<open>AssnMatcher.add_assn_matcher_proofsteps\<close>
setup \<open>SepLogic.add_sep_logic_proofsteps\<close>

ML_file "sep_time_test.ML"

attribute_setup forward_ent = \<open>setup_attrib add_forward_ent_prfstep\<close>
attribute_setup rewrite_ent = \<open>setup_attrib add_rewrite_ent_rule\<close>
attribute_setup hoare_triple = \<open>setup_attrib add_hoare_triple_prfstep\<close>

setup \<open>fold add_hoare_triple_prfstep [
  @{thm assert_rule}, @{thm update_rule}, @{thm nth_rule}, @{thm upd_rule},
  @{thm return_rule}, @{thm ref_rule}, @{thm lookup_rule}, @{thm new_rule},
  @{thm make_rule}, @{thm of_list_rule}, @{thm length_rule}, @{thm freeze_rule}]\<close>

(* Some simple tests *)

theorem "<$1> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $1> ref x <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $1> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * $1> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * $1> (!b) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $2> do { a := y; !a } <\<lambda>r. a \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $3> do { a := y; a := z; !a } <\<lambda>r. a \<mapsto>\<^sub>r z * \<up>(r = z)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $2> do { y \<leftarrow> !a; ref y} <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<$1> return x <\<lambda>r. \<up>(r = x)>" by auto2

end
