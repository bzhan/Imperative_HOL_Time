(* Example in linked lists *)

theory LinkedList
imports SepAuto Asymptotics_Recurrences
begin

section {* List assertion *}

datatype 'a node = Node (val: "'a") (nxt: "'a node ref option")
setup {* fold add_rewrite_rule @{thms node.sel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}

fun node_encode :: "'a::heap node \<Rightarrow> nat" where
  "node_encode (Node x r) = to_nat (x, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun os_list :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "os_list [] p = \<up>(p = None)"
| "os_list (x # l) (Some p) = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * os_list l q)"
| "os_list (x # l) None = false"
setup {* fold add_rewrite_ent_rule @{thms os_list.simps} *}

lemma os_list_empty [forward_ent_shadow]:
  "os_list [] p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma os_list_Cons [forward_ent_shadow]:
  "os_list (x # l) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * os_list l q)" by auto2

lemma os_list_empty_none [forward_ent]:
  "os_list (x # l) None \<Longrightarrow>\<^sub>A false" by auto2

lemma os_list_Cons_some [forward_ent]:
  "os_list [] (Some p) \<Longrightarrow>\<^sub>A false" by auto2

lemma os_list_is_some [forward_ent]:
  "os_list (x # l) p \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma os_list_is_not_empty [forward_ent]:
  "os_list xs (Some p) \<Longrightarrow>\<^sub>A true * \<up>(xs \<noteq> [])" by auto2

lemma os_list_none: "emp \<Longrightarrow>\<^sub>A os_list [] None" by auto2

lemma os_list_constr_ent:
  "p \<mapsto>\<^sub>r Node x q * os_list l q \<Longrightarrow>\<^sub>A os_list (x # l) (Some p)" by auto2

setup {* fold add_entail_matcher [@{thm os_list_none}, @{thm os_list_constr_ent}] *}
setup {* fold del_prfstep_thm @{thms os_list.simps} *}

type_synonym 'a os_list = "'a node ref option"

section {* Basic operations *}

definition os_empty :: "'a::heap os_list Heap" where [sep_proc]:
  "os_empty = return None"

lemma os_empty_rule [hoare_triple]:
  "<$1> os_empty <os_list []>" by auto2

definition os_is_empty :: "'a::heap os_list \<Rightarrow> bool Heap" where [sep_proc]:
  "os_is_empty b = return (b = None)"

lemma os_is_empty_rule [hoare_triple]:
  "<os_list xs b * $1> os_is_empty b <\<lambda>r. os_list xs b * \<up>(r \<longleftrightarrow> xs = [])>"
@proof @case "xs = []" @have "xs = hd xs # tl xs" @qed

definition os_prepend :: "'a \<Rightarrow> 'a::heap os_list \<Rightarrow> 'a os_list Heap" where [sep_proc]:
  "os_prepend a n = do { p \<leftarrow> ref (Node a n); return (Some p) }"

lemma os_prepend_rule [hoare_triple]:
  "<os_list xs n * $2> os_prepend x n <os_list (x # xs)>" by auto2

definition os_pop :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where [sep_proc]:
  "os_pop r = (case r of
    None \<Rightarrow> raise ''Empty Os_list'' |
    Some p \<Rightarrow> do {m \<leftarrow> !p; return (val m, nxt m)})"

lemma os_pop_rule [hoare_triple]:
  "<os_list xs (Some p) * $2>
   os_pop (Some p)
   <\<lambda>(x,r'). os_list (tl xs) r' * p \<mapsto>\<^sub>r (Node x r') * \<up>(x = hd xs)>"
@proof @case "xs = []" @have "xs = hd xs # tl xs" @qed

section \<open>Reverse\<close>

partial_function (heap) os_reverse_aux :: "'a::heap os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_reverse_aux q p = (case p of
    None \<Rightarrow> return q |
    Some r \<Rightarrow> do {
      v \<leftarrow> !r;
      r := Node (val v) q;
      os_reverse_aux p (nxt v) })"
declare os_reverse_aux.simps [sep_proc]

lemma os_reverse_aux_rule [hoare_triple]:
  "<os_list xs p * os_list ys q * $(2 * length xs + 1)>
    os_reverse_aux q p 
   <os_list ((rev xs) @ ys)>"
@proof @induct xs arbitrary p q ys @qed

definition os_reverse :: "'a::heap os_list \<Rightarrow> 'a os_list Heap" where [sep_proc]:
  "os_reverse p = os_reverse_aux None p"

lemma os_reverse_rule:
  "<os_list xs p * $(2 * length xs + 1)>
   os_reverse p
   <os_list (rev xs)>" by auto2

section \<open>Remove\<close>

setup {* fold add_rewrite_rule @{thms removeAll.simps} *}

partial_function (heap) os_rem :: "'a::heap \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option Heap" where
  "os_rem x b = (case b of 
     None \<Rightarrow> return None |
     Some p \<Rightarrow> do { 
       n \<leftarrow> !p;
       q \<leftarrow> os_rem x (nxt n);
       (if val n = x then
          return q
        else do {
          p := Node (val n) q; 
          return (Some p) }) })"
declare os_rem.simps [sep_proc]

lemma os_rem_rule [hoare_triple]:
  "<os_list xs b * $(4 * length xs + 1)>
   os_rem x b
   <\<lambda>r. os_list (removeAll x xs) r>\<^sub>t"
@proof @induct xs arbitrary b @qed

section \<open>Extract list\<close>

partial_function (heap) extract_list :: "'a::heap os_list \<Rightarrow> 'a list Heap" where
  "extract_list p = (case p of
    None \<Rightarrow> return []
  | Some pp \<Rightarrow> do {
      v \<leftarrow> !pp;
      ls \<leftarrow> extract_list (nxt v);
      return (val v # ls)
    })"
declare extract_list.simps [sep_proc]

lemma extract_list_rule [hoare_triple]:
  "<os_list l p * $(2 * length l + 1)>
   extract_list p
   <\<lambda>r. os_list l p * \<up>(r = l)>"
@proof @induct l arbitrary p @qed
  
section \<open>Ordered insert\<close>

fun list_insert :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_insert x [] = [x]"
| "list_insert x (y # ys) = (
    if x \<le> y then x # (y # ys) else y # list_insert x ys)"
setup {* fold add_rewrite_rule @{thms list_insert.simps} *}

lemma list_insert_length [rewrite_arg]:
  "length (list_insert x xs) = length xs + 1"
@proof @induct xs @qed

lemma list_insert_mset [rewrite]:
  "mset (list_insert x xs) = {#x#} + mset xs"
@proof @induct xs @qed

lemma list_insert_set [rewrite]:
  "set (list_insert x xs) = {x} \<union> set xs"
@proof @induct xs @qed

lemma list_insert_sorted [forward]:
  "sorted xs \<Longrightarrow> sorted (list_insert x xs)"
@proof @induct xs @qed

partial_function (heap) os_insert :: "'a::{ord,heap} \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_insert x b = (case b of
      None \<Rightarrow> os_prepend x None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        (if x \<le> val v then os_prepend x b
         else do {
           q \<leftarrow> os_insert x (nxt v);
           p := Node (val v) q;
           return (Some p) }) })"
declare os_insert.simps [sep_proc]

lemma os_insert_to_fun [hoare_triple]:
  "<os_list xs b * $(3 * length xs + 2)>
   os_insert x b
   <os_list (list_insert x xs)>\<^sub>t"
@proof @induct xs arbitrary b @qed

section \<open>Insertion sort\<close>

fun insert_sort :: "'a::ord list \<Rightarrow> 'a list" where
  "insert_sort [] = []"
| "insert_sort (x # xs) = list_insert x (insert_sort xs)"
setup {* fold add_rewrite_rule @{thms insert_sort.simps} *}

lemma insert_sort_length [rewrite_arg]:
  "length (insert_sort xs) = length xs"
@proof @induct xs @qed

lemma insert_sort_mset [rewrite]:
  "mset (insert_sort xs) = mset xs"
@proof @induct xs @qed

lemma insert_sort_sorted [forward]:
  "sorted (insert_sort xs)"
@proof @induct xs @qed

lemma insert_sort_is_sort [rewrite]:
  "insert_sort xs = sort xs" by auto2

fun os_insert_sort_aux :: "'a::{heap,ord} list \<Rightarrow> 'a os_list Heap" where
  "os_insert_sort_aux [] = (return None)"
| "os_insert_sort_aux (x # xs) = do {
     b \<leftarrow> os_insert_sort_aux xs;
     b' \<leftarrow> os_insert x b;
     return b'
   }"
declare os_insert_sort_aux.simps [sep_proc]

lemma os_insert_sort_aux_correct [hoare_triple]:
  "<$(2 * length xs * length xs + length xs + 1)>
   os_insert_sort_aux xs
   <os_list (insert_sort xs)>\<^sub>t"
@proof @induct xs @qed

definition os_insert_sort :: "'a::{ord,heap} list \<Rightarrow> 'a list Heap" where [sep_proc]:
  "os_insert_sort xs = do {
    p \<leftarrow> os_insert_sort_aux xs;
    l \<leftarrow> extract_list p;
    return l
  }"

definition os_insert_sort_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "os_insert_sort_time n = 2 * n * n + 3 * n + 3"

lemma os_insert_sort_rule [hoare_triple]:
  "<$(os_insert_sort_time (length xs))>
   os_insert_sort xs
   <\<lambda>ys. \<up>(ys = sort xs)>\<^sub>t" by auto2

lemma os_insert_sort_time_monotonic [backward]:
  "n \<le> m \<Longrightarrow> os_insert_sort_time n \<le> os_insert_sort_time m"
@proof @have "3 * n \<le> 3 * m" @qed

setup {* del_prfstep_thm @{thm os_insert_sort_time_def} *}

(* Alternative proof using bigO *)

fun os_insert_sort_aux' :: "'a::{heap,ord} list \<Rightarrow> 'a os_list Heap" where
  "os_insert_sort_aux' [] = (return None)"
| "os_insert_sort_aux' (x # xs) = do {
     b \<leftarrow> os_insert_sort_aux' xs;
     b' \<leftarrow> os_insert x b;
     return b'
   }"
declare os_insert_sort_aux'.simps [sep_proc]

fun os_insert_sort_aux_time :: "nat \<Rightarrow> nat" where 
  "os_insert_sort_aux_time 0 = 1"
| "os_insert_sort_aux_time (Suc n) = os_insert_sort_aux_time n + 3 * n + 2 + 1" 
setup {* add_rewrite_rule @{thm os_insert_sort_aux_time.simps(1)} *}

lemma os_insert_sort_aux_time_simps [rewrite]:
  "os_insert_sort_aux_time (n + 1) = os_insert_sort_aux_time n + 3 * n + 2 + 1" by simp

lemma os_insert_sort_aux_correct':
  "<$(os_insert_sort_aux_time (length xs))>
   os_insert_sort_aux' xs
   <os_list (insert_sort xs)>\<^sub>t"
@proof @induct xs @qed

lemma os_insert_sort_aux_time_asym': "os_insert_sort_aux_time \<in> \<Theta>(\<lambda>n. n * n)"
  by (rule bigTheta_linear_recurrence[where N=0]) auto

end
