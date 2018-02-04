theory Tree_Impl
  imports SepAuto Tree
begin

section {* Abstract tree *}

setup {* add_resolve_prfstep @{thm tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm tree.simps(1)})) *}
setup {* fold add_rewrite_rule @{thms tree.sel} *}
setup {* add_forward_prfstep_cond @{thm tree.collapse} [with_cond "?tree \<noteq> Node ?l ?v ?r"] *}
setup {* add_var_induct_rule @{thm tree.induct} *}
setup {* fold add_rewrite_rule @{thms tree.case} *}

section {* Tree nodes *}

datatype 'a node =
  Node (lsub: "'a node ref option") (val: 'a) (rsub: "'a node ref option")
setup {* fold add_rewrite_rule @{thms node.sel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}

fun node_encode :: "'a::heap node \<Rightarrow> nat" where
  "node_encode (Node l v r) = to_nat (l, v, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun btree :: "'a::heap tree \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "btree Leaf p = \<up>(p = None)"
| "btree (tree.Node lt v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp v rp * btree lt lp * btree rt rp)"
| "btree (tree.Node lt v rt) None = false"
setup {* fold add_rewrite_ent_rule @{thms btree.simps} *}

lemma btree_Leaf [forward_ent_shadow]: "btree Leaf p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma btree_not_Leaf [forward_ent_shadow]:
  "btree (tree.Node lt v rt) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp v rp * btree lt lp * btree rt rp)"
  by auto2

lemma btree_Node_none [forward_ent]: "btree (tree.Node lt v rt) None \<Longrightarrow>\<^sub>A false" by auto2

lemma btree_Leaf_some [forward_ent]: "btree Leaf (Some p) \<Longrightarrow>\<^sub>A false" by auto2

lemma btree_is_some [forward_ent]: "btree (tree.Node lt v rt) p \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma btree_is_not_Leaf [forward_ent]: "btree t (Some p) \<Longrightarrow>\<^sub>A true * \<up>(t \<noteq> Leaf)" by auto2

lemma btree_none: "emp \<Longrightarrow>\<^sub>A btree tree.Leaf None" by auto2

lemma btree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (tree.Node lt v rt) (Some p)" by auto2

setup {* fold add_entail_matcher [@{thm btree_none}, @{thm btree_constr_ent}] *}
setup {* fold del_prfstep_thm @{thms btree.simps} *}

type_synonym 'a ptree = "'a node ref option"

section {* Basic operations *}

definition tree_empty :: "'a ptree Heap" where [sep_proc]:
  "tree_empty = return None"

lemma tree_empty_rule [hoare_triple]:
  "<$1> tree_empty <btree Leaf>" by auto2

definition tree_is_empty :: "'a ptree \<Rightarrow> bool Heap" where [sep_proc]:
  "tree_is_empty b = return (b = None)"

lemma tree_is_empty_rule [hoare_triple]:
  "<btree t b * $1>
   tree_is_empty b
   <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Leaf)>" by auto2

definition tree_constr :: "'a::heap \<Rightarrow> 'a ptree Heap" where [sep_proc]:
  "tree_constr v = do { p \<leftarrow> ref (Node None v None); return (Some p) }"

lemma tree_constr_rule [hoare_triple]:
  "<$2> tree_constr v <btree \<langle>Leaf, v, Leaf\<rangle>>" by auto2

definition rotate_l :: "'a::heap ptree \<Rightarrow> 'a ptree Heap" where [sep_proc]:
  "rotate_l p = (case p of
    None \<Rightarrow> raise ''Empty ptree''
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     (case rsub t of
        None \<Rightarrow> raise ''Empty rsub''
      | Some rp \<Rightarrow> do {
         rt \<leftarrow> !rp;
         pp := Node (lsub t) (val t) (lsub rt);
         rp := Node p (val rt) (rsub rt);
         return (rsub t) })})"

lemma rotate_l_rule [hoare_triple]:
  "<btree \<langle>a, v, \<langle>b, w, c\<rangle>\<rangle> p * $5>
   rotate_l p
   <btree \<langle>\<langle>a, v, b\<rangle>, w, c\<rangle>>" by auto2

definition rotate_r :: "'a::heap ptree \<Rightarrow> 'a ptree Heap" where [sep_proc]:
  "rotate_r p = (case p of
    None \<Rightarrow> raise ''Empty ptree''
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     (case lsub t of
        None \<Rightarrow> raise ''Empty lsub''
      | Some lp \<Rightarrow> do {
         lt \<leftarrow> !lp;
         pp := Node (rsub lt) (val t) (rsub t);
         lp := Node (lsub lt) (val lt) p;
         return (lsub t) })})"

lemma rotate_r_rule [hoare_triple]:
  "<btree \<langle>\<langle>a, v, b\<rangle>, w, c\<rangle> p * $5>
   rotate_r p
   <btree \<langle>a, v, \<langle>b, w, c\<rangle>\<rangle>>" by auto2

end
