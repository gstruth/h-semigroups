(*section {* Verification Component Based on Bi-Semigroups *}*)
theory H_Semigroup
  imports Main GCD 
    
begin

notation times (infixl "\<cdot>" 70)
  and relcomp (infixl ";" 70)

class H_monoid = monoid_mult + plus +
  fixes preo :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 50) 
  and star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
  assumes preo_refl: "x \<preceq> x"
  and preo_trans: "x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
  and add_isol: "x \<preceq> y \<Longrightarrow> z + x \<preceq> z + y"
  and add_isor: "x \<preceq> y \<Longrightarrow> x + z \<preceq> y + z"
  and mult_isol: "x \<preceq> y \<Longrightarrow> z \<cdot> x \<preceq> z \<cdot> y"
  and mult_isor: "x \<preceq> y \<Longrightarrow> x \<cdot> z \<preceq> y \<cdot> z"
  and star_sim: "y \<cdot> x \<preceq> x \<cdot> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<preceq> x\<^sup>\<star> \<cdot> y"

begin

definition "H p x q \<equiv> p \<cdot> x \<preceq> x \<cdot> q"

lemma H_skip: "H p 1 p"
  by (simp add: H_def preo_refl)

lemma H_cons: "p \<preceq> p' \<Longrightarrow> H p' x q' \<Longrightarrow> q' \<preceq> q \<Longrightarrow> H p x q"
  by (meson H_def mult_isol mult_isor preo_trans)

lemma H_seq: " H r y q \<Longrightarrow> H p x r \<Longrightarrow> H p (x \<cdot> y) q" 
  by (simp add: H_def, rule preo_trans, drule mult_isor, auto simp: mult_assoc mult_isol)

lemma H_cond: 
assumes "\<And>x y. p \<cdot> (x + y) \<preceq> p \<cdot> x + p \<cdot> y" and "\<And>x y. x \<cdot> q + y \<cdot> q \<preceq> (x + y) \<cdot> q"
shows "H p v (p \<cdot> v) \<Longrightarrow> H p w (p \<cdot> w) \<Longrightarrow> H (p \<cdot> v) x q \<Longrightarrow> H (p \<cdot> w) y q \<Longrightarrow> H p (v \<cdot> x + w \<cdot> y) q"
  by (meson H_def assms add_isol add_isor preo_trans H_seq assms)

lemma H_loopi: "H i v (i \<cdot> v) \<Longrightarrow> H i w (i \<cdot> w) \<Longrightarrow> H (i \<cdot> v) x i \<Longrightarrow> p \<preceq> i \<Longrightarrow> i \<cdot> w \<preceq> q \<Longrightarrow> H p ((v \<cdot> x)\<^sup>\<star> \<cdot> w) q"
  by (meson H_cons H_def H_seq star_sim)

end

type_synonym 'a pred = "'a \<Rightarrow> bool" 
type_synonym 'a store = "string  \<Rightarrow> 'a"

lemma rel_star_sim_aux: "Y ; X \<subseteq> X ; Y \<Longrightarrow> Y ; X ^^ i \<subseteq> X ^^ i ; Y" 
  by (induct i, simp_all, blast)

interpretation rel_hm: H_monoid Id "op ;" "op \<union>" "op \<subseteq>" rtrancl
  by (standard, auto simp: SUP_subset_mono rtrancl_is_UN_relpow relcomp_UNION_distrib relcomp_UNION_distrib2 rel_star_sim_aux)
    
definition p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>") where "\<lceil>P\<rceil> = {(s,s) |s. P s}"
  
lemma p2r_mult_hom [simp]: "\<lceil>P\<rceil> ; \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>" 
  by (auto simp: p2r_def)

definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
  "v ::= e = {(s,s (v := e s)) |s. True}"

lemma H_assign: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> rel_hm.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil>"
  by (auto simp: rel_hm.H_def p2r_def gets_def)

definition if_then_else :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel " ("if _ then _ else _ fi" [64,64,64] 63) where
  "if P then X else Y fi = \<lceil>P\<rceil> ; X \<union> \<lceil>\<lambda>s. \<not> P s\<rceil> ; Y"

definition while :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("while _ do _ od" [64,64] 63) where
  "while P do X od = (\<lceil>P\<rceil> ; X)\<^sup>* ; \<lceil>\<lambda>s. \<not> P s\<rceil>" 

definition while_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while P inv I do X od = (\<lceil>P\<rceil> ; X)\<^sup>* ; \<lceil>\<lambda>s. \<not> P s\<rceil>" 

lemma rel_ref: "rel_hm.H \<lceil>P\<rceil> \<lceil>Q\<rceil> (\<lceil>P\<rceil> ; \<lceil>Q\<rceil>)"
  by (auto simp: rel_hm.H_def p2r_def)

lemma sH_cons: "(\<forall>s. P s \<longrightarrow> P' s) \<Longrightarrow> rel_hm.H \<lceil>P'\<rceil> X \<lceil>Q\<rceil> \<Longrightarrow> (\<forall>s. Q' s \<longrightarrow> Q s) \<Longrightarrow> rel_hm.H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"
  by (rule rel_hm.H_cons, auto simp: p2r_def)

lemma sH_cond: "rel_hm.H (\<lceil>P\<rceil> ; \<lceil>T\<rceil>) X \<lceil>Q\<rceil> \<Longrightarrow> rel_hm.H (\<lceil>P\<rceil> ; \<lceil>\<lambda>s.  \<not> T s\<rceil>) Y \<lceil>Q\<rceil> \<Longrightarrow> rel_hm.H \<lceil>P\<rceil> (if T then X else Y fi) \<lceil>Q\<rceil>"
  by (simp only: if_then_else_def, intro rel_hm.H_cond, auto, (metis p2r_mult_hom rel_ref)+)

lemma sH_whilei: "\<forall>s. P s \<longrightarrow> I s \<Longrightarrow> \<forall>s. I s \<and> \<not> R s \<longrightarrow> Q s \<Longrightarrow> rel_hm.H (\<lceil>I\<rceil>; \<lceil>R\<rceil>) X \<lceil>I\<rceil> \<Longrightarrow> rel_hm.H \<lceil>P\<rceil> (while R inv I do X od) \<lceil>Q\<rceil>"
  by (simp only: while_inv_def, intro rel_hm.H_loopi, auto simp: p2r_def, (metis p2r_def rel_ref)+)

lemma euclid:
  "rel_hm.H \<lceil>\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y\<rceil>
   (while (\<lambda>s. s ''y'' \<noteq> 0) inv (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    do
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    od)
   \<lceil>\<lambda>s. s ''x'' = gcd x y\<rceil>"     
  apply (rule sH_whilei, simp_all, clarsimp simp: p2r_def, intro rel_hm.H_seq)
  apply (rule H_assign, auto)+
  using gcd_red_nat by auto

end
