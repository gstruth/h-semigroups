(*section {* Verification Component Based on Bi-Semigroups *}*)

theory R_Semigroup
  imports H_Semigroup

begin

class R_monoid = H_monoid +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes star_iso: "x \<preceq> y \<Longrightarrow> x\<^sup>\<star> \<preceq> y\<^sup>\<star>"
  and R1: "H p (R p q) q"
  and R2: "H p x q \<Longrightarrow> x \<preceq> R p q"

begin

lemma R_skip: "p \<preceq> q \<Longrightarrow> 1 \<preceq> R p q"
  by (simp add: H_def R2)

lemma R_cons: "p \<preceq> p' \<Longrightarrow> q' \<preceq> q \<Longrightarrow> R p' q' \<preceq> R p q"
  using H_cons R1 R2 by blast

lemma R_seq: "(R p r) \<cdot> (R r q) \<preceq> R p q"
  using H_seq R1 R2 by blast

lemma R_loop: "H p q (p \<cdot> q) \<Longrightarrow> H p r (p \<cdot> r) \<Longrightarrow> (q \<cdot> R (p \<cdot> q) p)\<^sup>\<star> \<cdot> r \<preceq> R p (p \<cdot> r)"
  by (simp add: H_loopi R1 R2 preo_refl)

lemma R_cond: 
assumes "\<And>x y. p \<cdot> (x + y) \<preceq> p \<cdot> x + p \<cdot> y" and "\<And>x y. x \<cdot> q + y \<cdot> q \<preceq> (x + y) \<cdot> q"
shows "H p v (p \<cdot> v) \<Longrightarrow> H p w (p \<cdot> w) \<Longrightarrow> v \<cdot> R (p \<cdot> v) q + w \<cdot> R (p \<cdot> w) q \<preceq> R p q"
  by (simp add: assms H_cond R1 R2)

end

definition "rel_R P Q = \<Union>{X. rel_hm.H P X Q}"

interpretation rel_rm: R_monoid Id "op ;" "op \<union>" "op \<subseteq>" rtrancl rel_R
  by (standard, auto simp: rtrancl_mono rel_R_def rel_hm.H_def, blast)

lemma R_assign: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (simp add: H_assign rel_rm.R2)

lemma R_assignr: "(\<forall>s. Q' s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (rel_R \<lceil>P\<rceil> \<lceil>Q'\<rceil>) ; (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (metis H_assign rel_hm.H_seq rel_rm.R1 rel_rm.R2)

lemma R_assignl: "(\<forall>s. P s \<longrightarrow> P' (s (v := e s))) \<Longrightarrow> (v ::= e) ; (rel_R \<lceil>P'\<rceil> \<lceil>Q\<rceil>) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (metis H_assign rel_hm.H_seq rel_rm.R1 rel_rm.R2)

lemma if_then_else_ref: "X \<subseteq> X' \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow> if P then X else Y fi \<subseteq> if P then X' else Y' fi"
  by (auto simp: if_then_else_def)
                                     
lemma while_ref: "X \<subseteq> X' \<Longrightarrow> (while P do X od) \<subseteq> (while P do X' od)"
  by (simp add: while_def rel_hm.mult_isol rel_hm.mult_isor rel_rm.star_iso)

lemma euclid1: "rel_R \<lceil>\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y\<rceil> \<lceil>\<lambda>s. s ''x'' = gcd x y\<rceil>
   \<supseteq> rel_R \<lceil>\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y\<rceil> \<lceil>\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y \<and> \<not> s ''y'' \<noteq> 0\<rceil>"
  by (intro rel_rm.R_cons, auto simp: p2r_def)

abbreviation "P x y \<equiv> \<lceil>\<lambda>s::nat store. gcd (s ''x'') (s ''y'') = gcd x y \<and> s ''y'' \<noteq> 0\<rceil>"

lemma euclid2: "rel_R \<lceil>\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y\<rceil> \<lceil>\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y \<and> \<not> s ''y'' \<noteq> 0\<rceil>
    \<supseteq> while (\<lambda>s. s ''y'' \<noteq> 0) do rel_R (P x y) \<lceil>\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y\<rceil> od"
  apply (simp only: while_def p2r_mult_hom[symmetric]) by (intro rel_rm.R_loop, auto simp: p2r_def rel_hm.H_def)

lemma euclid3: "rel_R (P x y) \<lceil>\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y\<rceil> 
    \<supseteq> rel_R (P x y) \<lceil>\<lambda>s. gcd (s ''z'') (s ''y'') = gcd x y\<rceil> ; (''x'' ::= (\<lambda>s. s ''z''))"
  by (intro R_assignr, simp)

lemma euclid4: "rel_R (P x y) \<lceil>\<lambda>s. gcd (s ''z'') (s ''y'') = gcd x y\<rceil>
    \<supseteq> rel_R (P x y) \<lceil>\<lambda>s. gcd (s ''z'') (s ''x'' mod s ''y'') = gcd x y\<rceil> ; (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''))"
  by (intro R_assignr, simp)

lemma euclid5: "rel_R (P x y) \<lceil>\<lambda>s. gcd (s ''z'') (s ''x'' mod s ''y'') = gcd x y\<rceil>
    \<supseteq> (''z'' ::= (\<lambda>s. s ''y''))"
  by (intro R_assign, auto simp: gcd_non_0_nat)

lemma euclid_ref: "rel_R \<lceil>\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y\<rceil> \<lceil>\<lambda>s. s ''x'' = gcd x y\<rceil>
    \<supseteq> 
  while (\<lambda>s. s ''y'' \<noteq> 0)
    do 
      (''z'' ::= (\<lambda>s. s ''y'')); 
      (''y'' ::= (\<lambda>s. s ''x'' mod s ''y'')); 
      (''x'' ::= (\<lambda>s. s ''z'')) 
    od"
  apply (rule dual_order.trans, subst euclid1, simp, rule dual_order.trans, subst euclid2, simp)
  apply (intro while_ref) using euclid3 euclid4 euclid5 by fast

end

