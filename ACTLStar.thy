section \<open>Relation between ACTL* subset to the counterfactual Would Operator\<close>

theory ACTLStar

imports 
  GeneralOperators
  Main "HOL-Library.Omega_Words_Fun"
begin

context world_dependent_kripke_structure
begin

definition is_path :: \<open>'i \<Rightarrow> 'ap set word \<Rightarrow> bool\<close> 
  where \<open>is_path w \<pi> \<equiv> \<pi> 0 = ap(w) \<and> (\<forall> n. (\<exists> i1 i2. (i1 \<le><w> i2) \<and> (ap(i1) = \<pi> n) 
        \<and> (ap(i2) = \<pi> (Suc n))))\<close>

definition paths :: \<open>'i \<Rightarrow> 'ap set word set\<close>
  where \<open>paths w \<equiv> {\<pi>. is_path w \<pi>}\<close>

subsection \<open>Definition of a reduced ACTL* version\<close>

text \<open>This interpretation of ACTL* path formulas draws heavily on the LTL 
      formalisation done by Sickert and Seidel @{cite LTLAFP}.\<close>
datatype 'a ltlr =
  Prop_ltlr 'a                              ("prop\<^sub>r'(_')")
  | True_ltlr                               ("true\<^sub>r")
  | False_ltlr                              ("false\<^sub>r")
  | And_ltlr "'a ltlr" "'a ltlr"            ("_ and\<^sub>r _" [82,82] 81)
  | Implies_ltlr "'a ltlr" "'a ltlr"        ("_ implies\<^sub>r _" [81,81] 80)
  | Finally_ltlr "'a ltlr"                  ("F\<^sub>r _" [88] 87)
  | Until_ltlr "'a ltlr" "'a ltlr"          ("_ U\<^sub>r _" [84,84] 83)

datatype 'a actl_star =
  all_actl_star 'a                              ("A'(_')")
  | and_actl_star "'a actl_star" "'a actl_star" ("_ && _" [82,82] 81)
  | not_actl_star "'a actl_star"                ("~~ _" [88] 87)

primrec mc_ltlr :: \<open>'ap set word \<Rightarrow> 'ap ltlr \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>r _\<close> [80,80] 80) 
  where
    \<open>\<pi> \<Turnstile>\<^sub>r prop\<^sub>r(a) = (a \<in> \<pi> 0)\<close>
  | "\<pi> \<Turnstile>\<^sub>r true\<^sub>r = True"
  | "\<pi> \<Turnstile>\<^sub>r false\<^sub>r = False"
  | \<open>\<pi> \<Turnstile>\<^sub>r \<phi> and\<^sub>r \<psi> = (\<pi> \<Turnstile>\<^sub>r \<phi> \<and> \<pi> \<Turnstile>\<^sub>r \<psi>)\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r \<phi> implies\<^sub>r \<psi> = (\<pi> \<Turnstile>\<^sub>r \<phi> \<longrightarrow> \<pi> \<Turnstile>\<^sub>r \<psi>)\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r F\<^sub>r \<phi> = (\<exists>i. suffix i \<pi> \<Turnstile>\<^sub>r \<phi>)\<close> 
  | \<open>\<pi> \<Turnstile>\<^sub>r \<phi> U\<^sub>r \<psi> = (\<exists>i. suffix i \<pi> \<Turnstile>\<^sub>r \<psi> \<and> (\<forall>j<i. suffix j \<pi> \<Turnstile>\<^sub>r \<phi>))\<close>

primrec sem_actl_star :: \<open>'ap ltlr actl_star \<Rightarrow> 'i set\<close> (\<open>\<lbrakk> _ \<rbrakk>\<close> 80)  
  where 
    \<open>\<lbrakk> A(\<phi>) \<rbrakk> = {w. \<forall> \<pi>. is_path w \<pi> \<longrightarrow> \<pi> \<Turnstile>\<^sub>r \<phi>}\<close>
  | \<open>\<lbrakk> (~~ \<phi>) \<rbrakk> = UNIV - sem_actl_star \<phi>\<close>  
  | \<open>\<lbrakk> (\<phi> && \<psi>) \<rbrakk>= (sem_actl_star \<phi>) \<inter> (sem_actl_star \<psi>)\<close>

\<comment>\<open>The double negation elimination rule holds for our interpretation of ACTL*.\<close>
lemma actl_star_dne:
  fixes
    \<phi>_actl_star :: \<open>'ap ltlr actl_star\<close>
  shows 
    \<open>\<lbrakk>~~ (~~ \<phi>_actl_star)\<rbrakk> = \<lbrakk>\<phi>_actl_star\<rbrakk>\<close>
  by (simp add: Diff_Diff_Int)

end

subsection \<open>General Woulds semantics can not be expressed through ACTL*.\<close>

lemma (in preordered_counterfactual_structure) simplify_general_would:
  shows \<open>{w. (\<forall> w1. (w \<le><w> w1 \<and> w1 \<in> \<phi>) \<longrightarrow> 
          (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> (w3 \<in> UNIV - \<phi> \<union> \<psi>))))} = \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  using general_would_def by auto

datatype world = w_true | w_false | w1 | w2 | w3
datatype ap = \<phi> | \<psi>

text \<open>The following two functions describe a setting in which "if $\varphi$ would be the case, then 
      $\psi$ would be the case holds for $w_{true}$ but not for $w_{false}$. ACTL* is not able
      to distinguish between those two worlds.\<close>

fun count_access :: \<open>world \<Rightarrow> world \<Rightarrow> world \<Rightarrow> bool\<close> ("_ \<le><_> _" [70, 70, 70] 80) 
  where 
    \<open>count_access w_true _ w_true = True\<close>
  | \<open>count_access w_false _ w_false = True\<close>
  | \<open>count_access w1 _ w1 = True\<close>
  | \<open>count_access w2 _ w2 = True\<close>
  | \<open>count_access w3 _ w3 = True\<close>
  | \<open>count_access w_true w_true w1 = True\<close>
  | \<open>count_access w_true w_true w2 = True\<close>
  | \<open>count_access w_false w_false w1 = True\<close>
  | \<open>count_access w_false w_false w2 = True\<close>
  | \<open>count_access w_false w_false w3 = True\<close>
  | \<open>count_access w1 w_true w2 = True\<close>
  | \<open>count_access w1 w_false w2 = True\<close>
  | \<open>count_access w_true _ _ = False\<close>
  | \<open>count_access w_false _ _ = False\<close>
  | \<open>count_access w1 _ _ = False\<close>
  | \<open>count_access w2 _ _ = False\<close>
  | \<open>count_access w3 _ _ = False\<close>

primrec atomic_truth :: \<open>world \<Rightarrow> ap set\<close> (\<open>\<bullet>_\<close> [80])
  where 
    \<open>atomic_truth w_true = {}\<close>
  | \<open>atomic_truth w_false = {}\<close>
  | \<open>atomic_truth w1 = {\<phi>, \<psi>}\<close>
  | \<open>atomic_truth w2 = {\<phi>}\<close>
  | \<open>atomic_truth w3 = {\<phi>}\<close>

locale counterexample_actl_star =
  preordered_counterfactual_structure \<open>atomic_truth\<close> \<open>count_access\<close> 

begin

notation general_would (\<open>_ \<box>\<rightarrow>\<hungarumlaut> _\<close> [70, 70] 100)  
notation sem_actl_star  (\<open>\<lbrakk> _ \<rbrakk>\<close> 80)

\<comment>\<open>The key difference between $w_{true}$ and $w_{false}$. Facilitating \emph{metis} proofs.\<close>
lemma w3_not_accessible_from_w_true:
  shows \<open>w_true \<le><w_true> w3 \<Longrightarrow> False\<close>
  by auto 

subsection \<open>General Would can differentiate between $w_{true}$ and $w_{false}$.\<close>

lemma phi_semantics:
  shows \<open>{w. \<phi> \<in> \<bullet> w} = {w1, w2, w3}\<close>
proof 
  show \<open>{w. \<phi> \<in> \<bullet>w} \<subseteq> {w1, w2, w3}\<close>
  proof (rule ccontr)
    assume \<open>\<not> {w. \<phi> \<in> \<bullet>w} \<subseteq> {w1, w2, w3}\<close>
    hence \<open>w_true \<in> {w. \<phi> \<in> \<bullet>w} \<or> w_false \<in> {w. \<phi> \<in> \<bullet>w}\<close>
      by (auto, metis atomic_truth.simps(1) atomic_truth.simps(2) empty_iff world.exhaust)
    thus \<open>False\<close> by simp
  qed
next
  show \<open>{w1, w2, w3} \<subseteq> {w. \<phi> \<in> \<bullet>w}\<close> by simp
qed

lemma psi_semantics:
  shows \<open>{w. \<psi> \<in> \<bullet> w} = {w1}\<close>
proof
  show \<open>{w. \<psi> \<in> \<bullet>w} \<subseteq> {w1}\<close>
  proof (rule ccontr)
    assume \<open>\<not> {w. \<psi> \<in> \<bullet>w} \<subseteq> {w1}\<close>
    hence \<open>w_true \<in> {w. \<psi> \<in> \<bullet>w} \<or> w_false\<in> {w. \<psi> \<in> \<bullet>w} \<or> w2 \<in> {w. \<psi> \<in> \<bullet>w} \<or> w3 \<in> {w. \<psi> \<in> \<bullet>w}\<close>
      by (auto, metis ap.simps(2) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
          atomic_truth.simps(5) empty_iff singleton_iff world.exhaust)
    thus \<open>False\<close> by simp
  qed
next
  show \<open>{w1} \<subseteq> {w. \<psi> \<in> \<bullet>w}\<close>
    by simp
qed

lemma w_true_in_would_sem:
  shows \<open>w_true \<in> {w. \<phi> \<in> \<bullet> w} \<box>\<rightarrow>\<hungarumlaut> {w. \<psi> \<in> \<bullet> w}\<close>
proof - 
  have \<open>(\<forall> w1t. (w_true \<le><w_true> w1t \<and> w1t \<in> {w1,w2,w3}) \<longrightarrow> (\<exists> w2t. w2t \<le><w_true> w1t \<and> 
        w2t \<in> {w1,w2,w3} \<and> (\<forall> w3t. w3t \<le><w_true> w2t \<longrightarrow> (w3t \<in> UNIV - {w1,w2,w3} \<union> {w1}))))\<close> 
    by (metis (no_types, opaque_lifting) Diff_iff count_access.simps(11) count_access.simps(44) 
        emptyE inf_sup_aci(5) insert_iff insert_is_Un iso_tuple_UNIV_I local.reflexive 
        meaningful_acessibility w3_not_accessible_from_w_true)
  hence \<open>w_true \<in> {w. (\<forall> w1t. (w \<le><w> w1t \<and> w1t \<in> {w1,w2,w3}) \<longrightarrow> (\<exists> w2t. w2t \<le><w> w1t \<and> 
         w2t \<in> {w1,w2,w3} \<and> (\<forall> w3t. w3t \<le><w> w2t \<longrightarrow> (w3t \<in> UNIV - {w1,w2,w3} \<union> {w1}))))}\<close>
    by blast 
  thus \<open>w_true \<in> {w. \<phi> \<in> \<bullet> w}  \<box>\<rightarrow>\<hungarumlaut> {w. \<psi> \<in> \<bullet> w}\<close> 
    using simplify_general_would phi_semantics psi_semantics by metis
qed

lemma w_false_not_in_would_sem:
  shows \<open>w_false \<notin> {w. \<phi> \<in> \<bullet> w} \<box>\<rightarrow>\<hungarumlaut> {w. \<psi> \<in> \<bullet> w}\<close>
proof -
  have  \<open>\<not>(\<forall> w1t. (w_false \<le><w_false> w1t \<and> w1t \<in> {w1,w2,w3}) \<longrightarrow> 
         (\<exists> w2t. w2t \<le><w_false> w1t \<and> w2t \<in> {w1,w2,w3} \<and> 
         (\<forall> w3t. w3t \<le><w_false> w2t \<longrightarrow> (w3t \<in> UNIV - {w1,w2,w3} \<union> {w1}))))\<close>
    by (metis Diff_iff Un_iff count_access.simps(10) count_access.simps(41) 
        insertCI local.reflexive singleton_iff)
  hence \<open>w_false \<notin> {w. (\<forall> w1t. (w \<le><w> w1t \<and> w1t \<in> {w1,w2,w3}) \<longrightarrow> 
         (\<exists> w2t. w2t \<le><w> w1t \<and> w2t \<in> {w1,w2,w3} \<and> (\<forall> w3t. w3t \<le><w> w2t \<longrightarrow> 
         (w3t \<in> UNIV - {w1,w2,w3} \<union> {w1}))))}\<close> by blast
  thus \<open>w_false \<notin> {w. \<phi> \<in> \<bullet> w}  \<box>\<rightarrow>\<hungarumlaut> {w. \<psi> \<in> \<bullet> w}\<close> 
    using simplify_general_would phi_semantics psi_semantics by metis
qed

subsection \<open>Paths for $w_{true}$ and $w_{false}$ equal.\<close>

lemma no_single_psi_world:
  shows \<open>\<forall> i1. \<bullet> i1 \<noteq> {\<psi>}\<close> 
  by (metis ap.simps(2) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
      atomic_truth.simps(4) atomic_truth.simps(5) insert_not_empty 
      singleton_insert_inj_eq world.exhaust)

lemma phi_only_phi_suc_on_path:
  assumes 
    path: \<open>is_path w_true \<pi>\<close> and
    nth_place_phi: \<open>\<pi> n = {\<phi>}\<close>
  shows \<open>\<pi> (Suc n) = {\<phi>}\<close> 
proof (rule ccontr)
  assume \<open>\<pi> (Suc n) \<noteq> {\<phi>}\<close>
  from this path nth_place_phi have non_phi_suc:\<open>\<exists> i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = {\<phi>} \<and> \<bullet>i2 \<noteq> {\<phi>}\<close> 
    by (metis is_path_def)
  hence \<open>\<exists> i1. w2 \<le><w_true> i1 \<and> \<bullet> i1 \<noteq> {\<phi>}\<close> using atomic_truth.simps(4) 
    by (metis atomic_truth.simps(1) atomic_truth.simps(2) count_access.simps(36) 
        count_access.simps(37) empty_not_insert meaningful_acessibility 
        w3_not_accessible_from_w_true world.exhaust)
  thus \<open>False\<close> 
    by (metis atomic_truth.simps(4) atomic_truth.simps(5) count_access.simps(42) 
        count_access.simps(43) count_access.simps(44) world.exhaust)
qed

lemma phi_psi_only_phy_psi_or_phi_suc:
  assumes 
    path: \<open>is_path w_true \<pi>\<close> and
    nth_place_phi_psi: \<open>\<pi> n = {\<phi>, \<psi>}\<close>
  shows
     \<open>\<pi> (Suc n) = {\<phi>,\<psi>} \<or> \<pi> (Suc n) = {\<phi>}\<close>
proof (rule ccontr)
  assume cont_assm: \<open>\<not> (\<pi> (Suc n) = {\<phi>, \<psi>} \<or> \<pi> (Suc n) = {\<phi>})\<close>
  from this path nth_place_phi_psi have non_phi_suc: 
    \<open>\<exists> i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = {\<phi>, \<psi>} \<and> \<bullet>i2 \<noteq> {\<phi>, \<psi>} \<and> \<bullet>i2 \<noteq> {\<phi>}\<close> by (metis is_path_def)
  have \<open>\<exists> i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = {\<phi>, \<psi>} \<longrightarrow> i1 = w1\<close> by blast
  hence \<open>\<exists> i1. w1 \<le><w_true> i1 \<and> \<bullet>i1 \<noteq>  {\<phi>, \<psi>} \<and> \<bullet>i1 \<noteq>  {\<phi>}\<close> 
    by (metis cont_assm atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
        atomic_truth.simps(4) atomic_truth.simps(5) non_phi_suc nth_place_phi_psi 
        path phi_only_phi_suc_on_path world.exhaust)
  thus \<open>False\<close> 
    by (metis atomic_truth.simps(3) atomic_truth.simps(4) atomic_truth.simps(5) 
        count_access.simps(36) count_access.simps(37) world.exhaust)
qed

lemma after_start_eq_forth:
  assumes
    \<open>\<pi> 0 = \<bullet>w_true \<and>  \<pi> 0 = \<bullet>w_false\<close>
  shows
    \<open>(\<forall>n. \<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)) \<Longrightarrow>
     (\<forall>n. \<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n))\<close>
proof 
  assume is_w_true_path: \<open>\<forall>n. \<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)\<close>
  fix m
  show \<open>\<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
  proof (induct m)
    case 0
    then show ?case 
      by (metis (full_types) is_w_true_path assms reflexive count_access.simps(10) 
          count_access.simps(8) count_access.simps(9) world.exhaust)
  next
    case (Suc m)
    assume \<open>\<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
    then obtain i1 i2 where fixed_i1_i2:\<open>i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close> by blast
    have \<open>\<bullet> i2 = {} \<or> \<bullet> i2 = {\<phi>} \<or> \<bullet> i2 = {\<phi>, \<psi>}\<close> 
      by (metis atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
          atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
    then show ?case
    proof 
      assume \<open>\<bullet>i2 = {}\<close> 
      from this is_w_true_path have 
        \<open>\<pi> (Suc (Suc m)) = {} \<or> \<pi> (Suc (Suc m)) = {\<phi>} \<or> \<pi> (Suc (Suc m)) = {\<phi>, \<psi>}\<close> 
        by (metis (full_types) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
            atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
      then show \<open>\<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close> 
        by (metis \<open>\<bullet>i2 = {}\<close> fixed_i1_i2 atomic_truth.simps(2) atomic_truth.simps(3) 
            atomic_truth.simps(5) count_access.simps(10) count_access.simps(8) 
            meaningful_acessibility)
    next
      assume phi_or_phi_and_psi: \<open>\<bullet>i2 = {\<phi>} \<or> \<bullet>i2 = {\<phi>, \<psi>}\<close>
      show \<open>\<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m)) \<close>
      proof (cases \<open>\<bullet>i2 = {\<phi>}\<close>)
        case True
        have nth_place_phi: \<open>\<pi> (Suc m) = {\<phi>}\<close> using True fixed_i1_i2 by auto
        from this is_w_true_path phi_only_phi_suc_on_path have \<open>\<pi> (Suc (Suc m)) = {\<phi>}\<close> 
          using assms is_path_def by presburger
        then show ?thesis using Suc nth_place_phi by auto
      next
        case False
        from this phi_or_phi_and_psi have \<open>\<bullet>i2 = {\<phi>,\<psi>}\<close> by blast
        have nth_place_phi_psi: \<open>\<pi> (Suc m) = {\<phi>, \<psi>}\<close> 
          using \<open>\<bullet>i2 = {\<phi>, \<psi>}\<close> fixed_i1_i2 by auto
        from this is_w_true_path phi_psi_only_phy_psi_or_phi_suc have  
          \<open>\<pi> (Suc (Suc m)) = {\<phi>, \<psi>} \<or>\<pi> (Suc (Suc m)) = {\<phi>}\<close> using assms is_path_def by presburger
        then show ?thesis by (metis atomic_truth.simps(3) atomic_truth.simps(4) 
                              count_access.simps(12) local.reflexive nth_place_phi_psi)
      qed
    qed
  qed
qed  

lemma phi_only_phi_suc_on_path_w_false:
  assumes 
    path: \<open>is_path w_false \<pi>\<close> and
    nth_place_phi: \<open>\<pi> n = {\<phi>}\<close>
  shows \<open>\<pi> (Suc n) = {\<phi>}\<close> 
proof (rule ccontr)
  assume \<open>\<pi> (Suc n) \<noteq> {\<phi>}\<close>
  from this path nth_place_phi have non_phi_suc:
    \<open>\<exists> i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = {\<phi>} \<and> \<bullet>i2 \<noteq> {\<phi>}\<close> by (metis is_path_def)
  hence \<open>\<exists> i1. w2 \<le><w_false> i1 \<and> \<bullet> i1 \<noteq> {\<phi>}\<close> 
    by (metis atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
        atomic_truth.simps(5) count_access.simps(36) count_access.simps(37) count_access.simps(46) 
        count_access.simps(47) count_access.simps(48) insert_not_empty world.exhaust)
  thus \<open>False\<close> 
    by (metis atomic_truth.simps(4) atomic_truth.simps(5) count_access.simps(42) 
        count_access.simps(43) count_access.simps(44) world.exhaust)
qed

lemma phi_psi_only_phy_psi_or_phi_suc_w_false:
  assumes 
    path: \<open>is_path w_false \<pi>\<close> and
    nth_place_phi_psi: \<open>\<pi> n = {\<phi>, \<psi>}\<close>
  shows
     \<open>\<pi> (Suc n) = {\<phi>,\<psi>} \<or> \<pi> (Suc n) = {\<phi>}\<close>
proof (rule ccontr)
  assume contr_assm: \<open>\<not> (\<pi> (Suc n) = {\<phi>, \<psi>} \<or> \<pi> (Suc n) = {\<phi>})\<close>
  from this path nth_place_phi_psi have non_phi_suc: 
    \<open>\<exists> i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = {\<phi>, \<psi>} \<and> \<bullet>i2 \<noteq> {\<phi>, \<psi>} \<and> \<bullet>i2 \<noteq> {\<phi>}\<close> unfolding is_path_def 
    by metis
  hence \<open>\<exists> i1. w1 \<le><w_true> i1 \<and> \<bullet>i1 \<noteq>  {\<phi>, \<psi>} \<and> \<bullet>i1 \<noteq>  {\<phi>}\<close>  
    by (metis contr_assm atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
        atomic_truth.simps(5) count_access.simps(36) count_access.simps(37) insert_not_empty 
        nth_place_phi_psi path phi_only_phi_suc_on_path_w_false world.exhaust)
  thus \<open>False\<close> by (metis atomic_truth.simps(3) atomic_truth.simps(4) atomic_truth.simps(5) 
                   count_access.simps(36) count_access.simps(37) world.exhaust)
qed

lemma after_start_eq_back:
  assumes
    \<open>\<pi> 0 = \<bullet>w_true \<and>  \<pi> 0 = \<bullet>w_false\<close>
  shows
    \<open>(\<forall>n. \<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)) \<Longrightarrow>
     (\<forall>n. \<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n))\<close>
proof
  assume is_w_false_path: \<open>\<forall>n. \<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)\<close>
  fix m
  show \<open>\<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
  proof (induct m)
    case 0 
    from is_w_false_path have \<open>\<pi> 0 = {}\<close> by (simp add: assms)
    then show ?case 
      by (metis (no_types, opaque_lifting) atomic_truth.simps(1) atomic_truth.simps(2) 
          atomic_truth.simps(4) atomic_truth.simps(5) count_access.simps(6) count_access.simps(7) 
          is_w_false_path local.reflexive world.exhaust)
    case (Suc m)
    assume \<open>\<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
    then obtain i1 i2 where fixed_i1_i2: \<open>i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close> by blast
    from is_w_false_path have \<open>\<bullet> i2 = {} \<or> \<bullet> i2 = {\<phi>} \<or> \<bullet> i2 = {\<phi>, \<psi>}\<close>  
      by (metis atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
          atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
    from this show ?case  
    proof 
      assume \<open>\<bullet>i2 = {}\<close>
      from this is_w_false_path have 
        \<open>\<pi> (Suc (Suc m)) = {} \<or> \<pi> (Suc (Suc m)) = {\<phi>} \<or> \<pi> (Suc (Suc m)) = {\<phi>, \<psi>}\<close> 
        by (metis (full_types) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
            atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
      then show \<open>\<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close> 
        by (metis \<open>\<bullet>i2 = {}\<close> fixed_i1_i2 atomic_truth.simps(1) atomic_truth.simps(3) 
            atomic_truth.simps(4) count_access.simps(6) count_access.simps(7) 
            world_dependent_kripke_structure_axioms world_dependent_kripke_structure_def)
     next
       assume phi_or_phi_and_psi: \<open>\<bullet>i2 = {\<phi>} \<or> \<bullet>i2 = {\<phi>, \<psi>}\<close>
       show \<open>\<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close>
       proof (cases \<open>\<bullet>i2 = {\<phi>}\<close>)
         case True
         have nth_place_phi: \<open>\<pi> (Suc m) = {\<phi>}\<close> 
           using True fixed_i1_i2 by auto
         from this is_w_false_path have \<open>\<pi> (Suc (Suc m)) = {\<phi>}\<close> using assms is_path_def 
           using phi_only_phi_suc_on_path_w_false by auto
         then show \<open>\<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close> 
           using atomic_truth.simps(4) nth_place_phi by blast
       next
         case False
         from this phi_or_phi_and_psi have \<open>\<bullet>i2 = {\<phi>,\<psi>}\<close> by blast
         have nth_place_phi_psi: \<open>\<pi> (Suc m) = {\<phi>, \<psi>}\<close> 
           using \<open>\<bullet>i2 = {\<phi>, \<psi>}\<close> fixed_i1_i2 by auto
         from this is_w_false_path phi_psi_only_phy_psi_or_phi_suc_w_false have 
           \<open>\<pi> (Suc (Suc m)) = {\<phi>, \<psi>} \<or>\<pi> (Suc (Suc m)) = {\<phi>}\<close> using assms is_path_def by simp
         then show ?thesis 
           by (metis atomic_truth.simps(3) atomic_truth.simps(4) count_access.simps(11) 
               nth_place_phi_psi reflexive)
       qed 
     qed
  qed
qed

lemma w_false_path_iff_w_true_path:
  shows \<open>is_path w_false \<pi> \<longleftrightarrow> is_path w_true \<pi>\<close>
proof (unfold is_path_def)
  have same_start: \<open>\<pi> 0 = \<bullet>w_false \<longleftrightarrow> \<pi> 0 = \<bullet>w_true\<close> by simp
  then show \<open>\<pi> 0 = \<bullet>w_false \<and> (\<forall>n. \<exists>i1 i2. i1 \<le><w_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)) \<longleftrightarrow>
             \<pi> 0 = \<bullet>w_true \<and> (\<forall>n. \<exists>i1 i2. i1 \<le><w_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n))\<close>
  using after_start_eq_forth after_start_eq_back by auto
qed
  
lemma w_true_and_w_false_paths_eq:
  shows \<open>paths w_true = paths w_false\<close> 
  using w_false_path_iff_w_true_path paths_def by auto

subsection \<open>ACTL* can not distinguish between $w_{true}$ and $w_{false}$\<close>

definition existing_path :: \<open>ap set word\<close>
  where \<open>existing_path _ = {}\<close>

lemma existst_path_true_at_w_true_and_w_false:
  shows \<open>\<exists> \<pi>. is_path w_true \<pi> \<and> is_path w_false \<pi>\<close>
proof
  show \<open>is_path w_true existing_path \<and> is_path w_false existing_path\<close>
    by (metis atomic_truth.simps(1) atomic_truth.simps(2) existing_path_def is_path_def reflexive)
qed

lemma ltlr_only_distiguishing_differnt_paths:
  fixes 
    ltlr_formula :: \<open>ap ltlr\<close> and
    \<pi> \<rho> :: \<open>ap set word\<close>
  shows \<open>\<pi> \<Turnstile>\<^sub>r ltlr_formula \<and> \<not> (\<rho> \<Turnstile>\<^sub>r ltlr_formula) \<Longrightarrow> \<pi> \<noteq> \<rho>\<close> by auto

lemma paths_eq_all_paths_truth_eq:
  assumes
    \<open>\<exists> \<pi>. is_path w1t \<pi> \<and> is_path w2t \<pi>\<close> and
    \<open>paths w1t = paths w2t\<close>
  shows
    \<open>w1t \<in> \<lbrakk> A(ltlr_formula) \<rbrakk> \<Longrightarrow> w2t \<in> \<lbrakk>  A(ltlr_formula) \<rbrakk>\<close>
proof (rule ccontr)
  assume \<open>w1t \<in> \<lbrakk> A(ltlr_formula) \<rbrakk>\<close>
  hence all_paths_true: \<open>\<forall> \<pi>. is_path w1t \<pi> \<longrightarrow> \<pi> \<Turnstile>\<^sub>r ltlr_formula\<close> by simp
  assume \<open>w2t \<notin> \<lbrakk> A(ltlr_formula) \<rbrakk>\<close>  
  hence \<open>\<exists> \<pi>. is_path w2t \<pi> \<and> \<not> \<pi> \<Turnstile>\<^sub>r ltlr_formula\<close> by simp
  thus \<open>False\<close> using all_paths_true assms(2) paths_def by auto
qed

lemma paths_eq_means_non_distiguishable:
  fixes
    actl_star_formula :: \<open>ap ltlr actl_star\<close>
  shows \<open>w_true \<in> \<lbrakk> actl_star_formula \<rbrakk> \<longleftrightarrow>  w_false \<in> \<lbrakk> actl_star_formula \<rbrakk>\<close>
proof (induct rule: actl_star.induct)
  case (all_actl_star x)
  show ?case 
    using existst_path_true_at_w_true_and_w_false paths_eq_all_paths_truth_eq 
      w_true_and_w_false_paths_eq by blast
next
  case (and_actl_star x1a x2)
  then show ?case by simp
next
  case (not_actl_star x)
  then show ?case by simp
qed

subsection \<open>General Woulds semantics can not be mapped to ACTL*\<close>

lemma general_would_not_in_actl_star:
  fixes
    actl_star_formula :: \<open>ap ltlr actl_star\<close>
  shows \<open>{w. \<phi> \<in> \<bullet> w} \<box>\<rightarrow>\<hungarumlaut> {w. \<psi> \<in> \<bullet> w} \<noteq> \<lbrakk> actl_star_formula \<rbrakk>\<close>
proof (rule ccontr)
  assume semantics_eq: \<open>\<not> {w. \<phi> \<in> \<bullet>w} \<box>\<rightarrow>\<hungarumlaut> {w. \<psi> \<in> \<bullet>w} \<noteq> \<lbrakk> actl_star_formula \<rbrakk>\<close>
  hence w_true_in_semantics:\<open>w_true \<in> \<lbrakk> actl_star_formula \<rbrakk>\<close> using w_true_in_would_sem by blast
  from semantics_eq have \<open>w_false \<notin> \<lbrakk> actl_star_formula \<rbrakk>\<close> using w_false_not_in_would_sem 
    by fastforce 
  then show \<open>False\<close> using w_true_in_semantics paths_eq_means_non_distiguishable by auto
qed

end
end