section \<open>Relation of CTL* to the counterfactual Would Operator\<close>

theory CTLStar

imports 
  GeneralOperators
  Main "HOL-Library.Omega_Words_Fun"
begin

context world_dependant_kripke_structure begin

subsection \<open>Definition of a reduced CTL* version\<close>

text \<open>We give a formalisation of a reduced version of the logic CTL* described by Emerson, Allen and 
      Halpern @{cite Emerson1983}. The existential quantifier over paths  can be substituted by a 
      negated quantifier over all paths leaving us with the Logic CTL*. 
      Our interpretation of CTL* path formulas is taken from the LTL formalisation done by Sickert 
      and Seidel @{cite LTLAFP}.\<close>

definition is_path :: \<open>'i \<Rightarrow> 'ap set word \<Rightarrow> bool\<close> 
  where \<open>is_path w \<pi> \<equiv> \<pi> 0 = ap(w) \<and> (\<forall> n. (\<exists> i1 i2. (i1 \<le><w> i2) \<and> (ap(i1) = \<pi> n) 
        \<and> (ap(i2) = \<pi> (Suc n))))\<close>

definition paths :: \<open>'i \<Rightarrow> 'ap set word set\<close>
  where \<open>paths w \<equiv> {\<pi>. is_path w \<pi>}\<close>

\<comment>\<open>We can abstract from concrete semantics of the path formulas in later proofs. Hence a reduced
  implementation is sufficient.\<close>
datatype 'a ltlr =
  Prop_ltlr 'a                              (\<open>prop\<^sub>r'(_')\<close>)
  | True_ltlr                               (\<open>true\<^sub>r\<close>)
  | False_ltlr                              (\<open>false\<^sub>r\<close>)
  | And_ltlr  \<open>'a ltlr\<close> \<open>'a ltlr\<close>           (\<open>_ and\<^sub>r _\<close> [82,82] 81)
  | Implies_ltlr \<open>'a ltlr\<close> \<open>'a ltlr\<close>        (\<open>_ implies\<^sub>r _\<close> [81,81] 80)
  | Finally_ltlr \<open>'a ltlr\<close>                  (\<open>F\<^sub>r _\<close> [88] 87)
  | Until_ltlr \<open>'a ltlr\<close> \<open>'a ltlr\<close>          (\<open>_ U\<^sub>r _\<close> [84,84] 83)

datatype 'a ctl_star =
  all_ctl_star 'a                              (\<open>A'(_')\<close>)
  | and_ctl_star \<open>'a ctl_star\<close> \<open>'a ctl_star\<close> (\<open>_ && _\<close> [82,82] 81)
  | not_ctl_star \<open>'a ctl_star\<close>                (\<open>~~ _\<close> [88] 87)

primrec mc_ltlr :: \<open>'ap set word \<Rightarrow> 'ap ltlr \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>r _\<close> [80,80] 80) 
  where
    \<open>\<pi> \<Turnstile>\<^sub>r prop\<^sub>r(a) = (a \<in> \<pi> 0)\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r true\<^sub>r = True\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r false\<^sub>r = False\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r Phi and\<^sub>r Psi = (\<pi> \<Turnstile>\<^sub>r Phi \<and> \<pi> \<Turnstile>\<^sub>r Psi)\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r Phi implies\<^sub>r Psi = (\<pi> \<Turnstile>\<^sub>r Phi \<longrightarrow> \<pi> \<Turnstile>\<^sub>r Psi)\<close>
  | \<open>\<pi> \<Turnstile>\<^sub>r F\<^sub>r Phi = (\<exists>i. suffix i \<pi> \<Turnstile>\<^sub>r Phi)\<close> 
  | \<open>\<pi> \<Turnstile>\<^sub>r Phi U\<^sub>r Psi = (\<exists>i. suffix i \<pi> \<Turnstile>\<^sub>r Psi \<and> (\<forall>j<i. suffix j \<pi> \<Turnstile>\<^sub>r Phi))\<close>

primrec sem_ctl_star :: \<open>'ap ltlr ctl_star \<Rightarrow> 'i set\<close> (\<open>\<lbrakk> _ \<rbrakk>\<close> 80)  
  where 
    \<open>\<lbrakk> A(Phi) \<rbrakk> = {w. \<forall> \<pi>. is_path w \<pi> \<longrightarrow> \<pi> \<Turnstile>\<^sub>r Phi}\<close>
  | \<open>\<lbrakk> (~~ Phi) \<rbrakk> = UNIV - sem_ctl_star Phi\<close>  
  | \<open>\<lbrakk> (Phi && Psi) \<rbrakk>= (sem_ctl_star Phi) \<inter> (sem_ctl_star Psi)\<close>

\<comment>\<open>The double negation elimination rule holds for our interpretation of CTL*.\<close>
lemma ctl_star_dne:
  fixes
    Phi_ctl_star :: \<open>'ap ltlr ctl_star\<close>
  shows 
    \<open>\<lbrakk>~~ (~~ Phi_ctl_star)\<rbrakk> = \<lbrakk>Phi_ctl_star\<rbrakk>\<close>
  by (simp add: Diff_Diff_Int)

end

\<comment>\<open>Preliminary work to simplify evaluation of \emph{General Woulds} semantics.\<close>
lemma (in preordered_counterfactual_structure) simplify_general_would:
  shows \<open>{w. (\<forall> W1. (w \<le><w> W1 \<and> W1 \<in> Phi) \<longrightarrow> 
          (\<exists> W2. W2 \<le><w> W1 \<and> W2 \<in> Phi \<and> (\<forall> W3. W3 \<le><w> W2 \<longrightarrow> (W3 \<in> UNIV - Phi \<union> Psi))))} = Phi \<box>\<rightarrow>\<hungarumlaut> Psi\<close>
  using general_would_def by auto

datatype world = W_true | W_false | W1 | W2 | W3
datatype ap = Phi | Psi

text \<open>The following two functions describe a setting in which "if $\varphi$ would be the case, then
      $\psi$ would be the case holds for $w_{true}$ but not for $w_{false}$. CTL* is not able
      to distinguish between those two worlds.\<close>

fun count_access :: \<open>world \<Rightarrow> world \<Rightarrow> world \<Rightarrow> bool\<close> (\<open>_ \<le><_> _\<close> [70, 70, 70] 80) 
  where 
    \<open>count_access W_true _ W_true = True\<close>
  | \<open>count_access W_false _ W_false = True\<close>
  | \<open>count_access W1 _ W1 = True\<close>
  | \<open>count_access W2 _ W2 = True\<close>
  | \<open>count_access W3 _ W3 = True\<close>
  | \<open>count_access W_true W_true W1 = True\<close>
  | \<open>count_access W_true W_true W2 = True\<close>
  | \<open>count_access W_false W_false W1 = True\<close>
  | \<open>count_access W_false W_false W2 = True\<close>
  | \<open>count_access W_false W_false W3 = True\<close>
  | \<open>count_access W1 W_true W2 = True\<close>
  | \<open>count_access W1 W_false W2 = True\<close>
  | \<open>count_access W_true _ _ = False\<close>
  | \<open>count_access W_false _ _ = False\<close>
  | \<open>count_access W1 _ _ = False\<close>
  | \<open>count_access W2 _ _ = False\<close>
  | \<open>count_access W3 _ _ = False\<close>

primrec atomic_truth :: \<open>world \<Rightarrow> ap set\<close> (\<open>\<bullet>_\<close> [80])
  where 
    \<open>atomic_truth W_true = {}\<close>
  | \<open>atomic_truth W_false = {}\<close>
  | \<open>atomic_truth W1 = {Phi, Psi}\<close>
  | \<open>atomic_truth W2 = {Phi}\<close>
  | \<open>atomic_truth W3 = {Phi}\<close>

locale counterexample_ctl_star =
  preordered_counterfactual_structure \<open>atomic_truth\<close> \<open>count_access\<close> begin

notation general_would (\<open>_ \<box>\<rightarrow>\<hungarumlaut> _\<close> [70, 70] 100)  
notation sem_ctl_star  (\<open>\<lbrakk> _ \<rbrakk>\<close> 80)

\<comment>\<open>The key difference between $w_{true}$ and $w_{false}$. Facilitating \emph{metis} proofs.\<close>
lemma W3_not_accessible_from_W_true:
  shows \<open>W_true \<le><W_true> W3 \<Longrightarrow> False\<close>
  by auto 

subsection \<open>General Would can differentiate between $w_{true}$ and $w_{false}$.\<close>

lemma phi_semantics:
  shows \<open>{w. Phi \<in> \<bullet> w} = {W1, W2, W3}\<close>
proof 
  show \<open>{w. Phi \<in> \<bullet>w} \<subseteq> {W1, W2, W3}\<close>
  proof (rule ccontr)
    assume \<open>\<not> {w. Phi \<in> \<bullet>w} \<subseteq> {W1, W2, W3}\<close>
    hence \<open>W_true \<in> {w. Phi \<in> \<bullet>w} \<or> W_false \<in> {w. Phi \<in> \<bullet>w}\<close>
      by (auto, metis atomic_truth.simps(1) atomic_truth.simps(2) empty_iff world.exhaust)
    thus \<open>False\<close> by simp
  qed
next
  show \<open>{W1, W2, W3} \<subseteq> {w. Phi \<in> \<bullet>w}\<close> by simp
qed

lemma psi_semantics:
  shows \<open>{w. Psi \<in> \<bullet> w} = {W1}\<close>
proof
  show \<open>{w. Psi \<in> \<bullet>w} \<subseteq> {W1}\<close>
  proof (rule ccontr)
    assume \<open>\<not> {w. Psi \<in> \<bullet>w} \<subseteq> {W1}\<close>
    hence \<open>W_true \<in> {w. Psi \<in> \<bullet>w} \<or> W_false\<in> {w. Psi \<in> \<bullet>w} \<or> W2 \<in> {w. Psi \<in> \<bullet>w} \<or> W3 \<in> {w. Psi \<in> \<bullet>w}\<close>
      by (auto, metis ap.simps(2) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
          atomic_truth.simps(5) empty_iff singleton_iff world.exhaust)
    thus \<open>False\<close> by simp
  qed
next
  show \<open>{W1} \<subseteq> {w. Psi \<in> \<bullet>w}\<close>
    by simp
qed

lemma W_true_in_would_sem:
  shows \<open>W_true \<in> {w. Phi \<in> \<bullet> w} \<box>\<rightarrow>\<hungarumlaut> {w. Psi \<in> \<bullet> w}\<close>
proof - 
  have \<open>(\<forall> W1t. (W_true \<le><W_true> W1t \<and> W1t \<in> {W1,W2,W3}) \<longrightarrow> (\<exists> W2t. W2t \<le><W_true> W1t \<and> 
        W2t \<in> {W1,W2,W3} \<and> (\<forall> W3t. W3t \<le><W_true> W2t \<longrightarrow> (W3t \<in> UNIV - {W1,W2,W3} \<union> {W1}))))\<close> 
    by (metis (no_types, opaque_lifting) Diff_iff count_access.simps(11) count_access.simps(44) 
        emptyE inf_sup_aci(5) insert_iff insert_is_Un iso_tuple_UNIV_I local.reflexive 
        meaningful_acessibility W3_not_accessible_from_W_true)
  hence \<open>W_true \<in> {w. (\<forall> W1t. (w \<le><w> W1t \<and> W1t \<in> {W1,W2,W3}) \<longrightarrow> (\<exists> W2t. W2t \<le><w> W1t \<and> 
         W2t \<in> {W1,W2,W3} \<and> (\<forall> W3t. W3t \<le><w> W2t \<longrightarrow> (W3t \<in> UNIV - {W1,W2,W3} \<union> {W1}))))}\<close>
    by blast 
  thus \<open>W_true \<in> {w. Phi \<in> \<bullet> w}  \<box>\<rightarrow>\<hungarumlaut> {w. Psi \<in> \<bullet> w}\<close> 
    using simplify_general_would phi_semantics psi_semantics by metis
qed

lemma W_false_not_in_would_sem:
  shows \<open>W_false \<notin> {w. Phi \<in> \<bullet> w} \<box>\<rightarrow>\<hungarumlaut> {w. Psi \<in> \<bullet> w}\<close>
proof -
  have  \<open>\<not>(\<forall> W1t. (W_false \<le><W_false> W1t \<and> W1t \<in> {W1,W2,W3}) \<longrightarrow> 
         (\<exists> W2t. W2t \<le><W_false> W1t \<and> W2t \<in> {W1,W2,W3} \<and> 
         (\<forall> W3t. W3t \<le><W_false> W2t \<longrightarrow> (W3t \<in> UNIV - {W1,W2,W3} \<union> {W1}))))\<close>
    by (metis Diff_iff Un_iff count_access.simps(10) count_access.simps(41) 
        insertCI local.reflexive singleton_iff)
  hence \<open>W_false \<notin> {w. (\<forall> W1t. (w \<le><w> W1t \<and> W1t \<in> {W1,W2,W3}) \<longrightarrow> 
         (\<exists> W2t. W2t \<le><w> W1t \<and> W2t \<in> {W1,W2,W3} \<and> (\<forall> W3t. W3t \<le><w> W2t \<longrightarrow> 
         (W3t \<in> UNIV - {W1,W2,W3} \<union> {W1}))))}\<close> by blast
  thus \<open>W_false \<notin> {w. Phi \<in> \<bullet> w}  \<box>\<rightarrow>\<hungarumlaut> {w. Psi \<in> \<bullet> w}\<close> 
    using simplify_general_would phi_semantics psi_semantics by metis
qed

subsection \<open>The set of paths for $w_{true}$ and $w_{false}$ are equal.\<close>

lemma no_single_psi_world:
  shows \<open>\<forall> i1. \<bullet> i1 \<noteq> {Psi}\<close> 
  by (metis ap.simps(2) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
      atomic_truth.simps(4) atomic_truth.simps(5) insert_not_empty 
      singleton_insert_inj_eq world.exhaust)

lemma phi_only_phi_suc_on_path:
  assumes 
    path: \<open>is_path W_true \<pi>\<close> and
    nth_place_phi: \<open>\<pi> n = {Phi}\<close>
  shows \<open>\<pi> (Suc n) = {Phi}\<close> 
proof (rule ccontr)
  assume \<open>\<pi> (Suc n) \<noteq> {Phi}\<close>
  from this path nth_place_phi have non_phi_suc:\<open>\<exists> i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = {Phi} \<and> \<bullet>i2 \<noteq> {Phi}\<close> 
    by (metis is_path_def)
  hence \<open>\<exists> i1. W2 \<le><W_true> i1 \<and> \<bullet> i1 \<noteq> {Phi}\<close> using atomic_truth.simps(4) 
    by (metis atomic_truth.simps(1) atomic_truth.simps(2) count_access.simps(36) 
        count_access.simps(37) empty_not_insert meaningful_acessibility 
        W3_not_accessible_from_W_true world.exhaust)
  thus \<open>False\<close> 
    by (metis atomic_truth.simps(4) atomic_truth.simps(5) count_access.simps(42) 
        count_access.simps(43) count_access.simps(44) world.exhaust)
qed

lemma phi_psi_only_phy_psi_or_phi_suc:
  assumes 
    path: \<open>is_path W_true \<pi>\<close> and
    nth_place_phi_psi: \<open>\<pi> n = {Phi, Psi}\<close>
  shows
     \<open>\<pi> (Suc n) = {Phi,Psi} \<or> \<pi> (Suc n) = {Phi}\<close>
proof (rule ccontr)
  assume cont_assm: \<open>\<not> (\<pi> (Suc n) = {Phi, Psi} \<or> \<pi> (Suc n) = {Phi})\<close>
  from this path nth_place_phi_psi have non_phi_suc: 
    \<open>\<exists> i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = {Phi, Psi} \<and> \<bullet>i2 \<noteq> {Phi, Psi} \<and> \<bullet>i2 \<noteq> {Phi}\<close> by (metis is_path_def)
  have phi_psi_only_W1: \<open>\<exists> i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = {Phi, Psi} \<longrightarrow> i1 = W1\<close> by blast
  have \<open>\<exists> i1. W1 \<le><W_true> i1 \<longrightarrow> i1 = W1 \<and> i1 = W2\<close> by (meson count_access.simps(41))
  from phi_psi_only_W1 this have \<open>\<exists> i1. W1 \<le><W_true> i1 \<and> \<bullet>i1 \<noteq>  {Phi, Psi} \<and> \<bullet>i1 \<noteq>  {Phi}\<close> 
    using cont_assm atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
        atomic_truth.simps(4) atomic_truth.simps(5) non_phi_suc nth_place_phi_psi 
        path phi_only_phi_suc_on_path world.exhaust by (metis (full_types))
  thus \<open>False\<close> 
    by (metis atomic_truth.simps(3) atomic_truth.simps(4) atomic_truth.simps(5) 
        count_access.simps(36) count_access.simps(37) world.exhaust)
qed

lemma after_start_eq_forth:
  assumes
    \<open>\<pi> 0 = \<bullet>W_true \<and>  \<pi> 0 = \<bullet>W_false\<close>
  shows
    \<open>(\<forall>n. \<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)) \<Longrightarrow>
     (\<forall>n. \<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n))\<close>
proof 
  assume is_W_true_path: \<open>\<forall>n. \<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)\<close>
  fix m
  show \<open>\<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
  proof (induct m)
    case 0
    then show ?case 
      by (metis (full_types) is_W_true_path assms reflexive count_access.simps(10) 
          count_access.simps(8) count_access.simps(9) world.exhaust)
  next
    case (Suc m)
    assume \<open>\<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
    then obtain i1 i2 where fixed_i1_i2:\<open>i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close> by blast
    have \<open>\<bullet> i2 = {} \<or> \<bullet> i2 = {Phi} \<or> \<bullet> i2 = {Phi, Psi}\<close> 
      by (metis atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
          atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
    then show ?case
    proof 
      assume \<open>\<bullet>i2 = {}\<close> 
      from this is_W_true_path have 
        \<open>\<pi> (Suc (Suc m)) = {} \<or> \<pi> (Suc (Suc m)) = {Phi} \<or> \<pi> (Suc (Suc m)) = {Phi, Psi}\<close> 
        by (metis (full_types) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
            atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
      then show \<open>\<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close> 
        by (metis \<open>\<bullet>i2 = {}\<close> fixed_i1_i2 atomic_truth.simps(2) atomic_truth.simps(3) 
            atomic_truth.simps(5) count_access.simps(10) count_access.simps(8) 
            meaningful_acessibility)
    next
      assume phi_or_phi_and_psi: \<open>\<bullet>i2 = {Phi} \<or> \<bullet>i2 = {Phi, Psi}\<close>
      show \<open>\<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m)) \<close>
      proof (cases \<open>\<bullet>i2 = {Phi}\<close>)
        case True
        have nth_place_phi: \<open>\<pi> (Suc m) = {Phi}\<close> using True fixed_i1_i2 by auto
        from this is_W_true_path phi_only_phi_suc_on_path have \<open>\<pi> (Suc (Suc m)) = {Phi}\<close> 
          using assms is_path_def by presburger
        then show ?thesis using Suc nth_place_phi by auto
      next
        case False
        from this phi_or_phi_and_psi have \<open>\<bullet>i2 = {Phi,Psi}\<close> by blast
        have nth_place_phi_psi: \<open>\<pi> (Suc m) = {Phi, Psi}\<close> 
          using \<open>\<bullet>i2 = {Phi, Psi}\<close> fixed_i1_i2 by auto
        from this is_W_true_path phi_psi_only_phy_psi_or_phi_suc have  
          \<open>\<pi> (Suc (Suc m)) = {Phi, Psi} \<or>\<pi> (Suc (Suc m)) = {Phi}\<close> using assms is_path_def by presburger
        then show ?thesis by (metis atomic_truth.simps(3) atomic_truth.simps(4) 
                              count_access.simps(12) local.reflexive nth_place_phi_psi)
      qed
    qed
  qed
qed  

lemma phi_only_phi_suc_on_path_W_false:
  assumes 
    path: \<open>is_path W_false \<pi>\<close> and
    nth_place_phi: \<open>\<pi> n = {Phi}\<close>
  shows \<open>\<pi> (Suc n) = {Phi}\<close> 
proof (rule ccontr)
  assume \<open>\<pi> (Suc n) \<noteq> {Phi}\<close>
  from this path nth_place_phi have non_phi_suc:
    \<open>\<exists> i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = {Phi} \<and> \<bullet>i2 \<noteq> {Phi}\<close> by (metis is_path_def)
  hence \<open>\<exists> i1. W2 \<le><W_false> i1 \<and> \<bullet> i1 \<noteq> {Phi}\<close> 
    by (metis atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
        atomic_truth.simps(5) count_access.simps(36) count_access.simps(37) count_access.simps(46) 
        count_access.simps(47) count_access.simps(48) insert_not_empty world.exhaust)
  thus \<open>False\<close> 
    by (metis atomic_truth.simps(4) atomic_truth.simps(5) count_access.simps(42) 
        count_access.simps(43) count_access.simps(44) world.exhaust)
qed

lemma phi_psi_only_phy_psi_or_phi_suc_W_false:
  assumes 
    path: \<open>is_path W_false \<pi>\<close> and
    nth_place_phi_psi: \<open>\<pi> n = {Phi, Psi}\<close>
  shows
     \<open>\<pi> (Suc n) = {Phi,Psi} \<or> \<pi> (Suc n) = {Phi}\<close>
proof (rule ccontr)
  assume contr_assm: \<open>\<not> (\<pi> (Suc n) = {Phi, Psi} \<or> \<pi> (Suc n) = {Phi})\<close>
  from this path nth_place_phi_psi have non_phi_suc: 
    \<open>\<exists> i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = {Phi, Psi} \<and> \<bullet>i2 \<noteq> {Phi, Psi} \<and> \<bullet>i2 \<noteq> {Phi}\<close> unfolding is_path_def 
    by metis
  hence \<open>\<exists> i1. W1 \<le><W_true> i1 \<and> \<bullet>i1 \<noteq>  {Phi, Psi} \<and> \<bullet>i1 \<noteq>  {Phi}\<close>  
    by (metis contr_assm atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
        atomic_truth.simps(5) count_access.simps(36) count_access.simps(37) insert_not_empty 
        nth_place_phi_psi path phi_only_phi_suc_on_path_W_false world.exhaust)
  thus \<open>False\<close> by (metis atomic_truth.simps(3) atomic_truth.simps(4) atomic_truth.simps(5) 
                   count_access.simps(36) count_access.simps(37) world.exhaust)
qed

lemma after_start_eq_back:
  assumes
    \<open>\<pi> 0 = \<bullet>W_true \<and>  \<pi> 0 = \<bullet>W_false\<close>
  shows
    \<open>(\<forall>n. \<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)) \<Longrightarrow>
     (\<forall>n. \<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n))\<close>
proof
  assume is_W_false_path: \<open>\<forall>n. \<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)\<close>
  fix m
  show \<open>\<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
  proof (induct m)
    case 0 
    from is_W_false_path have \<open>\<pi> 0 = {}\<close> by (simp add: assms)
    then show ?case 
      by (metis (no_types, opaque_lifting) atomic_truth.simps(1) atomic_truth.simps(2) 
          atomic_truth.simps(4) atomic_truth.simps(5) count_access.simps(6) count_access.simps(7) 
          is_W_false_path local.reflexive world.exhaust)
    case (Suc m)
    assume \<open>\<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close>
    then obtain i1 i2 where fixed_i1_i2: \<open>i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> m \<and> \<bullet>i2 = \<pi> (Suc m)\<close> by blast
    from is_W_false_path have \<open>\<bullet> i2 = {} \<or> \<bullet> i2 = {Phi} \<or> \<bullet> i2 = {Phi, Psi}\<close>  
      by (metis atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
          atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
    from this show ?case  
    proof 
      assume \<open>\<bullet>i2 = {}\<close>
      from this is_W_false_path have 
        \<open>\<pi> (Suc (Suc m)) = {} \<or> \<pi> (Suc (Suc m)) = {Phi} \<or> \<pi> (Suc (Suc m)) = {Phi, Psi}\<close> 
        by (metis (full_types) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(3) 
            atomic_truth.simps(4) atomic_truth.simps(5) world.exhaust)
      then show \<open>\<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close> 
        by (metis \<open>\<bullet>i2 = {}\<close> fixed_i1_i2 atomic_truth.simps(1) atomic_truth.simps(3) 
            atomic_truth.simps(4) count_access.simps(6) count_access.simps(7) 
            world_dependant_kripke_structure_axioms world_dependant_kripke_structure_def)
     next
       assume phi_or_phi_and_psi: \<open>\<bullet>i2 = {Phi} \<or> \<bullet>i2 = {Phi, Psi}\<close>
       show \<open>\<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close>
       proof (cases \<open>\<bullet>i2 = {Phi}\<close>)
         case True
         have nth_place_phi: \<open>\<pi> (Suc m) = {Phi}\<close> 
           using True fixed_i1_i2 by auto
         from this is_W_false_path have \<open>\<pi> (Suc (Suc m)) = {Phi}\<close> using assms is_path_def 
           using phi_only_phi_suc_on_path_W_false by auto
         then show \<open>\<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> (Suc m) \<and> \<bullet>i2 = \<pi> (Suc (Suc m))\<close> 
           using atomic_truth.simps(4) nth_place_phi by blast
       next
         case False
         from this phi_or_phi_and_psi have \<open>\<bullet>i2 = {Phi,Psi}\<close> by blast
         have nth_place_phi_psi: \<open>\<pi> (Suc m) = {Phi, Psi}\<close> 
           using \<open>\<bullet>i2 = {Phi, Psi}\<close> fixed_i1_i2 by auto
         from this is_W_false_path phi_psi_only_phy_psi_or_phi_suc_W_false have 
           \<open>\<pi> (Suc (Suc m)) = {Phi, Psi} \<or>\<pi> (Suc (Suc m)) = {Phi}\<close> using assms is_path_def by simp
         then show ?thesis 
           by (metis atomic_truth.simps(3) atomic_truth.simps(4) count_access.simps(11) 
               nth_place_phi_psi reflexive)
       qed 
     qed
  qed
qed

lemma W_false_path_iff_W_true_path:
  shows \<open>is_path W_false \<pi> \<longleftrightarrow> is_path W_true \<pi>\<close>
proof (unfold is_path_def)
  have same_start: \<open>\<pi> 0 = \<bullet>W_false \<longleftrightarrow> \<pi> 0 = \<bullet>W_true\<close> by simp
  then show \<open>\<pi> 0 = \<bullet>W_false \<and> (\<forall>n. \<exists>i1 i2. i1 \<le><W_false> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n)) \<longleftrightarrow>
             \<pi> 0 = \<bullet>W_true \<and> (\<forall>n. \<exists>i1 i2. i1 \<le><W_true> i2 \<and> \<bullet>i1 = \<pi> n \<and> \<bullet>i2 = \<pi> (Suc n))\<close>
  using after_start_eq_forth after_start_eq_back by auto
qed
  
lemma W_true_and_W_false_paths_eq:
  shows \<open>paths W_true = paths W_false\<close> 
  using W_false_path_iff_W_true_path paths_def by auto

subsection \<open>CTL* can not distinguish between $w_{true}$ and $w_{false}$\<close>

definition existing_path :: \<open>ap set word\<close>
  where \<open>existing_path _ = {}\<close>

lemma existst_path_true_at_W_true_and_W_false:
  shows \<open>\<exists> \<pi>. is_path W_true \<pi> \<and> is_path W_false \<pi>\<close>
proof
  show \<open>is_path W_true existing_path \<and> is_path W_false existing_path\<close>
    by (metis atomic_truth.simps(1) atomic_truth.simps(2) existing_path_def is_path_def reflexive)
qed

lemma ltlr_only_distiguishing_differnt_paths:
  fixes 
    ltlr_formula :: \<open>ap ltlr\<close> and
    \<pi> \<rho> :: \<open>ap set word\<close>
  shows \<open>\<pi> \<Turnstile>\<^sub>r ltlr_formula \<and> \<not> (\<rho> \<Turnstile>\<^sub>r ltlr_formula) \<Longrightarrow> \<pi> \<noteq> \<rho>\<close> by auto

lemma paths_eq_all_paths_truth_eq:
  assumes
    \<open>\<exists> \<pi>. is_path W1t \<pi> \<and> is_path W2t \<pi>\<close> and
    \<open>paths W1t = paths W2t\<close>
  shows
    \<open>W1t \<in> \<lbrakk> A(ltlr_formula) \<rbrakk> \<Longrightarrow> W2t \<in> \<lbrakk>  A(ltlr_formula) \<rbrakk>\<close>
proof (rule ccontr)
  assume \<open>W1t \<in> \<lbrakk> A(ltlr_formula) \<rbrakk>\<close>
  hence all_paths_true: \<open>\<forall> \<pi>. is_path W1t \<pi> \<longrightarrow> \<pi> \<Turnstile>\<^sub>r ltlr_formula\<close> by simp
  assume \<open>W2t \<notin> \<lbrakk> A(ltlr_formula) \<rbrakk>\<close>  
  hence \<open>\<exists> \<pi>. is_path W2t \<pi> \<and> \<not> \<pi> \<Turnstile>\<^sub>r ltlr_formula\<close> by simp
  thus \<open>False\<close> using all_paths_true assms(2) paths_def by auto
qed

lemma paths_eq_means_non_distiguishable:
  fixes
    ctl_star_formula :: \<open>ap ltlr ctl_star\<close>
  shows \<open>W_true \<in> \<lbrakk> ctl_star_formula \<rbrakk> \<longleftrightarrow>  W_false \<in> \<lbrakk> ctl_star_formula \<rbrakk>\<close>
proof (induct rule: ctl_star.induct)
  case (all_ctl_star x)
  show ?case 
    using existst_path_true_at_W_true_and_W_false paths_eq_all_paths_truth_eq 
      W_true_and_W_false_paths_eq by blast
next
  case (and_ctl_star x1a x2)
  then show ?case by simp
next
  case (not_ctl_star x)
  then show ?case by simp
qed

subsection \<open>General Woulds semantics can not be expressed by CTL*\<close>

lemma general_would_not_in_ctl_star:
  fixes
    ctl_star_formula :: \<open>ap ltlr ctl_star\<close>
  shows \<open>{w. Phi \<in> \<bullet> w} \<box>\<rightarrow>\<hungarumlaut> {w. Psi \<in> \<bullet> w} \<noteq> \<lbrakk> ctl_star_formula \<rbrakk>\<close>
proof (rule ccontr)
  assume semantics_eq: \<open>\<not> {w. Phi \<in> \<bullet>w} \<box>\<rightarrow>\<hungarumlaut> {w. Psi \<in> \<bullet>w} \<noteq> \<lbrakk> ctl_star_formula \<rbrakk>\<close>
  hence W_true_in_semantics:\<open>W_true \<in> \<lbrakk> ctl_star_formula \<rbrakk>\<close> using W_true_in_would_sem by blast
  from semantics_eq have \<open>W_false \<notin> \<lbrakk> ctl_star_formula \<rbrakk>\<close> using W_false_not_in_would_sem 
    by fastforce 
  then show \<open>False\<close> using W_true_in_semantics paths_eq_means_non_distiguishable by auto
qed

end
end