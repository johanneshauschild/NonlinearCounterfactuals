theory StructureAndAssumptions
  imports Main
begin 

section \<open>Structure and sets of assumptions\<close>

locale world_dependent_kripke_structure =
  fixes
    \<comment>\<open>assigning a set of atomic propositions to each world.\<close>
    ap :: \<open>'i \<Rightarrow> 'ap set\<close> and
    \<comment>\<open>$w1 \leq_w w2$ is enconding the notion "world w1 is more similiar to w than w2"\<close>
    accessibility :: \<open>'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool\<close> ("_ \<le><_> _" [70, 70, 70] 80)
  assumes
    reflexive [intro]: \<open>w1 \<le><w> w1\<close>

text \<open>We dropped the set of initial states, allowing every state to be an initial one.
      This structure is meant to implement a Kripke structure.\<close>

locale preordered_counterfactual_structure = world_dependent_kripke_structure ap accessibility
  for
    ap :: \<open>'i \<Rightarrow> 'ap set\<close> and
    accessibility :: "'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool" ("_ \<le><_> _" [70, 70, 70] 80) +
  assumes
    transitive [intro]: \<open>\<lbrakk>w1 \<le><w> w2; w2 \<le><w> w3\<rbrakk> \<Longrightarrow> w1 \<le><w> w3\<close>  and
    \<comment>\<open>We assume, that any two worlds, wich are comparable in respect to a world, are also 
      acessible from that world:\<close>
    meaningful_acessibility [intro]: \<open>\<lbrakk>w1 \<le><w> w2; w1 \<noteq> w2\<rbrakk> \<Longrightarrow> w \<le><w> w1 \<and> w \<le><w> w2\<close> 

text \<open>Finkbeiner and Siber @{cite finkbeinerCounterfactualsModuloTemporal2023}, 
      as well as Lewis @{cite lewisCounterfactuals1973}, require $\leq_w$ to be minimal. 
      Conducting the proofs, this assumption turned out to be spurious. Hence it is not included 
      in any of the locales\<close>

locale finkbeiner_siber_structure = preordered_counterfactual_structure ap accessibility
  for
    ap :: \<open>'i \<Rightarrow> 'ap set\<close> and
    accessibility :: "'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool" ("_ \<le><_> _" [70, 70, 70] 80) +
  assumes
    total_accessibility: \<open>\<forall> w'. w \<le><w> w'\<close>

locale lewisian_structure =  preordered_counterfactual_structure ap accessibility
  for
    ap :: \<open>'i \<Rightarrow> 'ap set\<close> and
    accessibility :: "'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool" ("_ \<le><_> _" [70, 70, 70] 80) +
  assumes
    linearity: \<open>\<lbrakk>w \<le><w> w1; w\<le><w> w2\<rbrakk> \<Longrightarrow> w1 \<le><w> w2 \<or> w2 \<le><w> w1\<close>

locale total_accessible_lewisian_structure = lewisian_structure + finkbeiner_siber_structure

section \<open>Formula equivalences\<close>

\<comment>\<open>A lemma testing for basic liveliness property of the counterfactual structures.\<close>
lemma (in preordered_counterfactual_structure) not_phi_would_phi_false:
  shows 
    \<open>\<exists>w1. w \<le><w> w1 \<and> w1 \<in> UNIV - \<phi> \<and> (\<forall>w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> \<phi>) \<Longrightarrow> False\<close>
  by blast

text \<open>The following lemmata are dedicated to prove formula equivalences for later use.\<close>

lemma (in lewisian_structure) non_vacuous_woulds_equal:
  assumes
    \<open>\<exists> wz. w \<le><w> wz  \<and> wz \<in> \<phi>\<close>
  shows
    \<open>(\<forall> w1. (w \<le><w> w1 \<and> w1 \<in> \<phi>) \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
    (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>))) \<longleftrightarrow> (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
    (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))\<close>
proof
  assume \<open>\<forall>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
          (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>))\<close>
  thus \<open>\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall>w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>)\<close>
    by (metis assms meaningful_acessibility)
next
  assume \<open>\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall>w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>)\<close>
  thus \<open>\<forall>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
       (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>))\<close>
    by (metis linearity local.transitive)
qed

lemma (in preordered_counterfactual_structure) phi_stays_in_set:
  shows \<open>\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> (\<phi> \<union> \<psi>) \<or> w3 \<in> (UNIV - \<psi>))
        \<Longrightarrow> (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow>  w3 \<in> (UNIV - \<psi>)))\<close>
  by auto 

lemma (in preordered_counterfactual_structure) no_element_in_psi:
  shows \<open>(\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow>  w3 \<in> (UNIV - \<psi>))) \<Longrightarrow> 
  (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow>  w3 \<in> (UNIV - \<psi>)))\<close> by blast

lemma (in preordered_counterfactual_structure) possible_phi:
  shows \<open>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> (\<phi> \<union> \<psi>) \<and>
  (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>))) \<Longrightarrow> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi>)\<close> 
  by (metis meaningful_acessibility)

lemma (in preordered_counterfactual_structure) subset_can_be_generalized:
  shows \<open>(\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)) \<Longrightarrow> 
  (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - (\<phi> \<union> \<psi>) \<union> (UNIV - \<psi>)))\<close>
  by (metis Compl_eq_Diff_UNIV Compl_iff Un_iff)

lemma (in preordered_counterfactual_structure) simplify_general_strong_would:
  shows \<open>(\<forall> w1. w \<le><w> w1 \<and> w1 \<in> (\<phi> \<union> \<psi>) \<longrightarrow> 
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>))) \<Longrightarrow> 
  (\<forall>w1. w \<le><w> w1 \<and> w1 \<in> (\<phi> \<union> \<psi>) \<longrightarrow> (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi>))\<close>
  by auto

lemma (in preordered_counterfactual_structure) simplify_general_might_to_at_least_as_pos:
  shows
    \<open>\<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<or> 
    (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<longrightarrow> 
    (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> (\<phi> \<union> \<psi>) \<inter> \<phi>))) \<Longrightarrow>  
    \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> 
    (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))\<close>
  by auto

lemma (in preordered_counterfactual_structure) extend_at_least_as_pos_to_general_might:
  shows
    \<open>\<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> 
    \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>))) \<Longrightarrow> \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<or> 
    ((\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<longrightarrow> 
    (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> (\<phi> \<union> \<psi>) \<inter> \<phi>))))\<close>
  by (auto, metis meaningful_acessibility)

lemma (in lewisian_structure) general_would_comprehension_is_would_comprehension:
  shows
    \<open>(\<forall> w1. (w \<le><w> w1 \<and> w1 \<in> \<phi>) \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
     (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>))) \<longleftrightarrow> (\<forall> w1. (w \<le><w> w1) \<longrightarrow> w1 \<notin> \<phi>) \<or> 
     (\<exists> w1. (w \<le><w> w1) \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))\<close>
proof
  assume \<open>(\<forall>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
          (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>)))\<close>
  thus \<open>(\<forall>w1. w \<le><w> w1 \<longrightarrow> w1 \<notin> \<phi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
        (\<forall>w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))\<close>
    by (metis meaningful_acessibility)
next
  assume \<open>(\<forall>w1. w \<le><w> w1 \<longrightarrow> w1 \<notin> \<phi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
          (\<forall>w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))\<close>
  thus \<open>(\<forall>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
        (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>)))\<close>
    by (metis lewisian_structure.linearity lewisian_structure_axioms local.transitive)
qed

end