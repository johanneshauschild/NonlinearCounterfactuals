section \<open>Structure and sets of assumptions\<close>

theory StructureAndAssumptions
  imports Main
begin 

locale world_dependant_kripke_structure =
  fixes
    \<comment>\<open>Assigning a set of atomic propositions to each world.\<close>
    ap :: \<open>'i \<Rightarrow> 'ap set\<close> and
    \<comment>\<open>$w1 \leq_w w2$ is enconding the notion "$w_1$ at least as similar to $w$ as is $w_2$".
      A similar relation was defined by Lewis @{cite lewisCounterfactuals1973} as well as Finkbeiner 
      and Siber @{cite finkbeinerCounterfactualsModuloTemporal2023}\<close>
    accessibility :: \<open>'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool\<close> ("_ \<le><_> _" [70, 70, 70] 80)
  assumes
    reflexive [intro]: \<open>w1 \<le><w> w1\<close>

text \<open>This structure is meant to implement a Kripke structure close to these employed by Baier and 
      Katoen @{cite baier2008modelchecking}. The name "accessibility" for the function encoding the similarity 
      between worlds is due to the fact, that it is reinterpreted to state the fact "$w_1$ is more 
      accessible from $w$ than $w_2$" in the following \texttt{locales}.

      We dropped the set of initial states, allowing every state to be an initial one.\<close>

locale preordered_counterfactual_structure = world_dependant_kripke_structure ap accessibility
  for
    ap :: \<open>'i \<Rightarrow> 'ap set\<close> and
    accessibility :: "'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool" ("_ \<le><_> _" [70, 70, 70] 80) +
  assumes
    \<comment>\<open>Lewis' @{cite lewisCounterfactuals1973}  as well as Finkbeiner and Sibers 
      @{cite finkbeinerCounterfactualsModuloTemporal2023} structure are transitive\<close>
    transitive [intro]: \<open>\<lbrakk>w1 \<le><w> w2; w2 \<le><w> w3\<rbrakk> \<Longrightarrow> w1 \<le><w> w3\<close>  and
    \<comment>\<open>We assume, that any two worlds, which are comparable in respect to a world, are also 
      accessible from that world:\<close>
    meaningful_acessibility [intro]: \<open>\<lbrakk>w1 \<le><w> w2; w1 \<noteq> w2\<rbrakk> \<Longrightarrow> w \<le><w> w1 \<and> w \<le><w> w2\<close> 

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

\<comment>\<open>A lemma testing for a basic liveliness property.\<close>
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
    by (metis linearity transitive)
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

lemma (in preordered_counterfactual_structure) subset_generalized:
  shows\<open>(\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<psi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
        (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>))) \<longrightarrow> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
      (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - (\<phi> \<union> \<psi>) \<union> (UNIV - \<psi>))))\<close>
  by (metis DiffI UNIV_I Un_iff local.reflexive local.transitive meaningful_acessibility)

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
    by (metis linearity transitive)
qed

lemma (in preordered_counterfactual_structure) phi_or_psi_to_phi:
  \<open>\<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> 
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>))) \<longleftrightarrow> 
  (\<nexists>w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> 
   (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))\<close>
  by (auto, metis reflexive transitive meaningful_acessibility)

end