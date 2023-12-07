theory GeneralOperators
  imports 
    FinkbeinerSiberOperators
begin

section \<open>A reinterpretation of Lewis operators in the base structure\<close>

subsection \<open>Defining the operators\<close>

text \<open>Finkbeiner and Siber  @{cite finkbeinerCounterfactualsModuloTemporal2023} suggest to drop the 
      assumption that every world is accessible 
      from the actual world by not including inaccessible worlds in $\leq_w$. Small modifications on 
      Universal Would and Existential Might make it possible to depict their semantics 
      without assuming \emph{total accessibility}.\<close>

definition (in preordered_counterfactual_structure) general_would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<rightarrow> _\<close> [70, 70] 100) 
  where
    \<open>\<phi> \<box>\<rightarrow> \<psi> \<equiv> {w. (\<forall> w1. w \<le><w> w1 \<longrightarrow>  w1 \<notin> \<phi>) \<or> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> 
     (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> (w3 \<in> UNIV - \<phi> \<union> \<psi>))))}\<close>

abbreviation (in preordered_counterfactual_structure) general_might ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<diamond>\<rightarrow> _\<close> [70, 70] 100)  
  where
    \<open>\<phi> \<diamond>\<rightarrow> \<psi> \<equiv> UNIV - (\<phi> \<box>\<rightarrow> (UNIV - \<psi>))\<close> 

abbreviation  (in preordered_counterfactual_structure) general_strong_would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<Rightarrow> _\<close> [70, 70] 100)  
  where 
    \<open>\<phi> \<box>\<Rightarrow> \<psi> \<equiv> (\<diamond>\<phi>) \<inter> (\<phi> \<box>\<rightarrow> \<psi>)\<close>

abbreviation  (in preordered_counterfactual_structure) general_weak_might ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<diamond>\<Rightarrow> _\<close> [70, 70] 100)  
  where
    \<open>\<phi> \<diamond>\<Rightarrow> \<psi> \<equiv> UNIV - (\<phi> \<box>\<Rightarrow> (UNIV - \<psi>))\<close>

abbreviation (in preordered_counterfactual_structure) general_more_possible ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<prec>\<close> 100)  
  where 
    \<open>\<phi> \<prec> \<psi> \<equiv> (\<phi> \<union> \<psi>) \<box>\<Rightarrow> (UNIV - \<psi>)\<close>

abbreviation (in preordered_counterfactual_structure) general_at_least_as_possible :: 
  \<open>'i set \<Rightarrow>  'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<preceq>\<close> 100)
  where 
    \<open>\<phi> \<preceq> \<psi> \<equiv> (\<phi> \<union> \<psi>) \<diamond>\<Rightarrow> \<phi>\<close>

subsection \<open>Validating the definitions\<close>

text \<open>An example of a world and accessibility relation in which 
      "if $\varphi$ would be the case, then $\psi$ would be the case" holds in the 
      generalised version for the would operator.\<close>

lemma (in preordered_counterfactual_structure) general_would_instatiation:
  assumes
    \<open>\<phi> = {W3, W1}\<close> and
    \<open>\<psi> = {W1}\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>W \<le><W> W3\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W2 \<le><W> W3\<close> and
    \<open>\<not>W3 \<le><W> W1\<close> and
    \<open>W1 \<le><W> W3\<close> and
    \<open>W \<noteq> W3 \<and> W \<noteq> W1 \<and> W3 \<noteq> W1\<close>
  shows    
    \<open>W \<in> \<phi> \<box>\<rightarrow> \<psi>\<close>
  using assms unfolding general_would_def by blast

lemma (in preordered_counterfactual_structure) possible_eq_to_gen_would_def:
  shows \<open>w \<in> \<diamond> \<phi> \<longleftrightarrow> w \<in> UNIV - (\<phi> \<box>\<rightarrow> {})\<close>
  unfolding general_would_def by fastforce

lemma (in preordered_counterfactual_structure) general_might_follows_definition:
  shows \<open>w \<in> \<phi> \<diamond>\<rightarrow> \<psi> \<longleftrightarrow> w \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
         (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>))}\<close>
  unfolding general_would_def using Int_iff UNIV_I Un_iff mem_Collect_eq 
    preordered_counterfactual_structure_axioms by auto

lemma (in preordered_counterfactual_structure) general_strong_would_follows_definition:
  shows \<open>w \<in> \<phi> \<box>\<Rightarrow> \<psi> \<longleftrightarrow> w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> 
        (\<forall> w1. (w \<le><w> w1 \<and> w1 \<in> \<phi>) \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
        (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>)))}\<close>
  using general_would_def preordered_counterfactual_structure_axioms by auto

lemma (in preordered_counterfactual_structure) general_weak_might_follows_definition:
  shows \<open>w \<in> \<phi> \<diamond>\<Rightarrow> \<psi> \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or> 
         (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> 
         (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
proof
  assume \<open>w \<in> UNIV - ((\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> (UNIV - \<psi>)))\<close>
  thus \<open>w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or> (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
    using general_would_def preordered_counterfactual_structure_axioms by auto
next
  assume \<open>w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or> (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
          (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
  thus \<open>w \<in> UNIV - ((\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> (UNIV - \<psi>)))\<close>
    using general_would_def preordered_counterfactual_structure_axioms by auto
qed

text \<open>While we are able to deliver a set comprehension capturing the semantics for 
      \emph{General More Possible} as well as \emph{General At least as Possible}
      The big difference from the \emph{set comprehensions} for their Lewisian counterparts 
      suggests, that their semantics are strongly tied to the \emph{linearity} assumption.\<close>
lemma (in preordered_counterfactual_structure) general_more_possible_follows_definition:
  shows \<open>w \<in> \<phi> \<prec> \<psi> \<longleftrightarrow> w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>
  \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close>
proof
  assume \<open>w \<in> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow> (UNIV - \<psi>))\<close>
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<phi> \<union> \<psi> \<or> w3 \<in> UNIV - \<psi>)))}\<close>
    using general_would_def preordered_counterfactual_structure_axioms by auto 
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<psi>)))}\<close> 
      using phi_stays_in_set by auto
  hence \<open>w \<in> {w. (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<psi>)))}\<close>
      using no_element_in_psi by auto
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close> by auto
  thus \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<psi> \<longrightarrow> 
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close> using possible_phi by blast
next
  assume \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and>
          (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<psi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> 
          (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close>
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> 
        (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<and> 
        (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - (\<phi> \<union> \<psi>) \<union> (UNIV - \<psi>))))}\<close> 
      using subset_generalized by blast
    thus \<open>w \<in> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow> (UNIV - \<psi>))\<close> 
      using general_strong_would_follows_definition by presburger
qed

lemma (in preordered_counterfactual_structure) weak_might_def_to_set_comprehension:
  shows \<open>w \<in> UNIV - ((\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> (UNIV - \<psi>))) \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or>
         (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> 
         (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
  using general_weak_might_follows_definition by presburger

lemma (in preordered_counterfactual_structure) general_at_least_as_possible_follows_definition:
  shows 
    \<open>w \<in> \<phi> \<preceq> \<psi> \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or>
    (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close>
proof 
  assume \<open>w \<in> UNIV - (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow> (UNIV - \<phi>))\<close>
  hence \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<or> 
  (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<longrightarrow> 
  (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> (\<phi> \<union> \<psi>) \<inter> \<phi>)))}\<close> using weak_might_def_to_set_comprehension by meson
  hence \<open>w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> 
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close> 
    using simplify_general_might_to_at_least_as_pos by auto
  thus \<open>w \<in> {w. (\<nexists>w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
        (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close> 
    using phi_or_psi_to_phi by force
next
  assume \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and>
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close>
  hence \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and>
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close> using phi_or_psi_to_phi by force
  hence \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> 
  \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> (\<phi> \<union> \<psi>) \<inter> \<phi>)))}\<close> 
    using extend_at_least_as_pos_to_general_might by auto 
  thus \<open>w \<in> UNIV - ((\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow> (UNIV - \<phi>)))\<close> 
    using weak_might_def_to_set_comprehension by presburger
qed

subsection \<open>Comparison to Lewis Operators\<close>

text \<open>Finally, we are able to show, that the generalised operators meet their Lewisian counterparts
      under the \emph{linearity} assumption. The same holds for Finkbeiner and Sibers operators 
      under the \emph{total accessibility} assumption.
      For any of the Lewisian operators (exept `At Least As Possible'), it can be shown by 
      counterexample, that they miss their 
      (likely) intended semantics being evaluated under the base assumptions.
      The same holds for Finkbeiner and Sibers operators.\<close>

lemma (in lewisian_structure) would_equivalent_to_general_would:
  shows
    \<open>w \<in> \<phi> \<box>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<rightarrow> \<psi>\<close> 
  unfolding would_def general_would_def using general_would_comprehension_is_would_comprehension 
  by blast

lemma (in preordered_counterfactual_structure) would_not_wide_enough:
  assumes
    \<open>\<phi> = {W1, W2}\<close> and
    \<open>\<psi> = {W2}\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>\<not> W1 \<le><W> W2\<close> and
    \<open>\<not> W2 \<le><W> W1\<close> and
    \<open>W \<noteq> W1 \<and> W \<noteq> W2 \<and> W1 \<noteq> W2\<close>
  shows
    \<open>W \<notin> \<phi> \<box>\<rightarrow> \<psi> \<and> W \<in> \<phi> \<box>\<rightarrow>\<^sub>L \<psi>\<close>
proof
    have \<open>(\<forall> w1. W \<le><W> w1 \<longrightarrow> w1 \<notin> \<phi>) \<or> (\<forall> w1. W \<le><W> w1 \<and> w1 \<in> \<phi> \<longrightarrow>
    (\<exists> w2. w2 \<le><W> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><W> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>))) \<Longrightarrow> False\<close> 
      using assms(1) assms(2) assms(4) assms(6) assms(7) by blast
    thus \<open>W \<notin> \<phi> \<box>\<rightarrow> \<psi>\<close> using general_would_def by force
next
    have \<open>(\<forall> w1. W \<le><W> w1 \<longrightarrow> w1 \<notin> \<phi>) \<or> 
    (\<exists> w1. W \<le><W> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><W> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))\<close> 
      using assms(1) assms(2) assms(3) assms(5) by blast
    thus \<open>W \<in> \<phi> \<box>\<rightarrow>\<^sub>L \<psi>\<close> by (simp add: would_def)
qed

lemma (in lewisian_structure) might_equivalent_to_general_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<rightarrow> \<psi>\<close>
  by (simp add: would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) might_not_narrow_enough:
  assumes
    \<open>\<phi> = {W1, W2}\<close> and
    \<open>\<psi> = {W1}\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>\<not> W1 \<le><W> W2\<close> and
    \<open>\<not> W2 \<le><W> W1\<close> and
    \<open>W \<noteq> W1 \<and> W \<noteq> W2 \<and> W1 \<noteq> W2\<close>
  shows
    \<open>W \<notin> \<phi> \<diamond>\<rightarrow>\<^sub>L \<psi> \<and> W \<in> \<phi> \<diamond>\<rightarrow> \<psi>\<close>
proof
  show \<open>W \<notin> UNIV - \<phi> \<box>\<rightarrow>\<^sub>L(UNIV - \<psi>)\<close> 
    unfolding would_def using assms(1) assms(2) assms(3) assms(5) by blast
next
  have  \<open>W \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> 
         (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>))}\<close> using assms(1) assms(2) assms(4) assms(6) by blast
  thus \<open>W \<in> UNIV - \<phi> \<box>\<rightarrow> (UNIV - \<psi>)\<close> using general_might_follows_definition by presburger
qed

lemma (in lewisian_structure) strong_would_equivalent_to_general_strong_would:
  shows
    \<open>w \<in> \<phi> \<box>\<Rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<Rightarrow> \<psi>\<close>
  by (simp add: would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) strong_would_not_wide_enough:
  assumes
    \<open>\<phi> = {W1, W2}\<close> and
    \<open>\<psi> = {W2, W}\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>\<not> W1 \<le><W> W2\<close> and
    \<open>\<not> W2 \<le><W> W1\<close> and
    \<open>W \<noteq> W1 \<and> W \<noteq> W2 \<and> W1 \<noteq> W2\<close>
  shows
    \<open>W \<notin> \<phi> \<box>\<Rightarrow> \<psi> \<and> W \<in> \<phi> \<box>\<Rightarrow>\<^sub>L \<psi>\<close>
proof
  show \<open>W \<in> (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<^sub>L\<psi>)\<close> 
    using assms would_def by auto
next
  show \<open>W \<notin> (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> \<psi>)\<close> 
    using assms general_would_def preordered_counterfactual_structure_axioms by auto
qed

lemma (in lewisian_structure) weak_might_equivalent_to_general_weak_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<Rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<Rightarrow> \<psi>\<close>
  by (simp add: would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) weak_might_not_narrow_enough:
  assumes
    \<open>\<phi> = {W1, W2}\<close> and
    \<open>\<psi> = {W1}\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>\<not> W1 \<le><W> W2\<close> and
    \<open>\<not> W2 \<le><W> W1\<close> and
    \<open>W \<noteq> W1 \<and> W \<noteq> W2 \<and> W1 \<noteq> W2\<close>
  shows
    \<open>W \<notin> \<phi> \<diamond>\<Rightarrow>\<^sub>L \<psi> \<and> W \<in> \<phi> \<diamond>\<Rightarrow> \<psi>\<close>
proof
  show \<open>W \<notin> UNIV - (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<^sub>L(UNIV - \<psi>))\<close>
    unfolding would_def using assms(1) assms(2) assms(3) assms(5) by blast
  show \<open>W \<in> UNIV - (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> (UNIV - \<psi>))\<close> 
    using assms might_not_narrow_enough by auto
qed
    
lemma (in lewisian_structure) more_possible_equivalent_to_general_more_possible:
  shows
    \<open>w \<in> \<phi> \<prec>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<prec> \<psi>\<close>
  using strong_would_equivalent_to_general_strong_would by presburger

lemma (in preordered_counterfactual_structure) more_possible_not_wide_enough:
  assumes
    \<open>\<phi> = {W2}\<close> and
    \<open>\<psi> = {W1}\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>\<not> W1 \<le><W> W2\<close> and
    \<open>\<not> W2 \<le><W> W1\<close> and
    \<open>W \<noteq> W1 \<and> W \<noteq> W2 \<and> W1 \<noteq> W2\<close>
  shows \<open>W \<in> \<phi> \<prec>\<^sub>L \<psi> \<and> W \<notin> \<phi> \<prec> \<psi>\<close>
proof
  have \<open>W \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<notin> \<psi>)}\<close> 
      using assms(1) assms(2) assms(3) assms(5) by blast
  thus \<open>W \<in> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow>\<^sub>L (UNIV - \<psi>))\<close> 
      using assms might_not_narrow_enough preordered_counterfactual_structure_axioms by auto
next
  show \<open>W \<notin> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow> (UNIV - \<psi>))\<close> 
    using assms might_not_narrow_enough by auto
qed

lemma (in lewisian_structure) at_least_as_possible_equivalent_to__general_at_least_as_possible:
  shows
    \<open>w \<in> \<phi> \<preceq> \<psi> \<longleftrightarrow> w \<in> \<phi> \<preceq>\<^sub>L \<psi>\<close>
  using weak_might_equivalent_to_general_weak_might by presburger

lemma (in preordered_counterfactual_structure) at_least_as_possible_not_narrow_enough:
  assumes
    \<open>\<phi> = {W2}\<close> and
    \<open>\<psi> = {W1, W2}\<close> and
    \<open>W \<le><W> W2\<close> and
    \<open>W \<le><W> W1\<close> and
    \<open>\<not> W1 \<le><W> W2\<close> and
    \<open>\<not> W2 \<le><W> W1\<close> and
    \<open>W \<noteq> W1 \<and> W \<noteq> W2 \<and> W1 \<noteq> W2\<close>
  shows
    \<open>W \<in> \<phi> \<preceq> \<psi> \<and> W \<notin> \<phi> \<preceq>\<^sub>L \<psi>\<close>
  using assms general_at_least_as_possible_follows_definition unfolding would_def by blast

subsection \<open>Comparison to Finkbeiner and Sibers Operators\<close>

lemma (in finkbeiner_siber_structure) universal_would_equivalent_to_general_would:
  shows
    \<open>w \<in> \<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<rightarrow> \<psi>\<close>
  by (simp add: general_would_def universal_would_def preordered_counterfactual_structure_axioms 
      total_accessibility)

lemma (in preordered_counterfactual_structure) universal_would_considering_inaccessible_worlds:
  assumes
    \<open>\<phi> = {W1}\<close>  and
    \<open>\<psi> = {}\<close> and
    \<open>\<not> W \<le><W> W1\<close>
  shows
    \<open>W \<notin> \<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<and> W \<in> \<phi> \<box>\<rightarrow> \<psi>\<close>
  using assms unfolding universal_would_def general_would_def by blast

lemma (in finkbeiner_siber_structure) existential_might_equivalent_to_general_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<rightarrow> \<psi>\<close>
  by (simp add: universal_would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) existential_might_considering_inaccessible_worlds:
  assumes
    \<open>\<phi> = {W1}\<close>  and
    \<open>\<psi> = {W1}\<close> and
    \<open>\<not> W \<le><W> W1\<close>
  shows
    \<open>W \<in> \<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<and> W \<notin> \<phi> \<diamond>\<rightarrow> \<psi>\<close>
  by (simp add: assms general_would_def universal_would_def)

end