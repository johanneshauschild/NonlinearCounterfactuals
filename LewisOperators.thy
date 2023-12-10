section \<open>Definition of Lewis Counterfactual Operators\<close>

theory LewisOperators
  imports StructureAndAssumptions
begin

text\<open>In this theory, we provide definitions for Lewis' counterfactual operators 
     \<^cite>\<open>lewisCounterfactuals1973\<close> and compare these to their semantics, as intended by Lewis.
     The counterfactual operators in this theory and the following theories have been shallowly 
     embedded \<^cite>\<open>benzmullerUniversalReasoningRational2017\<close>.\<close>

context preordered_counterfactual_structure begin

subsection \<open>Lewis' central operators\<close>

definition would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<rightarrow>\<^sub>L_\<close> [70, 70] 100)
  where 
    \<open>\<phi> \<box>\<rightarrow>\<^sub>L\<psi> \<equiv> {w. (\<forall> w1. (w \<le><w> w1) \<longrightarrow> w1 \<notin> \<phi>) \<or>
    (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))}\<close>

abbreviation (in preordered_counterfactual_structure) might :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<diamond>\<rightarrow>\<^sub>L\<close>100)
  where 
    \<open>\<phi> \<diamond>\<rightarrow>\<^sub>L \<psi> \<equiv> UNIV - (\<phi> \<box>\<rightarrow>\<^sub>L(UNIV - \<psi>))\<close>

subsection \<open>Necessity and Possibility\<close>

abbreviation (in preordered_counterfactual_structure) necessary ::
  \<open>'i set \<Rightarrow> 'i set\<close> (\<open>\<box> _\<close>  [70] 80)
  where
    \<open>(\<box> \<phi>) \<equiv> (UNIV - \<phi>) \<box>\<rightarrow>\<^sub>L \<phi>\<close>

\<comment>\<open>For the `possible' operator, definition and check against semantics have been swapped, in order 
  to obtain just one `possible' operator, independent of any of the counterfactual operators.\<close>
abbreviation (in preordered_counterfactual_structure) possible ::
  \<open>'i set \<Rightarrow> 'i set\<close> (\<open>\<diamond> _\<close>  [70] 80)
  where
    \<open>\<diamond> \<phi> \<equiv> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>}\<close>   

subsection \<open>Four more of Lewis' operators\<close>

abbreviation  (in preordered_counterfactual_structure) strong_would :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<box>\<Rightarrow>\<^sub>L\<close>100)
  where 
    \<open>\<phi> \<box>\<Rightarrow>\<^sub>L \<psi> \<equiv> (\<diamond>\<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<^sub>L\<psi>)\<close>

abbreviation (in preordered_counterfactual_structure) weak_might :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<diamond>\<Rightarrow>\<^sub>L\<close>100)
  where 
    \<open>\<phi> \<diamond>\<Rightarrow>\<^sub>L \<psi> \<equiv> UNIV - (\<phi> \<box>\<Rightarrow>\<^sub>L (UNIV - \<psi>))\<close>

abbreviation (in preordered_counterfactual_structure) more_possible :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<prec>\<^sub>L\<close>100)
  where 
    \<open>\<phi> \<prec>\<^sub>L \<psi> \<equiv> (\<phi> \<union> \<psi>) \<box>\<Rightarrow>\<^sub>L (UNIV - \<psi>)\<close>

abbreviation (in preordered_counterfactual_structure) at_least_as_possible :: 
  \<open>'i set \<Rightarrow>  'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<preceq>\<^sub>L\<close>100)
  where 
    \<open>\<phi> \<preceq>\<^sub>L \<psi> \<equiv> (\<phi> \<union> \<psi>) \<diamond>\<Rightarrow>\<^sub>L \<phi>\<close>
end

subsection \<open>Validation of Lewis' operators\<close>

lemma (in lewisian_structure) would_instatiation:
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
    \<open>W \<in> \<phi> \<box>\<rightarrow>\<^sub>L\<psi>\<close>
  using assms unfolding would_def by blast

context preordered_counterfactual_structure begin 

text \<open>In order to ensure that our implementation of the structure, as well as the definition of 
      Lewis' operators within are valid, we perform a comparison for each operator between its 
      abbreviation and a \emph{set comprehension} depicting its intended semantics.\<close>

lemma necessary_follows_definition:
  shows 
    \<open>w \<in> \<box> \<phi> \<longleftrightarrow> w \<in> {w. \<forall>w1. w \<le><w> w1 \<longrightarrow> w1 \<in> \<phi>}\<close>
  using would_def by auto

lemma possible_follows_defintion:
  shows 
    \<open>w \<in> \<diamond> \<phi> \<longleftrightarrow> w \<in> UNIV - (\<phi> \<box>\<rightarrow>\<^sub>L{})\<close>
  using would_def by auto

lemma might_follows_definition:
  shows 
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in>  {w. (\<exists> w1. w \<le><w> w1  \<and> w1 \<in> \<phi>) \<and> 
     (\<forall> w1. w \<le><w> w1 \<longrightarrow> (w1 \<notin> \<phi> \<or> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>)))}\<close>
proof
  assume \<open>w \<in> UNIV - \<phi> \<box>\<rightarrow>\<^sub>L(UNIV - \<psi>)\<close>
  thus \<open>w \<in> {w. (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> 
        (\<forall> w1. w \<le><w> w1 \<longrightarrow> w1 \<notin> \<phi> \<or> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>))}\<close>
    by (simp add: would_def preordered_counterfactual_structure_axioms)
next
  assume \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> 
          (\<forall> w1. w \<le><w> w1 \<longrightarrow> w1 \<notin> \<phi> \<or> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>))}\<close>
  thus \<open>w \<in> UNIV - \<phi> \<box>\<rightarrow>\<^sub>L(UNIV - \<psi>) \<close>
    using would_def by auto
qed

lemma strong_would_follows_definition:
  shows
    \<open>w \<in> \<phi> \<box>\<Rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
     (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> (w2 \<in> UNIV - \<phi> \<union> \<psi>)))}\<close>
  using would_def by auto

lemma weak_might_follows_definition:
  shows
    \<open>w \<in> \<phi> \<diamond>\<Rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or>
     (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>))}\<close>
  using would_def by auto

lemma more_possible_follows_definition:
  shows
    \<open>w \<in> \<phi> \<prec>\<^sub>L \<psi> \<longleftrightarrow> w \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<notin> \<psi>)}\<close>
  unfolding would_def by blast

lemma at_least_as_possible_follows_definition:
  shows
    \<open>w \<in> \<phi> \<preceq>\<^sub>L \<psi> \<longleftrightarrow> w \<in> {w. \<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<psi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi>)}\<close>
  unfolding would_def by blast

end
end
