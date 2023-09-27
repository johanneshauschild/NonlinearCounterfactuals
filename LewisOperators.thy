theory LewisOperators
  imports StructureAndAssumptions
begin
 
section \<open>Definition of Lewis \emph{Counterfactual} operators\<close>

context preordered_counterfactual_structure begin

subsection \<open>Lewis most notorious operators\<close>

definition would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<rightarrow> _\<close> [70, 70] 100)
  where 
    \<open>\<phi> \<box>\<rightarrow> \<psi> \<equiv> {w. (\<forall> w1. (w \<le><w> w1) \<longrightarrow> w1 \<notin> \<phi>) \<or>
    (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))}\<close>

abbreviation (in preordered_counterfactual_structure) might :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<diamond>\<rightarrow>\<close>100)
  where 
    \<open>\<phi> \<diamond>\<rightarrow> \<psi> \<equiv> UNIV - (\<phi> \<box>\<rightarrow> (UNIV - \<psi>))\<close>

subsection \<open>Necessity and Possibility\<close>

text\<open>Lewis @{cite lewisCounterfactuals1973} suggests defining the modal operators
    \emph{necessary} and \emph{possible} through his \emph{would} operator as follows:\<close>

abbreviation (in preordered_counterfactual_structure) necessary ::
  \<open>'i set \<Rightarrow> 'i set\<close> (\<open>\<box> _\<close>  [70] 80)
  where
    \<open>(\<box> \<phi>) \<equiv> (UNIV - \<phi>) \<box>\<rightarrow> \<phi>\<close>

abbreviation (in preordered_counterfactual_structure) possible ::
  \<open>'i set \<Rightarrow> 'i set\<close> (\<open>\<diamond> _\<close>  [70] 80)
  where
    \<open>\<diamond> \<phi> \<equiv> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>}\<close>   

subsection \<open>Four more of Lewis operators\<close>

abbreviation  (in preordered_counterfactual_structure) strong_would :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<box>\<Rightarrow>\<close>100)
  where 
    \<open>\<phi> \<box>\<Rightarrow> \<psi> \<equiv> (\<diamond>\<phi>) \<inter> (\<phi> \<box>\<rightarrow> \<psi>)\<close>

abbreviation (in preordered_counterfactual_structure) weak_might :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<diamond>\<Rightarrow>\<close>100)
  where 
    \<open>\<phi> \<diamond>\<Rightarrow> \<psi> \<equiv> UNIV - (\<phi> \<box>\<Rightarrow> (UNIV - \<psi>))\<close>

abbreviation (in preordered_counterfactual_structure) more_possible :: 
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<prec>\<close>100)
  where 
    \<open>\<phi> \<prec> \<psi> \<equiv> (\<phi> \<union> \<psi>) \<box>\<Rightarrow> (UNIV - \<psi>)\<close>

abbreviation (in preordered_counterfactual_structure) at_least_as_possible :: 
  \<open>'i set \<Rightarrow>  'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<preceq>\<close>100)
  where 
    \<open>\<phi> \<preceq> \<psi> \<equiv> (\<phi> \<union> \<psi>) \<diamond>\<Rightarrow> \<phi>\<close>
end

subsection \<open>Validatin of Lewis operators\<close>

context lewisian_structure begin 

text \<open>An example of a world and accessibility relation in which 
     "if $\varphi$ would be the case, then $\psi$ would be the case" holds.\<close>

lemma would_instatiation:
  assumes
    \<open>\<phi> = {i1, i2}\<close> and
    \<open>\<psi> = {i2}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>i3 \<le><i3> i_vac\<close> and
    \<open>i_vac \<le><i3> i1\<close> and
    \<open>\<not>i1 \<le><i3> i2\<close> and
    \<open>i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows    
    \<open>i3 \<in> \<phi> \<box>\<rightarrow> \<psi>\<close>
  using assms unfolding would_def by blast

text \<open>In order to ensure, that our implementation of the structure, as well as the definition of 
      Lewis operators in it are valid, we perform a comparison for each operator between its 
      abbreviation and a \emph{set comprehension} depicting its intended semantics.\<close>

lemma necessary_follows_definition:
  shows 
    \<open>w \<in> \<box> \<phi> \<longleftrightarrow> w \<in> {w. \<forall>w1. w \<le><w> w1 \<longrightarrow> w1 \<in> \<phi>}\<close>
  using would_def by auto

lemma possible_follows_defintion:
  shows 
    \<open>w \<in> \<diamond> \<phi> \<longleftrightarrow> w \<in> UNIV - (\<phi> \<box>\<rightarrow> {})\<close>
  using would_def by auto

lemma might_follows_definition:
  shows 
    \<open>w \<in> \<phi> \<diamond>\<rightarrow> \<psi> \<longleftrightarrow> w \<in>  {w. (\<exists> w1. w \<le><w> w1  \<and> w1 \<in> \<phi>) \<and> 
     (\<forall> w1. w \<le><w> w1 \<longrightarrow> (w1 \<notin> \<phi> \<or> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>)))}\<close>
proof
  assume \<open>w \<in> UNIV - \<phi> \<box>\<rightarrow> (UNIV - \<psi>)\<close>
  thus \<open>w \<in> {w. (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> 
        (\<forall> w1. w \<le><w> w1 \<longrightarrow> w1 \<notin> \<phi> \<or> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>))}\<close>
    by (simp add: would_def preordered_counterfactual_structure_axioms)
next
  assume \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> 
          (\<forall> w1. w \<le><w> w1 \<longrightarrow> w1 \<notin> \<phi> \<or> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>))}\<close>
  thus \<open>w \<in> UNIV - \<phi> \<box>\<rightarrow> (UNIV - \<psi>) \<close>
    using would_def by auto
qed

lemma strong_would_follows_definion:
  shows
    \<open>w \<in> \<phi> \<box>\<Rightarrow> \<psi> \<longleftrightarrow> w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
     (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> (w2 \<in> UNIV - \<phi> \<union> \<psi>)))}\<close>
  using would_def by auto

lemma weak_might_follows_definition:
  shows
    \<open>w \<in> \<phi> \<diamond>\<Rightarrow> \<psi> \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or>
     (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<inter> \<psi>))}\<close>
  using would_def by auto

lemma at_least_as_possible_follows_definition:
  shows
    \<open>w \<in> \<phi> \<preceq> \<psi> \<longleftrightarrow> w \<in> {w. \<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<psi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi>)}\<close>
  unfolding would_def by blast

lemma more_possible_follows_definition:
  shows
    \<open>w \<in> \<phi> \<prec> \<psi> \<longleftrightarrow> w \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<notin> \<psi>)}\<close>
  unfolding would_def by blast

end
end
