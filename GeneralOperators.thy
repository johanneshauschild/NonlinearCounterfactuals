theory GeneralOperators
  imports 
    FinkbeinerSiberOperators
begin

section \<open>A reinterpretation of Lewis operators in the base structure\<close>

subsection \<open>Defining the operators\<close>

text \<open>Finkbeiner and Siber @{cite finkbeinerCounterfactualsModuloTemporal2023} suggest to drop the assumption that every world is accessible 
      from the actual world by not including inaccessible worlds in $\leq_w$. Small modifications on 
      Universal Would and Existenstial Might make it possible to depict their semantics 
      in this more general structure\<close>

definition (in preordered_counterfactual_structure) general_would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close>
  (\<open>_ \<box>\<rightarrow>\<hungarumlaut> _\<close> [70, 70] 100)  
  where
    \<open>\<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi> \<equiv> {w. (\<forall> w1. w \<le><w> w1 \<longrightarrow>  w1 \<notin> \<phi>) \<or>
    (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> (w3 \<in> UNIV - \<phi> \<union> \<psi>))))}\<close>

abbreviation (in preordered_counterfactual_structure) general_might ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close>
  (\<open>_ \<diamond>\<rightarrow>\<hungarumlaut> _\<close> [70, 70] 100)  
  where
    \<open>\<phi> \<diamond>\<rightarrow>\<hungarumlaut> \<psi> \<equiv> UNIV - (\<phi> \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>))\<close> 

abbreviation  (in preordered_counterfactual_structure) general_strong_would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<Rightarrow>\<hungarumlaut> _\<close> [70, 70] 100)  
  where 
    \<open>\<phi> \<box>\<Rightarrow>\<hungarumlaut> \<psi> \<equiv> (\<diamond>\<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>)\<close>

abbreviation  (in preordered_counterfactual_structure) general_weak_might ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<diamond>\<Rightarrow>\<hungarumlaut> _\<close> [70, 70] 100)  
  where
    \<open>\<phi> \<diamond>\<Rightarrow>\<hungarumlaut> \<psi> \<equiv> UNIV - (\<phi> \<box>\<Rightarrow>\<hungarumlaut> (UNIV - \<psi>))\<close>

abbreviation (in preordered_counterfactual_structure) general_more_possible ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<prec>\<hungarumlaut> _\<close> [70, 70] 100)  
  where 
    \<open>\<phi> \<prec>\<hungarumlaut> \<psi> \<equiv> (\<phi> \<union> \<psi>) \<box>\<Rightarrow>\<hungarumlaut> (UNIV - \<psi>)\<close>

abbreviation (in preordered_counterfactual_structure) general_at_least_as_possible :: 
  \<open>'i set \<Rightarrow>  'i set \<Rightarrow> 'i set\<close> (infixr\<open>\<preceq>\<hungarumlaut>\<close> 100)
  where \<open>\<phi> \<preceq>\<hungarumlaut> \<psi> \<equiv> (\<phi> \<union> \<psi>) \<diamond>\<Rightarrow>\<hungarumlaut> \<phi>\<close>

subsection \<open>Validating the definitions\<close>

text \<open>An example of a world and accessibility relation in which 
      "if $\varphi$ would be the case, then $\psi$ would be the case" holds in the 
      generalised version for the would operator.\<close>

lemma (in preordered_counterfactual_structure) general_would_instatiation:
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
    \<open>i3 \<in> \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  using assms unfolding general_would_def by blast

lemma (in preordered_counterfactual_structure) general_might_follows_definition:
  shows \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<hungarumlaut> \<psi> \<longleftrightarrow> w \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and>
    w3 \<in> \<phi> \<inter> \<psi>))}\<close>
  unfolding general_would_def using Int_iff UNIV_I Un_iff mem_Collect_eq preordered_counterfactual_structure_axioms by auto

lemma (in preordered_counterfactual_structure) general_strong_would_follows_definition:
  shows \<open>w \<in> \<phi> \<box>\<Rightarrow>\<hungarumlaut> \<psi> \<longleftrightarrow> w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> 
  (\<forall> w1. (w \<le><w> w1 \<and> w1 \<in> \<phi>) \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>)))}\<close>
  using preordered_counterfactual_structure.general_would_def preordered_counterfactual_structure_axioms by auto

lemma (in preordered_counterfactual_structure) general_weak_might_follows_definition:
  shows \<open>w \<in> \<phi> \<diamond>\<Rightarrow>\<hungarumlaut> \<psi> \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or> 
  (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
proof
  assume \<open>w \<in> UNIV - ((\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>)))\<close>
  thus \<open>w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or> (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> 
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
    using general_would_def 
      preordered_counterfactual_structure_axioms by auto
next
  assume \<open>w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or>
  (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
  thus \<open>w \<in> UNIV - ((\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>)))\<close>
    using general_would_def preordered_counterfactual_structure_axioms by auto
qed

lemma (in preordered_counterfactual_structure) general_more_possible_follows_definition:
  shows \<open>w \<in> \<phi> \<prec>\<hungarumlaut> \<psi> \<longleftrightarrow> w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>
  \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close>
proof
  assume \<open>w \<in> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>))\<close>
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<phi> \<union> \<psi> \<or> w3 \<in> UNIV - \<psi>)))}\<close>
    using general_would_def preordered_counterfactual_structure_axioms by auto 
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<psi>)))}\<close> using phi_stays_in_set by auto
  hence \<open>w \<in> {w. (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists>w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall>w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<psi>)))}\<close> using no_element_in_psi by auto
  hence \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close> by auto
  thus \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow> 
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close> using possible_phi by blast
next
  assume \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<and>
             (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<notin> \<psi>)))}\<close>
  hence strong_would_set_comp: \<open>w \<in> {w. (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<longrightarrow>
       (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - (\<phi> \<union> \<psi>) \<union> (UNIV - \<psi>))))}\<close> using subset_can_be_generalized by auto
  thus \<open>w \<in> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>))\<close> using general_strong_would_follows_definition by presburger
qed

lemma (in preordered_counterfactual_structure) weak_might_def_to_set_comprehension:
  shows \<open>w \<in> UNIV - ((\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>))) \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi>) \<or>
 (\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>)))}\<close>
  using general_weak_might_follows_definition by presburger

lemma (in preordered_counterfactual_structure) general_at_least_as_possible_follows_definition:
  shows 
    \<open>w \<in> \<phi> \<preceq>\<hungarumlaut> \<psi> \<longleftrightarrow> w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or>
    (\<exists> w1. w \<le><w> w1 \<and> (w1 \<in> \<phi> \<union> \<psi>) \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close>
proof 
  assume \<open>w \<in> UNIV - (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<phi>))\<close>
  hence \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<or> 
  (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> (\<phi> \<union> \<psi>) \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<longrightarrow> 
  (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> (\<phi> \<union> \<psi>) \<inter> \<phi>)))}\<close> using weak_might_def_to_set_comprehension by meson
  thus \<open>w \<in> {w. \<not>(\<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and> 
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close> 
    using simplify_general_might_to_at_least_as_pos by auto
next
  assume \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> \<and>
  (\<forall>w2. w2 \<le><w> w1 \<and> w2 \<in> \<psi> \<longrightarrow> (\<exists>w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi>)))}\<close>
  hence \<open>w \<in> {w. \<not>(\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi>) \<or> (\<exists>w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<union> \<psi> 
  \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<union> \<psi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> (\<phi> \<union> \<psi>) \<inter> \<phi>)))}\<close> 
    using extend_at_least_as_pos_to_general_might by auto 
  thus \<open>w \<in> UNIV - ((\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<phi>)))\<close> 
    using weak_might_def_to_set_comprehension by presburger
qed

subsection \<open>Comparison to Lewis Operators\<close>

lemma (in lewisian_structure) would_equivalent_to_general_would:
  shows
    \<open>w \<in> \<phi> \<box>\<rightarrow> \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>\<close> 
  unfolding would_def general_would_def using general_would_comprehension_is_would_comprehension by blast

lemma (in preordered_counterfactual_structure) would_not_wide_enough:
  assumes
    \<open>\<phi> = {i1, i2}\<close> and
    \<open>\<psi> = {i2}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>\<not> i1 \<le><i3> i2\<close> and
    \<open>\<not> i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows
    \<open>i3 \<notin> \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi> \<and> i3 \<in> \<phi> \<box>\<rightarrow> \<psi>\<close>
proof
    have \<open>(\<forall> w1. i3 \<le><i3> w1 \<longrightarrow> w1 \<notin> \<phi>) \<or> (\<forall> w1. i3 \<le><i3> w1 \<and> w1 \<in> \<phi> \<longrightarrow>
    (\<exists> w2. w2 \<le><i3> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><i3> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>))) \<Longrightarrow> False\<close> 
      using assms(1) assms(2) assms(4) assms(6) assms(7) by blast
    thus \<open>i3 \<notin> \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>\<close> using general_would_def by force
next
    have \<open>(\<forall> w1. i3 \<le><i3> w1 \<longrightarrow> w1 \<notin> \<phi>) \<or> 
    (\<exists> w1. i3 \<le><i3> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><i3> w1 \<longrightarrow> w2 \<in> UNIV - \<phi> \<union> \<psi>))\<close> 
      using assms(1) assms(2) assms(3) assms(5) by blast
    thus \<open>i3 \<in> \<phi> \<box>\<rightarrow> \<psi>\<close> by (simp add: would_def)
qed

lemma (in lewisian_structure) might_equivalent_to_general_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow> \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  by (simp add: would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) might_not_narrow_enough:
  assumes
    \<open>\<phi> = {i1, i2}\<close> and
    \<open>\<psi> = {i1}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>\<not> i1 \<le><i3> i2\<close> and
    \<open>\<not> i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows
    \<open>i3 \<notin> \<phi> \<diamond>\<rightarrow> \<psi> \<and> i3 \<in> \<phi> \<diamond>\<rightarrow>\<hungarumlaut> \<psi>\<close>
proof
  show \<open>i3 \<notin> UNIV - \<phi> \<box>\<rightarrow> (UNIV - \<psi>)\<close> 
    unfolding would_def using assms(1) assms(2) assms(3) assms(5) by blast
next
    have  \<open>i3 \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and>
    w3 \<in> \<phi> \<inter> \<psi>))}\<close> using assms(1) assms(2) assms(4) assms(6) by blast
    thus \<open>i3 \<in> UNIV - \<phi> \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>)\<close> using general_might_follows_definition by presburger
qed

lemma (in lewisian_structure) strong_would_equivalent_to_general_strong_would:
  shows
    \<open>w \<in> \<phi> \<box>\<Rightarrow> \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<Rightarrow>\<hungarumlaut> \<psi>\<close>
  by (simp add: would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) strong_would_not_wide_enough:
  assumes
    \<open>\<phi> = {i1, i2}\<close> and
    \<open>\<psi> = {i2, i3}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>\<not> i1 \<le><i3> i2\<close> and
    \<open>\<not> i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows
    \<open>i3 \<notin> \<phi> \<box>\<Rightarrow>\<hungarumlaut> \<psi> \<and> i3 \<in> \<phi> \<box>\<Rightarrow> \<psi>\<close>
proof
  show \<open>i3 \<in> (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> \<psi>)\<close> 
    using assms would_def by auto
next
  show \<open>i3 \<notin> (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>)\<close> 
    using assms general_would_def preordered_counterfactual_structure_axioms by auto
qed

lemma (in lewisian_structure) weak_might_equivalent_to_general_weak_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<Rightarrow> \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<Rightarrow>\<hungarumlaut> \<psi>\<close>
  by (simp add: would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) weak_might_not_narrow_enough:
  assumes
    \<open>\<phi> = {i1, i2}\<close> and
    \<open>\<psi> = {i1}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>\<not> i1 \<le><i3> i2\<close> and
    \<open>\<not> i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows
    \<open>i3 \<notin> \<phi> \<diamond>\<Rightarrow> \<psi> \<and> i3 \<in> \<phi> \<diamond>\<Rightarrow>\<hungarumlaut> \<psi>\<close>
proof
  show \<open>i3 \<notin> UNIV - (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow> (UNIV - \<psi>))\<close>
    unfolding would_def using assms(1) assms(2) assms(3) assms(5) by blast
  show \<open>i3 \<in> UNIV - (\<diamond> \<phi>) \<inter> (\<phi> \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>))\<close> 
    using assms might_not_narrow_enough by auto
qed
    
lemma (in lewisian_structure) more_possible_equivalent_to_general_more_possible:
  shows
    \<open>w \<in> \<phi> \<prec> \<psi> \<longleftrightarrow> w \<in> \<phi> \<prec>\<hungarumlaut> \<psi>\<close>
  using strong_would_equivalent_to_general_strong_would by presburger

lemma (in preordered_counterfactual_structure) more_possible_not_wide_enough:
  assumes
    \<open>\<phi> = {i2}\<close> and
    \<open>\<psi> = {i1}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>\<not> i1 \<le><i3> i2\<close> and
    \<open>\<not> i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows \<open>i3 \<in> \<phi> \<prec> \<psi> \<and> i3 \<notin> \<phi> \<prec>\<hungarumlaut> \<psi>\<close>
proof
  have \<open>i3 \<in> {w. \<exists> w1. w \<le><w> w1 \<and> w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<longrightarrow> w2 \<notin> \<psi>)}\<close> 
      using assms(1) assms(2) assms(3) assms(5) by blast
  thus \<open>i3 \<in> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow> (UNIV - \<psi>))\<close> 
      using assms might_not_narrow_enough preordered_counterfactual_structure_axioms by auto
next
  show \<open>i3 \<notin> (\<diamond> (\<phi> \<union> \<psi>)) \<inter> ((\<phi> \<union> \<psi>) \<box>\<rightarrow>\<hungarumlaut> (UNIV - \<psi>))\<close> 
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) might_not_narrow_enough by auto
qed

lemma (in lewisian_structure) at_least_as_possible_equivalent_to__general_at_least_as_possible:
  shows
    \<open>w \<in> \<phi> \<preceq>\<hungarumlaut> \<psi> \<longleftrightarrow> w \<in> \<phi> \<preceq> \<psi>\<close>
  using weak_might_equivalent_to_general_weak_might by presburger

lemma (in preordered_counterfactual_structure) at_least_as_possible_not_narrow_enough:
  assumes
    \<open>\<phi> = {i2}\<close> and
    \<open>\<psi> = {i1, i2}\<close> and
    \<open>i3 \<le><i3> i2\<close> and
    \<open>i3 \<le><i3> i1\<close> and
    \<open>\<not> i1 \<le><i3> i2\<close> and
    \<open>\<not> i2 \<le><i3> i1\<close> and
    \<open>i3 \<noteq> i1 \<and> i3 \<noteq> i2 \<and> i1 \<noteq> i2\<close>
  shows
    \<open>i3 \<in> \<phi> \<preceq>\<hungarumlaut> \<psi> \<and> i3 \<notin> \<phi> \<preceq> \<psi>\<close>
  using assms general_at_least_as_possible_follows_definition unfolding would_def by blast

subsection \<open>Comparison to Finkbeiner and Sibers Operators\<close>

lemma (in finkbeiner_siber_structure) universal_would_equivalent_to_general_would:
  shows
    \<open>w \<in> \<phi> \<box>\<rightarrow>\<acute> \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  by (simp add: preordered_counterfactual_structure.general_would_def preordered_counterfactual_structure.universal_would_def preordered_counterfactual_structure_axioms total_accessibility)

lemma (in preordered_counterfactual_structure) universal_would_considering_inaccessible_worlds:
  assumes
    \<open>\<phi> = {i1}\<close>  and
    \<open>\<psi> = {}\<close> and
    \<open>\<not> i2 \<le><i2> i1\<close>
  shows
    \<open>i2 \<notin> \<phi> \<box>\<rightarrow>\<acute> \<psi> \<and> i2 \<in> \<phi> \<box>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  using assms unfolding universal_would_def general_would_def by blast

lemma (in finkbeiner_siber_structure) universal_might_equivalent_to_general_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<acute> \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  by (simp add: universal_would_equivalent_to_general_would)

lemma (in preordered_counterfactual_structure) existential_might_considering_inaccessible_worlds:
  assumes
    \<open>\<phi> = {i1}\<close>  and
    \<open>\<psi> = {i1}\<close> and
    \<open>\<not> i2 \<le><i2> i1\<close>
  shows
    \<open>i2 \<in> \<phi> \<diamond>\<rightarrow>\<acute> \<psi> \<and> i2 \<notin> \<phi> \<diamond>\<rightarrow>\<hungarumlaut> \<psi>\<close>
  by (simp add: assms general_would_def universal_would_def)

end