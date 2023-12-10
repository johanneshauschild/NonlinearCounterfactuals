theory FinkbeinerSiberOperators
  imports 
    LewisOperators
begin

section \<open>Formalisation and Validation of Finkbeiner and Sibers Operators\<close>

text \<open>In this theory, we provide definitions for Finkbeiner and Sibers counterfactual operators 
      \<^cite>\<open>finkbeinerCounterfactualsModuloTemporal2023\<close> and compare their definitions to their 
      semantics as stated by Finkbeiner and Siber.\<close>

subsection \<open>Finkbeiner and Sibers adapted Counterfactual Operators\<close>

definition (in preordered_counterfactual_structure) universal_would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<rightarrow>\<^sub>F\<^sub>S _\<close> [70, 70] 100)
  where 
    \<open>\<phi>  \<box>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<equiv> {w. (\<forall> w1. w1 \<notin> \<phi>) \<or>
     (\<forall> w1. w1 \<in> \<phi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>)))}\<close>

abbreviation (in preordered_counterfactual_structure) existential_might ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<diamond>\<rightarrow>\<^sub>F\<^sub>S _\<close> [70, 70] 100)
  where
    \<open>\<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<equiv> UNIV - (\<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S (UNIV - \<psi>))\<close>

subsection \<open>Validation of the Formalisation of Finkbeiner and Sibers Operators\<close>

lemma (in preordered_counterfactual_structure) existential_might_follows_definition :
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<longleftrightarrow> w \<in> {w. \<exists> w1. w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> 
     (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>))}\<close>
proof 
  assume \<open>w \<in> UNIV - (\<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S (UNIV - \<psi>))\<close>
  thus \<open>w \<in> {w. \<exists> w1. w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>))}\<close>
    unfolding universal_would_def using DiffD2 by auto
next
  assume \<open>w \<in> {w. \<exists> w1. w1 \<in> \<phi> \<and> (\<forall> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<longrightarrow> 
          (\<exists> w3. w3 \<le><w> w2 \<and> w3 \<in> \<phi> \<inter> \<psi>))}\<close>
  thus  \<open>w \<in> UNIV - (\<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S (UNIV - \<psi>))\<close>
    unfolding universal_would_def using preordered_counterfactual_structure_axioms by auto
qed

subsection \<open>Equivalence to Lewis' Operators under Total Accessibility and Linearity\<close>

text \<open>As shown by Finkbeiner and Siber \<^cite>\<open>finkbeinerCounterfactualsModuloTemporal2023\<close>, 
      `Universal Would' and `Existential Might' are equivalent to Lewis' version of these 
      operators, assuming total accessibility and linearity.\<close>

lemma (in total_accessible_lewisian_structure) would_equal_to_universal_would:
  shows \<open>w \<in> \<phi> \<box>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S \<psi>\<close>
  using reflexive transitive total_accessibility linearity unfolding would_def universal_would_def 
  by (auto, metis)

lemma (in  total_accessible_lewisian_structure) might_equal_to_existential_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi>\<close>
  by (simp add: would_equal_to_universal_would)

end
