theory FinkbeinerSiberOperators
  imports 
    LewisOperators
begin

section \<open>Formalization and Validation of Finkbeiner and Sibers operators\<close>

subsection \<open>Finkbeiner and Sibers adapted \emph{Counterfactual} operators\<close>

definition (in preordered_counterfactual_structure) universal_would ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<box>\<rightarrow>\<^sub>F\<^sub>S _\<close> [70, 70] 100)
  where 
    \<open>\<phi>  \<box>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<equiv> {w. (\<forall> w1. w1 \<notin> \<phi>) \<or>
     (\<forall> w1. w1 \<in> \<phi> \<longrightarrow> (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> w3 \<in> UNIV - \<phi> \<union> \<psi>)))}\<close>

abbreviation (in preordered_counterfactual_structure) existential_might ::
  \<open>'i set \<Rightarrow> 'i set \<Rightarrow> 'i set\<close> (\<open>_ \<diamond>\<rightarrow>\<^sub>F\<^sub>S _\<close> [70, 70] 100)
  where
    \<open>\<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi> \<equiv> UNIV - (\<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S (UNIV - \<psi>))\<close>

subsection \<open>Validation of the formalisation of Finkbeiner and Sibers operators\<close>

lemma (in finkbeiner_siber_structure) existential_might_follows_definition :
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

subsection \<open>Equivalence under total accessibility and linearity\<close>

text \<open>As shown by Finkbeiner and Siber @{cite finkbeinerCounterfactualsModuloTemporal2023}, 
      \emph{Universal Would} and \emph{Existential Might} are equivalent to Lewis version of these 
      operators, assuming total accessibility and linearity\<close>

lemma (in total_accessible_lewisian_structure) would_equal_to_universal_would:
  shows \<open>w \<in> \<phi> \<box>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<box>\<rightarrow>\<^sub>F\<^sub>S \<psi>\<close>
  using reflexive transitive total_accessibility linearity unfolding would_def universal_would_def 
  by (auto, metis)

lemma (in  total_accessible_lewisian_structure) might_equal_to_existential_might:
  shows
    \<open>w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>L \<psi> \<longleftrightarrow> w \<in> \<phi> \<diamond>\<rightarrow>\<^sub>F\<^sub>S \<psi>\<close>
  by (simp add: would_equal_to_universal_would)

end
