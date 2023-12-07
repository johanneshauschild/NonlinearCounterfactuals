theory CTLStar

imports 
  GeneralOperators
  Main "HOL-Library.Omega_Words_Fun" 

begin

section \<open>Relation between expressive power of CTL* and Counterfactual Operators\<close>

context world_dependant_kripke_structure

begin



\<comment>\<open>Path definition taken from the Isabelle/HOL Tutorial @{cite nipkow2002isabelle}
      Usage of $\omega$-words inspired by @{cite sickert2016ltl}.\<close>
definition is_path :: \<open>'i \<Rightarrow> 'i word \<Rightarrow> bool\<close> 
  where \<open>is_path w \<pi> \<equiv>  \<pi> 0 = w \<and> (\<forall> n. \<pi> n \<le><\<pi> n> \<pi> (Suc n))\<close>

\<comment>\<open>Definition of the logic $CTL^*$ as in @{cite baier2008modelchecking}\<close>
datatype 'a state_formula =  
  Prop_state 'a ("prop'(_')")
  | True_state  ("true")
  | And_state \<open>'a state_formula\<close> \<open>'a state_formula\<close> (\<open>_ && _ \<close> [82,82] 81)
  | Neg_state \<open>'a state_formula\<close> (\<open>~~ _ \<close> [100])
  | Exists_state \<open>'a path_formula\<close> (\<open>EE _\<close>)
  and 'a path_formula = 
  Is \<open>'a state_formula\<close>
  | Neg_path \<open>'a path_formula\<close> (\<open>neg _ \<close> [100])
  | And_path \<open>'a path_formula\<close> \<open>'a path_formula\<close> (\<open>_ and _\<close> [82,82] 81) 
  | Next_path \<open>'a path_formula\<close> (\<open>X _\<close>)
  | Until_path \<open>'a path_formula\<close> \<open>'a path_formula\<close> (\<open>_ UU _\<close> [82,82] 81)

primrec 
  mc_state_formula :: \<open>'i \<Rightarrow> 'ap state_formula \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>s _\<close> [82,82] 81)  and
  mc_path_formula :: \<open>'i word \<Rightarrow> 'ap path_formula \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>p _\<close> [82,82] 81)
  where
  \<open>w \<Turnstile>\<^sub>s prop(a) = (a \<in> (ap w))\<close>
| \<open>w \<Turnstile>\<^sub>s true = True\<close>
| \<open>w \<Turnstile>\<^sub>s (~~ \<phi>) = (\<not>(w \<Turnstile>\<^sub>s \<phi>))\<close>
| \<open>w \<Turnstile>\<^sub>s (\<phi> && \<psi>) = ((w \<Turnstile>\<^sub>s \<phi>) \<and> (w \<Turnstile>\<^sub>s \<psi>))\<close>
| \<open>w \<Turnstile>\<^sub>s (EE \<phi>) = (\<exists> \<pi>. is_path w \<pi> \<and> \<pi> \<Turnstile>\<^sub>p \<phi>)\<close> 
| \<open>\<pi> \<Turnstile>\<^sub>p(Is \<phi>) = (\<pi> 0) \<Turnstile>\<^sub>s \<phi>\<close>
| \<open>\<pi> \<Turnstile>\<^sub>p neg \<phi> = (\<not>\<pi> \<Turnstile>\<^sub>p \<phi>)\<close>
| \<open>\<pi> \<Turnstile>\<^sub>p (\<phi> and \<psi>) = (\<pi> \<Turnstile>\<^sub>p \<phi> \<and> \<pi> \<Turnstile>\<^sub>p \<psi>)\<close>
| \<open>\<pi> \<Turnstile>\<^sub>p(X \<phi>) = ((suffix 1 \<pi>) \<Turnstile>\<^sub>p \<phi>)\<close>
| \<open>\<pi> \<Turnstile>\<^sub>p(\<phi> UU \<psi>) = (\<exists>i. ((suffix i \<pi>) \<Turnstile>\<^sub>p \<psi>) \<and> (\<forall>j<i. ((suffix j \<pi>) \<Turnstile>\<^sub>p \<phi>)))\<close>

\<comment>\<open>Bisimulation definition  inspired by Baier and Katoen @{cite baier2008modelchecking} and by 
      Pohlmann @{cite pohlmann2021reactivebisim}\<close>
definition bisimulation :: \<open>('i \<Rightarrow> 'i \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>bisimulation R \<equiv> \<forall> w v. R w v \<longrightarrow> 
    (ap w = ap v) \<and>
    (\<forall> w'. w \<le><w> w' \<longrightarrow> (\<exists> v'. v \<le><v> v' \<and> R w' v')) \<and>
    (\<forall> v'. v \<le><v> v' \<longrightarrow> (\<exists> w'. w \<le><w> w' \<and> R w' v'))\<close> 

\<comment>\<open>Definition taken from @{cite pohlmann2021reactivebisim}\<close>
definition bisimilar :: \<open>'i \<Rightarrow> 'i \<Rightarrow> bool\<close> (\<open>_ \<leftrightarrow> _\<close> [70, 70] 70)
  where \<open>w \<leftrightarrow> v \<equiv> \<exists> R. bisimulation R \<and> R w v\<close>

\<comment>\<open>Lemma and it's proof also taken from @{cite pohlmann2021reactivebisim}\<close>
lemma bisim_sym:
  assumes \<open>p \<leftrightarrow> q\<close>
  shows \<open>q \<leftrightarrow> p\<close>
  using assms unfolding bisimilar_def
proof 
  fix R
  assume \<open>bisimulation R \<and> R p q\<close>
  let ?R' = \<open>\<lambda> a b. R b a\<close>
  have \<open>bisimulation ?R' \<and> ?R' q p\<close> using bisimulation_def \<open>bisimulation R \<and> R p q\<close> by presburger
  thus \<open>\<exists>R. bisimulation R \<and> R q p\<close> by auto
qed

text \<open>For the following lemma we assume, that the path lifting lemma (Lemma 7.5 in 
      @{cite baier2008modelchecking}) holds. It states that, for any two worlds $w_1, w_2$ if $w_1$
      is bisimilar to $w_2$, then for a path $\pi_1$ departing from $w_1$, there exists a path
      $\pi_2$ departing from $w_2$, such that for all $n \in \mathbb{N}$ it holds that the world at the
      nth position in $(\pi_1)$ is bisimilar to the world at the nth position in $\pi_2$.
      Proving it would have been out of the scope for the thesis.\<close>

lemma existential_path_non_dist:
  assumes
    \<open>\<And> \<pi>1 \<pi>2. (\<forall>i. \<pi>1 i \<leftrightarrow> \<pi>2 i) \<longrightarrow> \<pi>1 \<Turnstile>\<^sub>p x = \<pi>2 \<Turnstile>\<^sub>p x\<close> and
    path_lifting: \<open>\<And> w v \<pi>1 \<pi>2. \<lbrakk>bisimilar w v; is_path w \<pi>1\<rbrakk> \<Longrightarrow> 
      (\<exists> \<pi>2. is_path v \<pi>2 \<and> (\<forall> i. \<pi>1 i \<leftrightarrow> \<pi>2 i))\<close>
  shows \<open>w \<leftrightarrow> v \<Longrightarrow>  w \<Turnstile>\<^sub>s (EE x) \<Longrightarrow> v \<Turnstile>\<^sub>s (EE x)\<close>
proof -
  assume bisim: \<open>w \<leftrightarrow> v\<close>
  assume \<open>w \<Turnstile>\<^sub>s EE x\<close>
  then obtain \<pi>1 where pi1_path: \<open>is_path w \<pi>1 \<and> (\<pi>1  \<Turnstile>\<^sub>p x)\<close> 
    using mc_state_formula.simps(5) by blast
  then obtain \<pi>2 where stepwise_bisim_pi2_path: \<open>is_path v \<pi>2 \<and> (\<forall> i. (\<forall> i. \<pi>1 i \<leftrightarrow> \<pi>2 i))\<close>  
    using bisim assms path_lifting by blast
  hence \<open>\<pi>1 \<Turnstile>\<^sub>p x = \<pi>2 \<Turnstile>\<^sub>p x\<close> using assms by blast
  thus \<open>v \<Turnstile>\<^sub>s (EE x)\<close> using stepwise_bisim_pi2_path pi1_path by auto
qed

text \<open>This proof is an Isabelle implementation of the proof, that bisimulation is finer than 
      $CTL^*$-equivalence, as shown by Baier and Katoen @{cite baier2008modelchecking} 
      in Lemma 7.26.\<close>
lemma bisimulation_finer_than_ctls:
  fixes 
    \<Phi> :: \<open>'ap state_formula\<close> and
    \<phi> :: \<open>'ap path_formula\<close> 
  assumes
    path_lifting: \<open>\<And> w v \<pi>1 \<pi>2. \<lbrakk>bisimilar w v; is_path w \<pi>1\<rbrakk> \<Longrightarrow> 
      (\<exists> \<pi>2. is_path v \<pi>2 \<and> (\<forall> i. \<pi>1 i \<leftrightarrow> \<pi>2 i))\<close> 
  shows
    \<open>\<And> w v. w \<leftrightarrow> v \<longrightarrow> (w  \<Turnstile>\<^sub>s \<Phi> \<longleftrightarrow> v \<Turnstile>\<^sub>s \<Phi>)\<close>
    and \<open>\<And> \<pi>1 \<pi>2. (\<forall> i. \<pi>1 i \<leftrightarrow> \<pi>2 i) \<longrightarrow> \<pi>1 \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<pi>2 \<Turnstile>\<^sub>p \<phi>\<close>
proof (induct \<Phi> and \<phi>)
  case (Prop_state x)
  then show ?case using bisimilar_def bisimulation_def by auto
next
  case True_state
  then show ?case by simp
next
  case (And_state x1 x2)
  then show ?case by force
next
  case (Neg_state x)
  then show ?case using mc_state_formula.simps(3) by blast
next
  case (Exists_state x)
  show ?case using bisim_sym path_lifting 
    using Exists_state existential_path_non_dist by blast  
next
  case (Is x)
  then show ?case using mc_path_formula.simps(1) by blast
next
  case (Neg_path x)
  then show ?case using mc_path_formula.simps(2) by blast
next
  case (And_path x1 x2)
  then show ?case by simp
next
  thm mc_path_formula.simps(4)
  case (Next_path x)  
  then show ?case by force 
next
  case (Until_path x1 x2)
  then show ?case by (metis mc_path_formula.simps(5) suffix_nth)
qed

end

subsection \<open>Example \emph{Counterfactual} Structure containing two \enquote*{Would} 
            distinguishable worlds\<close>

datatype world = W_true | W_false | W1 | W2 | W3
datatype ap = B | F

fun cf_accessibility :: \<open>world \<Rightarrow> world \<Rightarrow> world \<Rightarrow> bool\<close> ("_ \<lessapprox><_> _" [70, 70, 70] 80) 
  where 
    \<open>cf_accessibility W_true _ W_true = True\<close>
  | \<open>cf_accessibility W_false _ W_false = True\<close>
  | \<open>cf_accessibility W1 _ W1 = True\<close>
  | \<open>cf_accessibility W2 _ W2 = True\<close>
  | \<open>cf_accessibility W3 _ W3 = True\<close>
  | \<open>cf_accessibility W_true W_true W1 = True\<close>
  | \<open>cf_accessibility W_true W_true W2 = True\<close>
  | \<open>cf_accessibility W_false W_false W1 = True\<close>
  | \<open>cf_accessibility W_false W_false W2 = True\<close>
  | \<open>cf_accessibility W_false W_false W3 = True\<close>
  | \<open>cf_accessibility W1 W_true W2 = True\<close>
  | \<open>cf_accessibility W1 W_false W2 = True\<close>
  | \<open>cf_accessibility W1 W1 W2 = True\<close>
  | \<open>cf_accessibility W_true _ _ = False\<close> 
  | \<open>cf_accessibility W_false _ _ = False\<close>
  | \<open>cf_accessibility W1 _ _ = False\<close>
  | \<open>cf_accessibility W2 _ _ = False\<close>
  | \<open>cf_accessibility W3 _ _ = False\<close>

primrec atomic_truth :: \<open>world \<Rightarrow> ap set\<close> (\<open>\<L> _\<close> [80])
  where 
    \<open>atomic_truth W_true = {}\<close>
  | \<open>atomic_truth W_false = {}\<close>
  | \<open>atomic_truth W1 = {B, F}\<close>
  | \<open>atomic_truth W2 = {B}\<close>
  | \<open>atomic_truth W3 = {B}\<close>

locale would_distiguishing_wt_wf =
  preordered_counterfactual_structure \<open>atomic_truth\<close> \<open>cf_accessibility\<close> 

begin

notation general_would (\<open>_ \<box>\<rightarrow> _\<close> [70, 70] 100)  

lemma (in preordered_counterfactual_structure) simplify_general_would:
  shows \<open>{w. (\<forall> w1. (w \<le><w> w1 \<and> w1 \<in> \<phi>) \<longrightarrow> 
  (\<exists> w2. w2 \<le><w> w1 \<and> w2 \<in> \<phi> \<and> (\<forall> w3. w3 \<le><w> w2 \<longrightarrow> (w3 \<in> UNIV - \<phi> \<union> \<psi>))))} = \<phi> \<box>\<rightarrow> \<psi>\<close>
  using general_would_def by auto

lemma phi_semantics:
  shows \<open>{w. B \<in> \<L> w} = {W1, W2, W3}\<close>
proof 
  show \<open>{w. B \<in> \<L> w} \<subseteq> {W1, W2, W3}\<close>
  proof (rule ccontr)
    assume \<open>\<not> {w. B \<in> \<L> w} \<subseteq> {W1, W2, W3}\<close>
    hence \<open>W_true \<in> {w. B \<in> \<L> w} \<or> W_false \<in> {w. B \<in> \<L> w}\<close>
      by (auto, metis atomic_truth.simps(1) atomic_truth.simps(2) empty_iff world.exhaust)
    thus \<open>False\<close> by simp
  qed
next
  show \<open>{W1, W2, W3} \<subseteq> {w. B \<in> \<L> w}\<close> by simp
qed

lemma psi_semantics:
  shows \<open>{w. F \<in> \<L> w} = {W1}\<close>
proof
  show \<open>{w. F \<in>  \<L> w} \<subseteq> {W1}\<close>
  proof (rule ccontr)
    assume \<open>\<not> {w. F \<in> \<L> w} \<subseteq> {W1}\<close>
    hence \<open>W_true \<in> {w. F \<in> \<L> w} \<or> W_false\<in> {w. F \<in> \<L> w} \<or> W2 \<in> {w. F \<in> \<L> w} \<or> W3 \<in> {w. F \<in> \<L> w}\<close>
      by (auto, metis ap.simps(2) atomic_truth.simps(1) atomic_truth.simps(2) atomic_truth.simps(4) 
          atomic_truth.simps(5) empty_iff singleton_iff world.exhaust)
    thus \<open>False\<close> by simp
  qed
next
  show \<open>{W1} \<subseteq> {w. F \<in> \<L> w}\<close> by simp
qed

text \<open>The following two lemmata show, that $W_{true}$ and $W_{false}$ are distinguishable 
      by \enquote*{General Would}\<close>

lemma W_true_in_would_sem:
  shows \<open>W_true \<in> {w. B \<in> \<L> w} \<box>\<rightarrow> {w. F \<in> \<L> w}\<close>
proof -
  have \<open>(\<forall> w1. (W_true \<lessapprox><W_true> w1 \<and> w1 \<in> {W1,W2,W3}) \<longrightarrow> 
        (\<exists> w2. w2 \<lessapprox><W_true> w1 \<and> w2 \<in> {W1,W2,W3} \<and> (\<forall> w3. w3 \<lessapprox><W_true> w2 \<longrightarrow> 
        (w3 \<in> UNIV - {W1,W2,W3} \<union> {W1}))))\<close> 
    by (metis (no_types, opaque_lifting) Diff_iff cf_accessibility.simps(11) 
        cf_accessibility.simps(23) cf_accessibility.simps(44) emptyE insertE insertI1 insertI2 
        insert_is_Un iso_tuple_UNIV_I local.reflexive meaningful_acessibility sup.commute)
  hence \<open>W_true \<in> {w. (\<forall> w1. (w \<lessapprox><w> w1 \<and> w1 \<in> {W1,W2,W3}) \<longrightarrow> 
  (\<exists> w2. w2 \<lessapprox><w> w1 \<and> w2 \<in> {W1,W2,W3} \<and> (\<forall> w3. w3 \<lessapprox><w> w2 \<longrightarrow> (w3 \<in> UNIV - {W1,W2,W3} \<union> {W1}))))}\<close>
    by blast 
  thus \<open>W_true \<in> {w. B \<in> \<L> w}  \<box>\<rightarrow> {w. F \<in> \<L> w}\<close> 
    using simplify_general_would phi_semantics psi_semantics by metis
qed

lemma W_false_not_in_would_sem:
  shows \<open>W_false \<notin> {w. B \<in> \<L> w} \<box>\<rightarrow> {w. F \<in> \<L> w}\<close>
proof -
  have  \<open>\<not>(\<forall> w1. (W_false \<lessapprox><W_false> w1 \<and> w1 \<in> {W1,W2,W3}) \<longrightarrow> 
  (\<exists> w2. w2 \<lessapprox><W_false> w1 \<and> w2 \<in> {W1,W2,W3} \<and> (\<forall> w3. w3 \<lessapprox><W_false> w2 \<longrightarrow> 
  (w3 \<in> UNIV - {W1,W2,W3} \<union> {W1}))))\<close>
    by (metis Diff_iff Un_iff cf_accessibility.simps(10) cf_accessibility.simps(41) insertCI 
        local.reflexive singleton_iff)
  hence \<open>W_false \<notin> {w. (\<forall> w1. (w \<lessapprox><w> w1 \<and> w1 \<in> {W1,W2,W3}) \<longrightarrow> 
  (\<exists> w2. w2 \<lessapprox><w> w1 \<and> w2 \<in> {W1,W2,W3} \<and> (\<forall> w3. w3 \<lessapprox><w> w2 \<longrightarrow> (w3 \<in> UNIV - {W1,W2,W3} \<union> {W1}))))}\<close> 
    by blast
  thus \<open>W_false \<notin> {w. B \<in> \<L> w}  \<box>\<rightarrow> {w. F \<in> \<L> w}\<close> 
    using simplify_general_would phi_semantics psi_semantics by metis
qed 
  
end

subsection \<open>$W_{true}$ and $W_{false}$ are not distinguishable by  $CTL^*$\<close>

fun ctls_accessibility :: \<open>world \<Rightarrow> world \<Rightarrow> world \<Rightarrow> bool\<close> ("_ \<lesssim><_> _" [70, 70, 70] 80) 
  where 
    \<open>ctls_accessibility W_true _ W_true = True\<close>
  | \<open>ctls_accessibility W_false _ W_false = True\<close>
  | \<open>ctls_accessibility W1 _ W1 = True\<close>
  | \<open>ctls_accessibility W2 _ W2 = True\<close>
  | \<open>ctls_accessibility W3 _ W3 = True\<close>
  | \<open>ctls_accessibility W_true _ W1 = True\<close>
  | \<open>ctls_accessibility W_true _ W2 = True\<close>
  | \<open>ctls_accessibility W_false _ W1 = True\<close>
  | \<open>ctls_accessibility W_false _ W2 = True\<close>
  | \<open>ctls_accessibility W_false _ W3 = True\<close>
  | \<open>ctls_accessibility W1 _ W2 = True\<close>
  | \<open>ctls_accessibility W_true _ _ = False\<close> 
  | \<open>ctls_accessibility W_false _ _ = False\<close>
  | \<open>ctls_accessibility W1 _ _ = False\<close>
  | \<open>ctls_accessibility W2 _ _ = False\<close>
  | \<open>ctls_accessibility W3 _ _ = False\<close>

locale ctls_not_distiguishing_wt_wf =
  world_dependant_kripke_structure \<open>atomic_truth\<close> \<open>ctls_accessibility\<close> 

begin

notation mc_state_formula (\<open>_ \<Turnstile>\<^sub>s _\<close> [82,82] 81)
notation bisimilar (\<open>_ \<leftrightarrow> _\<close> [70, 70] 70)

fun bisim_r :: \<open>world \<Rightarrow> world \<Rightarrow> bool\<close> 
  where 
    \<open>bisim_r W_true W_true = True\<close>
  | \<open>bisim_r W_false W_false = True\<close>
  | \<open>bisim_r W1 W1 = True\<close>
  | \<open>bisim_r W2 W2 = True\<close>
  | \<open>bisim_r W3 W3 = True\<close>
  | \<open>bisim_r W2 W3 = True\<close>
  | \<open>bisim_r W3 W2 = True\<close>
  | \<open>bisim_r W_true W_false = True\<close>
  | \<open>bisim_r W_false W_true = True\<close>
  | \<open>bisim_r W_true _ = False\<close>
  | \<open>bisim_r W_false _ = False\<close>
  | \<open>bisim_r W1 _ = False\<close>
  | \<open>bisim_r W2 _ = False\<close>
  | \<open>bisim_r W3 _ = False\<close>

lemma bism_r_has_eq_labels:
  shows \<open>\<forall>w v. bisim_r w v \<longrightarrow> \<L> w = \<L> v\<close>
proof -
  have \<open>\<L> W_true = \<L> W_false\<close> using atomic_truth.simps by blast
  moreover have \<open>\<L> W2 = \<L> W3\<close> using atomic_truth.simps by blast
  ultimately show Atom_truths_sim: \<open>\<forall>w v. bisim_r w v \<longrightarrow> \<L> w = \<L> v\<close> 
    using atomic_truth.simps apply auto using bisim_r.elims(2) apply force 
    using bisim_r.elims(2) by force
qed

text \<open>A block of lemmata proving properties of bisimulation function for later use.\<close>

lemma w_true_reaches_w1_w2_w_true:
  shows \<open>W_true \<lesssim><W_true> w \<longrightarrow> w = W1 \<or> w = W2 \<or> w = W_true\<close>
  using ctls_accessibility.elims(2) by blast

lemma w_false_reaches_w1_w2_w3_w_false:
  shows \<open>W_false \<lesssim><W_false> w \<longrightarrow> w = W1 \<or> w = W2 \<or> w = W3 \<or> w = W_false\<close>
  using ctls_accessibility.elims(2) by blast

lemma w1_reaches_w1_w2:
  shows \<open>W1 \<lesssim><W1> w \<longrightarrow> w = W1 \<or> w = W2\<close>
  using ctls_accessibility.elims(2) by blast

lemma w2_reaches_w2:
  shows \<open>W2 \<lesssim><W2> w \<longrightarrow> w = W2\<close>
  using ctls_accessibility.elims(2) by blast

lemma w3_reaches_w3:
  shows \<open>W3 \<lesssim><W3> w \<longrightarrow> w = W3\<close>
  using ctls_accessibility.elims(2) by blast

lemma bisim_r_contains_lhs:
  shows \<open>bisim_r w v \<longrightarrow> (w = W1) \<or> (w = W2) \<or> (w = W3) \<or> (w = W_false) \<or> (w = W_true)\<close>
  using bisim_r.simps world.exhaust by blast

lemma bisim_r_contains_rhs:
  shows \<open>bisim_r w v \<longrightarrow> (v = W1) \<or> (v = W2) \<or> (v = W3) \<or> (v = W_false) \<or> (v = W_true)\<close>
  using bisim_r.simps world.exhaust by blast

lemma bisim_constraints_meant_for_bisim_worlds_lhs:
  shows \<open>\<forall> v. P W1 v  \<and> P W2 v \<and> P W3 v \<and> P W_false v \<and> P W_true v \<Longrightarrow> \<forall> w v. bisim_r w v \<longrightarrow> P w v\<close> 
  using bisim_r_contains_lhs by blast

lemma bisim_constraints_meant_for_bisim_worlds_rhs:
  shows \<open>\<forall> w. P w W1  \<and> P w W2 \<and> P w W3 \<and> P w W_false \<and> P w W_true \<Longrightarrow> \<forall> w v. bisim_r w v \<longrightarrow> P w v\<close> 
  using bisim_r_contains_rhs by blast

lemma bisim_r_is_bisimulation_forth:
  shows \<open>(bisim_r w v) \<longrightarrow> (\<forall>w'. w \<lesssim><w> w' \<longrightarrow> (\<exists>v'. v \<lesssim><v> v' \<and> bisim_r w' v'))\<close>
proof
  assume \<open>bisim_r w v\<close>
  show \<open>\<forall>w'. w \<lesssim><w> w' \<longrightarrow> (\<exists>v'. v \<lesssim><v> v' \<and> bisim_r w' v')\<close> 
  proof (cases w)
    case W_true
    then show ?thesis 
      using \<open>bisim_r w v\<close> bisim_r.simps(10) bisim_r.simps(11) bisim_r.simps(12) bisim_r.simps(3) 
        bisim_r.simps(4) bisim_r_contains_rhs ctls_accessibility.simps(8) 
        ctls_accessibility.simps(9) w_true_reaches_w1_w2_w_true by blast
  next
    case W_false
    then show ?thesis 
      using \<open>bisim_r w v\<close> bisim_r.simps(13) bisim_r.simps(14) bisim_r.simps(15) bisim_r.simps(3) 
        bisim_r.simps(4) bisim_r.simps(5) bisim_r.simps(7) bisim_r_contains_rhs 
        ctls_accessibility.simps(6) ctls_accessibility.simps(7) w_false_reaches_w1_w2_w3_w_false 
        by blast
  next
    case W1
    then show ?thesis 
      using \<open>bisim_r w v\<close> bisim_r.simps(16) bisim_r.simps(17) bisim_r.simps(19) bisim_r.simps(4) 
        bisim_r_contains_rhs w1_reaches_w1_w2 by blast
  next
    case W2
    then show ?thesis 
      using \<open>bisim_r w v\<close> w2_reaches_w2 by blast
  next
    case W3
    then show ?thesis using \<open>bisim_r w v\<close> w3_reaches_w3 by blast
  qed
qed


lemma bisim_r_is_bisimulation_back:
  shows \<open>(bisim_r w v) \<longrightarrow> (\<forall>v'. v \<lesssim><v> v' \<longrightarrow> (\<exists>w'. w \<lesssim><w> w' \<and> bisim_r w' v'))\<close>
proof
  assume \<open>bisim_r w v\<close>
  then show \<open>\<forall>v'. v \<lesssim><v> v' \<longrightarrow> (\<exists>w'. w \<lesssim><w> w' \<and> bisim_r w' v')\<close>
  proof (cases w)
    case W_true
    then show ?thesis 
      by (metis bisim_r.simps(1) bisim_r.simps(3) bisim_r.simps(4) bisim_r.simps(6) bisim_r.simps(8) 
          ctls_accessibility.simps(6) ctls_accessibility.simps(7) local.reflexive world.exhaust) 
  next
    case W_false
    then show ?thesis 
      by (metis bisim_r.simps(2) bisim_r.simps(3) bisim_r.simps(5) bisim_r.simps(7) bisim_r.simps(9) 
          ctls_accessibility.simps(10) ctls_accessibility.simps(8) local.reflexive world.exhaust)
  next
    case W1
    then show ?thesis 
      using \<open>bisim_r w v\<close> bisim_r.simps(16) bisim_r.simps(17) bisim_r.simps(18) bisim_r.simps(19) 
        bisim_r.simps(4) bisim_r_contains_rhs w1_reaches_w1_w2 by blast
  next
    case W2
    then show ?thesis 
      using \<open>bisim_r w v\<close> bisim_r.simps(20) bisim_r.simps(21) bisim_r.simps(22) 
        ctls_accessibility.elims(2) by blast
  next
    case W3
    then show ?thesis 
      by (metis \<open>bisim_r w v\<close> bisim_r.simps(23) bisim_r.simps(24) bisim_r.simps(25) bisim_r.simps(6) 
          local.reflexive w2_reaches_w2 w3_reaches_w3 world.exhaust)
  qed
qed  
  
lemma bism_r_is_bisimulation:
  shows \<open>bisimulation bisim_r\<close>
  unfolding bisimulation_def 
  using bisim_r_is_bisimulation_back bisim_r_is_bisimulation_forth bism_r_has_eq_labels by blast

text \<open>Knowing that $W_{true}$ and $W_{false}$ are bisimilar, we can show, that there is no 
      distinguishing $CTL^*$ formula for them.\<close>

lemma w_true_w_false_not_ctl_star_distiguishable:
  fixes 
    \<Phi> :: \<open>ap state_formula\<close>
  assumes
    bisim_sym: \<open>\<And> w v. w \<leftrightarrow> v \<Longrightarrow> v \<leftrightarrow> w\<close> and 
    path_lifting: \<open>\<And> w v \<pi>1 \<pi>2. \<lbrakk>bisimilar w v; is_path w \<pi>1\<rbrakk> \<Longrightarrow> 
      (\<exists> \<pi>2. is_path v \<pi>2 \<and> (\<forall> i. \<pi>1 i \<leftrightarrow> \<pi>2 i))\<close> 
  shows 
    \<open>(W_true \<Turnstile>\<^sub>s \<Phi> \<longleftrightarrow>  W_false \<Turnstile>\<^sub>s \<Phi>)\<close>
proof -
  have \<open>bisim_r W_true W_false\<close> by simp
  hence \<open>W_true \<leftrightarrow> W_false\<close> using bism_r_is_bisimulation bisimilar_def by force
  thus ?thesis using path_lifting bisimulation_finer_than_ctls by auto
qed 

end

end
