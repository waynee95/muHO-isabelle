theory MuHO1_Semantics_Kleene
  imports MuHO1_Semantics_Tarski
begin

section "Algorithmic Semantics"

context ctx
begin

function approx_tm0 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> tm0 \<Rightarrow> name \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
and approx_tm1 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> tm1 \<Rightarrow> name \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)"
and sem_tm0_k :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> tm0 \<Rightarrow> 'a"
and sem_tm1_k :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> tm1 \<Rightarrow> ('a \<Rightarrow> 'a)"
  where
"approx_tm0 \<eta>0 \<eta>1 \<phi> x init 0 = init" |
"approx_tm0 \<eta>0 \<eta>1 \<phi> x init (Suc n) =
    sem_tm0_k (\<eta>0(x := approx_tm0 \<eta>0 \<eta>1 \<phi> x init n)) \<eta>1 \<phi>" |

"approx_tm1 \<eta>0 \<eta>1 \<phi> x init 0 = init" |
"approx_tm1 \<eta>0 \<eta>1 \<phi> x init (Suc n) = sem_tm1_k \<eta>0 (\<eta>1(x := approx_tm1 \<eta>0 \<eta>1 \<phi> x init n)) \<phi>" |

"sem_tm0_k \<eta>0 \<eta>1 (Var0 x) = (\<eta>0 x)" |
"sem_tm0_k \<eta>0 \<eta>1 (Func0 f) = abs_func0 f" |
"sem_tm0_k \<eta>0 \<eta>1 (App \<phi> \<psi>) = (sem_tm1_k \<eta>0 \<eta>1 \<phi>) (sem_tm0_k \<eta>0 \<eta>1 \<psi>)" |
"sem_tm0_k \<eta>0 \<eta>1 (Mu0 X \<phi>) = approx_tm0 \<eta>0 \<eta>1 \<phi> X \<bottom> (card (UNIV::'a set))" |

"sem_tm1_k \<eta>0 \<eta>1 (Var1 x) = (\<eta>1 x)" |
"sem_tm1_k \<eta>0 \<eta>1 (Func1 f) = abs_func1 f" |
"sem_tm1_k \<eta>0 \<eta>1 (Lam x \<phi>) = (\<lambda>d. sem_tm0_k (\<eta>0(x := d)) \<eta>1 \<phi>)" |
"sem_tm1_k \<eta>0 \<eta>1 (Mu1 X \<phi>) = approx_tm1 \<eta>0 \<eta>1 \<phi> X (\<lambda>_. \<bottom>) (card (UNIV::('a\<Rightarrow>'a) set))"
  by pat_completeness auto
termination
  by size_change

lemma approx_tm0_mono:
  "\<lbrakk>\<And>\<eta>0 \<eta>1 \<eta>0' \<eta>1'.

   \<lbrakk> \<forall>z. \<eta>0 z \<le> \<eta>0' z;
     \<forall>f z. \<eta>1 f z \<le> \<eta>1' f z;
     \<forall>f. mono (\<eta>1 f);
     \<forall>f. mono (\<eta>1' f) \<rbrakk>
   \<Longrightarrow> sem_tm0_k \<eta>0 \<eta>1 \<phi> \<le> sem_tm0_k \<eta>0' \<eta>1' \<phi>;

    \<forall>z. \<eta>0 z \<le> \<eta>0' z;
    \<forall>f z. (\<eta>1 f) z \<le> (\<eta>1' f) z;
    \<forall>f. mono (\<eta>1 f);
    \<forall>f. mono (\<eta>1' f) \<rbrakk>
  \<Longrightarrow> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n \<le> approx_tm0 \<eta>0' \<eta>1' \<phi> x \<bottom> n"
  by (induction n) auto

lemma approx_tm1_mono:
  "\<lbrakk> \<And>\<eta>0 \<eta>1 \<eta>0' \<eta>1'.

   \<lbrakk> \<forall>z. \<eta>0 z \<le> \<eta>0' z;
     \<forall>f z. \<eta>1 f z \<le> \<eta>1' f z;
     \<forall>f. mono (\<eta>1 f);
     \<forall>f. mono (\<eta>1' f) \<rbrakk>
   \<Longrightarrow> sem_tm1_k \<eta>0 \<eta>1 \<phi>' \<le> sem_tm1_k \<eta>0' \<eta>1' \<phi>'
       \<and> mono (sem_tm1_k \<eta>0 \<eta>1 \<phi>')
       \<and> mono (sem_tm1_k \<eta>0' \<eta>1' \<phi>');

    \<forall>z. \<eta>0 z \<le> \<eta>0' z;
    \<forall>f z. (\<eta>1 f) z \<le> (\<eta>1' f) z;
    \<forall>f. mono (\<eta>1 f);
    \<forall>f. mono (\<eta>1' f) \<rbrakk>
  \<Longrightarrow> approx_tm1 \<eta>0 \<eta>1 \<phi>' x (\<lambda>_. \<bottom>) n \<le> approx_tm1 \<eta>0' \<eta>1' \<phi>' x (\<lambda>_. \<bottom>) n
      \<and> mono (approx_tm1 \<eta>0 \<eta>1 \<phi>' x (\<lambda>_. \<bottom>) n)
      \<and> mono (approx_tm1 \<eta>0' \<eta>1' \<phi>' x (\<lambda>_. \<bottom>) n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: monoI)
next
  case (Suc n)
  then show ?case
    by (smt (verit, ccfv_SIG) approx_tm1.simps(2) fun_upd_apply le_funD)
qed

theorem sem_k_mono:
  "\<And>\<eta>0 \<eta>1 \<eta>0' \<eta>1'.
  \<lbrakk> \<forall>z. \<eta>0 z \<le> \<eta>0' z;
    \<forall>f z. (\<eta>1 f) z \<le> (\<eta>1' f) z;
    \<forall>f. mono (\<eta>1 f);
    \<forall>f. mono (\<eta>1' f) \<rbrakk>
  \<Longrightarrow> sem_tm0_k \<eta>0 \<eta>1 \<phi> \<le> sem_tm0_k \<eta>0' \<eta>1' \<phi>"

  "\<And>\<eta>0 \<eta>1 \<eta>0' \<eta>1'.
  \<lbrakk> \<forall>z. \<eta>0 z \<le> \<eta>0' z;
    \<forall>f z. (\<eta>1 f) z \<le> (\<eta>1' f) z;
    \<forall>f. mono (\<eta>1 f);
    \<forall>f. mono (\<eta>1' f) \<rbrakk>
  \<Longrightarrow> sem_tm1_k \<eta>0 \<eta>1 \<phi>' \<le> sem_tm1_k \<eta>0' \<eta>1' \<phi>'
      \<and> mono (sem_tm1_k \<eta>0 \<eta>1 \<phi>') \<and> mono (sem_tm1_k \<eta>0' \<eta>1' \<phi>')"
proof (induction \<phi> and \<phi>')
  case (Var0 x)
  then show ?case
    by simp
next
  case (Func0 f)
  then show ?case
    by simp
next
  case (App x1 x2)
  have 1: "sem_tm0_k \<eta>0 \<eta>1 x2 \<le> sem_tm0_k \<eta>0' \<eta>1' x2"
    using App.IH(2) App.prems by simp

  have 2: "sem_tm1_k \<eta>0 \<eta>1 x1 \<le> sem_tm1_k \<eta>0' \<eta>1' x1"
     using App.IH(1) App.prems by simp

  with 1 have "(sem_tm1_k \<eta>0 \<eta>1 x1) (sem_tm0_k \<eta>0 \<eta>1 x2) \<le>
            (sem_tm1_k \<eta>0 \<eta>1 x1) (sem_tm0_k \<eta>0' \<eta>1' x2)"
    using App.IH(1) App.prems(3) monoD by blast
  with 2 have "(sem_tm1_k \<eta>0 \<eta>1 x1) (sem_tm0_k \<eta>0 \<eta>1 x2) \<le>
            (sem_tm1_k \<eta>0' \<eta>1' x1) (sem_tm0_k \<eta>0' \<eta>1' x2)"
    by (metis dual_order.trans le_fun_def)
  then show ?case by simp
next
  case (Mu0 x1a \<phi>)
  then show ?case
    by (simp add: approx_tm0_mono abs_func1_mono)
next
  case (Var1 x)
  then show ?case
    by (simp add: le_fun_def)
next
  case (Func1 f)
  then show ?case
    by (simp add: abs_func1_mono monoI)
next
  case (Lam x1 x2)
  then show ?case
    by (smt (verit, ccfv_threshold) dual_order.eq_iff fun_upd_apply
        le_funI monoI sem_tm1_k.simps(3))
next
  case (Mu1 x1a \<phi>)
  then show ?case
    by (simp add: approx_tm1_mono)
qed


lemma sem_tm1_k_fun_upd_mono: "\<lbrakk> \<forall>f. mono (\<eta>1 f); z \<le> z'; mono z; mono z' \<rbrakk>
  \<Longrightarrow> sem_tm1_k \<eta>0 (\<eta>1(x := z)) \<phi> \<le> sem_tm1_k \<eta>0 (\<eta>1(x := z')) \<phi>"
  by (smt (verit) dual_order.eq_iff fun_upd_apply le_funE sem_k_mono(2))

section "Equivalence of Algorithmic and Denotational Semantics"

lemma approx_tm0_mono_min:
  "\<forall>f. mono (\<eta>1 f)
  \<Longrightarrow> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n \<le> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc n)" for n
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using sem_k_mono(1) by simp
qed

lemma approx_tm0_mono_min2:
  "\<lbrakk> \<forall>f. mono (\<eta>1 f); m \<ge> n \<rbrakk>
  \<Longrightarrow> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n \<le> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> m"
proof (induction m)
  case 0
  then show ?case
    by (simp add: approx_tm0_mono)
next
  case (Suc m)
  then show ?case
    by (metis approx_tm0_mono_min lift_Suc_mono_le)
qed

lemma approx_tm1_mono_min:
  "\<forall>f. mono (\<eta>1 f)
    \<Longrightarrow> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n \<le> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: le_fun_def)
next
  case (Suc n)
  have 0: "approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc n) =
            sem_tm1_k \<eta>0 (\<eta>1(x := approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n)) \<phi>"
    by simp

  have 1: "approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc (Suc n)) =
          sem_tm1_k \<eta>0 (\<eta>1(x := approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc n))) \<phi>"
    by simp

  from 0 1 show ?case
    by (smt (verit) Suc.IH Suc.prems approx_tm1_mono sem_tm1_k_fun_upd_mono
        dual_order.eq_iff sem_k_mono(2))
qed

lemma approx_tm1_mono_min2:
  "\<lbrakk> \<forall>f. mono (\<eta>1 f); m \<ge> n \<rbrakk>
  \<Longrightarrow> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n \<le> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) m"
proof (induction m)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  then show ?case
    by (metis approx_tm1_mono_min lift_Suc_mono_le)
qed

lemma approx_tm0_stays_stable:
  assumes "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n = approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc n)"
    and "m \<ge> n"
    and "\<forall>f. mono (\<eta>1 f)"
    shows "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> m = approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n"
proof (rule order.antisym)
  show "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> m \<ge> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n"
    by (simp add: approx_tm0_mono_min2 assms(2) assms(3))

  show "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> m \<le> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n"
  proof (induction m)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    then show ?case
    by (metis (no_types, lifting) dual_order.eq_iff approx_tm0_mono_min2
        assms(1) assms(3) le_SucE approx_tm0.simps(2) nat_le_linear)
  qed
qed

lemma inj_func_card:
  assumes "\<forall>i \<le> card S + 1. \<forall>i' \<le> card S + 1.
           i \<noteq> i' \<longrightarrow> f i \<noteq> f i'"
  shows "n \<le> card S + 1 \<longrightarrow> n \<le> card (\<Union>i\<le>n. {f i})"
proof (rule impI, induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "\<forall>i\<le>n. \<forall>i'\<le>n. i \<noteq> i' \<longrightarrow> {f i} \<noteq> {f i'}"
    using Suc.prems assms by auto
  then have "\<forall>i\<le>n. {f i} \<noteq> {f (Suc n)}"
    using Suc.prems assms by auto
  then have 0: "\<not> ({f (Suc n)} \<subseteq> (\<Union>i\<le>n. {f i}))"
    by auto

  have "(\<Union>i\<le>Suc n. {f i}) = (\<Union>i\<le>n. {f i}) \<union> {f (Suc n)}"
    by (simp add: atMost_Suc)
  then have "card (\<Union>i\<le>Suc n. {f i}) = card ((\<Union>i\<le>n. {f i}) \<union> {f (Suc n)})"
    by auto
  with 0 have 1: "\<dots> = card (\<Union>i\<le>n. {f i}) + card ({f (Suc n)})"
    by simp

  have "Suc n \<le> card (\<Union>i\<le>n. {f i}) + 1"
    using Suc.IH Suc.prems by auto
  also have "\<dots> \<le> card ((\<Union>i\<le>n. {f i}) \<union> {f (Suc n)})"
    using 1 by auto
  also have "\<dots> \<le> card ((\<Union>i\<le>Suc n. {f i}))"
    by (simp add: atMost_Suc)
  finally show ?case by simp
qed

lemma approx_tm0_eventually_stable:
  assumes "\<forall>f. mono (\<eta>1 f)"
  shows "\<exists>n \<le> card (UNIV::'a set).
      approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n = approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc n)"
proof (rule ccontr) 
  assume 0: "\<not> (\<exists>n\<le>(card (UNIV::'a set)).
      approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n = approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc n))"
  then have 1: "\<forall>m\<le>(card (UNIV::'a set)).
      approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> m < approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc m)"
    using approx_tm0_mono_min assms order_less_le by blast

    let ?A = "\<Union>i\<le>(card (UNIV::'a set) + 1). 
                {(approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> i)}"

  have 2: "?A \<subseteq> (UNIV::'a set)"
    by auto

  from 0 1 have "\<forall>i\<le>(card (UNIV::'a set) + 1).
                 \<forall>i'\<le>(card (UNIV::'a set) + 1).
    i' \<noteq> i \<longrightarrow> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> i \<noteq> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> i'"
    using approx_tm0_mono_min approx_tm0_mono_min2 assms
    by (metis Suc_eq_plus1 antisym not_less_eq_eq)

  then have "\<forall>n\<le>(card (UNIV::'a set) + 1).
             n \<le> card (\<Union>i\<le>n. {(approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> i)})"
    using inj_func_card by metis
  then have 3: "card ?A > (card (UNIV::'a set))"
    by auto

  from 2 3 show False
    by (meson card_mono finite_UNIV leD)
qed
    
lemma approx_tm0_mu_final: "\<forall>f. mono (\<eta>1 f)
  \<Longrightarrow> approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (card (UNIV ::'a::finite_lattice set))
      = approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc (card (UNIV ::'a set)))"
  by (metis approx_tm0_eventually_stable approx_tm0_stays_stable le_SucI)

lemma approx_tm1_stays_stable:
  assumes "approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n = approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc n)"
    and "m \<ge> n"
    and "\<forall>f. mono (\<eta>1 f)"
  shows "approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) m = approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n"
proof (rule order.antisym)
  show "approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n \<le> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) m"
    by (simp add: approx_tm1_mono_min2 assms(2) assms(3))

  show "approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) m \<le> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n"
  proof (induction m)
    case 0
    then show ?case
      by (simp add: le_fun_def)
  next
    case (Suc m)
    then show ?case
      by (metis (no_types, lifting) approx_tm1.simps(2) approx_tm1_mono_min2
          assms(1) assms(3) dual_order.eq_iff le_SucE nat_le_linear)
  qed
qed

lemma approx_tm1_eventually_stable:
  assumes "\<forall>f. mono (\<eta>1 f)"
  shows "\<exists>n \<le> card (UNIV::('a\<Rightarrow>'a) set).
  approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n = approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc n)"
proof (rule ccontr)
  assume 0: "\<not> (\<exists>n\<le>card (UNIV::('a\<Rightarrow>'a) set).
            approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) n = approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc n))"
  then have 1: "\<forall>m\<le>card (UNIV::('a\<Rightarrow>'a) set).
                approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) m < approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc m)"
    using approx_tm1_mono_min assms order_le_imp_less_or_eq by blast

  let ?A = "\<Union>i\<le>(card (UNIV::('a\<Rightarrow>'a) set) + 1). {(approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) i)}"

  have 2: "?A \<subseteq> (UNIV::('a\<Rightarrow>'a::finite_lattice) set)"
    by auto

  from 0 1 have "\<forall>i\<le>(card (UNIV::('a\<Rightarrow>'a) set) + 1). \<forall>i'\<le>(card (UNIV::('a\<Rightarrow>'a) set) + 1).
    i < i' \<longrightarrow> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) i < approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) i'"
    using approx_tm1_mono_min2 assms
    by (smt (verit, del_insts) Suc_eq_plus1 dual_order.eq_iff le_funI not_less_eq_eq order_less_le)

  then have "\<forall>i\<le>(card (UNIV::('a\<Rightarrow>'a) set) + 1). \<forall>i'\<le>(card (UNIV::('a\<Rightarrow>'a) set) + 1).
    i \<noteq> i' \<longrightarrow> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) i \<noteq> approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) i'"
    using approx_tm1_mono_min2 assms
    by (metis linorder_neq_iff order_less_irrefl)

  then have "\<forall>n\<le>(card (UNIV::('a\<Rightarrow>'a) set) + 1).
              n \<le> card (\<Union>i\<le>n. {(approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) i)})"
    by (metis inj_func_card)
  then have 3: "card ?A > (card (UNIV::('a\<Rightarrow>'a) set))"
    by auto
  then have 4: "card ?A \<le> card (UNIV::('a\<Rightarrow>'a) set)"
    using card_mono finite_UNIV by blast

  from 3 4 show False  by simp
qed

lemma approx_tm1_mu_final: "\<forall>f. mono (\<eta>1 f) \<Longrightarrow>
      approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (card (UNIV::('a\<Rightarrow>'a::finite_lattice) set))
      = approx_tm1 \<eta>0 \<eta>1 \<phi> x (\<lambda>_. \<bottom>) (Suc (card (UNIV::('a\<Rightarrow>'a::finite_lattice) set)))"
      by (metis approx_tm1.simps(2) approx_tm1_eventually_stable approx_tm1_stays_stable)

lemma unfold_mu0:
  assumes "\<forall>f. mono (\<eta>1 f)"
  shows "sem_tm0 \<eta>0 \<eta>1 (Mu0 x1a \<phi>)
            = sem_tm0 (\<eta>0(x1a := sem_tm0 \<eta>0 \<eta>1 (Mu0 x1a \<phi>))) \<eta>1 \<phi>"
    (is "?l = ?r")
proof -
  have 0: "sem_tm0 \<eta>0 \<eta>1 (Mu0 x1a \<phi>) =
             \<Sqinter>{d. sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi> \<le> d}"
    by simp

  have 1: "sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi> \<le> d \<longrightarrow> ?l \<le> d" for d
    by (simp add: Inf_lower)
  then have 2: "(sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi> \<le> d)
        \<longrightarrow> (\<eta>0(x1a := ?l)) x \<le> (\<eta>0(x1a := d)) x" for x d
    by simp
  then have "sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi> \<le> d
        \<longrightarrow> ?r \<le> sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi>" for d
    by (simp add: assms sem_mono(1))
  then have "sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi> \<le> d \<longrightarrow> ?r \<le> d" for d
    using dual_order.trans by blast
  then have 3: "?r \<le> \<Sqinter>{d. sem_tm0 (\<eta>0(x1a := d)) \<eta>1 \<phi> \<le> d}"
    by (simp add: le_Inf_iff)
  with 1 2 have "sem_tm0 \<eta>0 \<eta>1 (Mu0 x1a \<phi>)
    \<le> sem_tm0 (\<eta>0(x1a := sem_tm0 \<eta>0 \<eta>1 (Mu0 x1a \<phi>))) \<eta>1 \<phi>"
    using assms sem_mono(1) by auto
  with 3 show ?thesis by simp
qed

lemma unfold_mu1:
  assumes "\<forall>f. mono (\<eta>1 f)"
  shows "sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>) = sem_tm1 \<eta>0 (\<eta>1(x1a := sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>))) \<phi>"
    (is "?l = ?r")
proof -
  have 0: "sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>) = \<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d}"
    by simp

  have 1: "mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d \<longrightarrow> ?l \<le> d" for d
    by (simp add: Inf_lower)
  then have " mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d \<longrightarrow> (\<eta>1(x1a := ?l)) x \<le> (\<eta>1(x1a := d)) x" for x d
    by auto
  with 1 have "mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d \<longrightarrow> ?r \<le> (sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi>)" for d
    by (meson dual_order.refl assms sem_mono(2) sem_tm_fun_upd_mono)
  then have "mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d \<longrightarrow> ?r \<le> d" for d
    using dual_order.trans by blast

  then have 2: "?r \<le> \<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d}"
    by (simp add: le_Inf_iff)
  with 0 1 have 3: "sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>)
                  \<le> sem_tm1 \<eta>0 (\<eta>1(x1a := sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>))) \<phi>"
    using sem_mono(2) assms
    by (smt (verit) dual_order.eq_iff fun_upd_apply le_fun_def)

  from 2 3 show ?thesis by simp
qed

theorem sem_k_eq_sem:
"\<And>\<eta>0 \<eta>1. \<forall>f. mono (\<eta>1 f) \<Longrightarrow> sem_tm0_k \<eta>0 \<eta>1 \<phi> = sem_tm0 \<eta>0 \<eta>1 \<phi>"

"\<And>\<eta>0 \<eta>1. \<forall>f. mono (\<eta>1 f) \<Longrightarrow> sem_tm1_k \<eta>0 \<eta>1 \<phi>' = sem_tm1 \<eta>0 \<eta>1 \<phi>'"
proof (induction \<phi> and \<phi>')
  case (Mu0 x \<phi>)

  have 1: "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n 
            \<le> \<Sqinter>{d. sem_tm0 (\<eta>0(x := d)) \<eta>1 \<phi> \<le> d}" for n
  proof (induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    have 0: "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc n)
            = sem_tm0_k (\<eta>0(x := approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n)) \<eta>1 \<phi>"
      by simp
    then have 1: "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (Suc n)
            = sem_tm0 (\<eta>0(x := approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n)) \<eta>1 \<phi>"
      using Mu0.IH Mu0.prems by fastforce
    then have "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n \<le> sem_tm0 \<eta>0 \<eta>1 (Mu0 x \<phi>)"
      by (simp add: Suc)
    then have 2: "sem_tm0 (\<eta>0(x := approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> n)) \<eta>1 \<phi>
                  \<le> sem_tm0 (\<eta>0(x := sem_tm0 \<eta>0 \<eta>1 (Mu0 x \<phi>))) \<eta>1 \<phi>"
      using Mu0.prems sem_mono(1) by auto

   have "sem_tm0 \<eta>0 \<eta>1 (Mu0 x \<phi>) =
              sem_tm0 (\<eta>0(x := sem_tm0 \<eta>0 \<eta>1 (Mu0 x \<phi>))) \<eta>1 \<phi>"
      using Mu0.prems unfold_mu0 by blast
   with 0 1 2 show ?case
     by (metis sem_tm0.simps(4))
  qed

  let ?t = "approx_tm0 \<eta>0 \<eta>1 \<phi> x \<bottom> (card (UNIV::'a set))"

  have "sem_tm0 (\<eta>0(x := ?t)) \<eta>1 \<phi> \<le> ?t"
    by (metis approx_tm0.simps(2) approx_tm0_mu_final 
        dual_order.eq_iff Mu0.IH Mu0.prems)
  then have 2: "?t \<ge> \<Sqinter>{d. sem_tm0 (\<eta>0(x := d)) \<eta>1 \<phi> \<le> d}"
    by (simp add: Inf_lower)

  from 1 2 show ?case
    by (simp add: order.antisym)
next
  case (Lam x \<phi>)
  then have "(\<lambda>d'. sem_tm0 (\<eta>0(x := d')) \<eta>1 \<phi>) d =
      (\<lambda>d'. sem_tm0_k (\<eta>0(x := d')) \<eta>1 \<phi>) d" for d
    by fastforce
  then show ?case
    by simp
next
  case (Mu1 x1a \<phi>)
  have 1: "approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) n
    \<le> \<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d}" for n
  proof (induction n)
    case 0
    then show ?case
      by (simp add: le_fun_def)
  next
    case (Suc n)
    have 0: "approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) (Suc n)
            = sem_tm1_k \<eta>0 (\<eta>1(x1a := approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) n)) \<phi>"
      by simp
    then have 1: "approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) (Suc n)
            = sem_tm1 \<eta>0 (\<eta>1(x1a := approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) n)) \<phi>"
      using Mu1.IH Mu1.prems
      by (smt (verit, best) approx_tm1_mono dual_order.eq_iff fun_upd_apply sem_k_mono(2))
    then have "approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) n \<le> sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>)"
      by (simp add: Suc)
    then have 2: "sem_tm1 \<eta>0 (\<eta>1(x1a := approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_.\<bottom>) n)) \<phi>
                  \<le> sem_tm1 \<eta>0 (\<eta>1(x1a := sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>))) \<phi>"
      by (smt (verit) Mu1.prems approx_tm1_mono dual_order.eq_iff sem_tm_fun_upd_mono
          ctx_axioms sem_k_mono(2) sem_mono(2))

    have "sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>) =
              sem_tm1 \<eta>0 (\<eta>1(x1a := sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>))) \<phi>"
      using Mu1.prems unfold_mu1 by blast
    with 0 1 2 show ?case
      by (metis sem_tm1.simps(4))
  qed

  let ?t = "approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_.\<bottom>) (card (UNIV::('a\<Rightarrow>'a) set))"

  have "?t = approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>)(Suc (card (UNIV::('a\<Rightarrow>'a) set)))"
    using Mu1.prems approx_tm1_mu_final by blast
  then have "sem_tm1 \<eta>0 (\<eta>1(x1a := ?t)) \<phi> \<le> ?t"
    by (smt (verit, best) dual_order.eq_iff approx_tm1_mono fun_upd_apply
        Mu1.IH Mu1.prems approx_tm1.simps(2) sem_k_mono(2))

  then have 2: "approx_tm1 \<eta>0 \<eta>1 \<phi> x1a (\<lambda>_. \<bottom>) (card (UNIV::('a\<Rightarrow>'a) set))
               \<ge> \<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d}"
    by (smt (verit, best) Inf_lower Mu1.prems approx_tm1_mono dual_order.eq_iff
        mem_Collect_eq sem_k_mono(2))

  from 1 2 show ?case
    by (metis dual_order.eq_iff sem_tm1.simps(4) sem_tm1_k.simps(4))
qed auto

end end