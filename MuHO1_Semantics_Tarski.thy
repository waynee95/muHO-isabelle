theory MuHO1_Semantics_Tarski
  imports MuHO1_Syntax
begin

section "Denotational Semantics"

context ctx
begin

fun
  sem_tm0 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> tm0 \<Rightarrow> 'a"
and
  sem_tm1 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> tm1 \<Rightarrow> ('a \<Rightarrow> 'a)" 
where
"sem_tm0 \<eta>0 \<eta>1 (Var0 x) = (\<eta>0 x)" |
"sem_tm0 \<eta>0 \<eta>1 (Func0 f) = (abs_func0  f)" |
"sem_tm0 \<eta>0 \<eta>1 (App \<phi> \<psi>) = (sem_tm1 \<eta>0 \<eta>1 \<phi>) (sem_tm0 \<eta>0 \<eta>1 \<psi>)" |
"sem_tm0 \<eta>0 \<eta>1 (Mu0 X \<phi>) = \<Sqinter>{d. sem_tm0 (\<eta>0(X := d)) \<eta>1 \<phi> \<le> d}" |

"sem_tm1 \<eta>0 \<eta>1 (Var1 x) = (\<eta>1 x)" |
"sem_tm1 \<eta>0 \<eta>1 (Func1 f) = (abs_func1 f)" |
"sem_tm1 \<eta>0 \<eta>1 (Lam x \<phi>) = (\<lambda>d. sem_tm0 (\<eta>0(x := d)) \<eta>1 \<phi>)" |
"sem_tm1 \<eta>0 \<eta>1 (Mu1 X \<phi>) = \<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(X := d)) \<phi> \<le> d}"

lemma sem_mono:
"\<And>\<eta>0 \<eta>1 \<eta>0' \<eta>1'.
  \<lbrakk> \<forall>z. \<eta>0 z \<le> \<eta>0' z;
    \<forall>f z. (\<eta>1 f) z \<le> (\<eta>1' f) z;
    \<forall>f. mono (\<eta>1 f);
    \<forall>f. mono (\<eta>1' f) \<rbrakk>
  \<Longrightarrow> sem_tm0 \<eta>0 \<eta>1 \<phi> \<le> sem_tm0 \<eta>0' \<eta>1' \<phi>"

"\<And>\<eta>0 \<eta>1 \<eta>0' \<eta>1'.
  \<lbrakk> \<forall>z. \<eta>0 z \<le> \<eta>0' z;
    \<forall>f z. (\<eta>1 f) z \<le> (\<eta>1' f) z;
    \<forall>f. mono (\<eta>1 f);
    \<forall>f. mono (\<eta>1' f) \<rbrakk>
  \<Longrightarrow> sem_tm1 \<eta>0 \<eta>1 \<phi>' \<le> sem_tm1 \<eta>0' \<eta>1' \<phi>'
      \<and> mono (sem_tm1 \<eta>0 \<eta>1 \<phi>') \<and> mono (sem_tm1 \<eta>0' \<eta>1' \<phi>')"
proof (induction \<phi> and \<phi>')
  case (Var0 x)
  then show ?case
    by simp
next
  case (Func0 f)
  then show ?case
    by simp
next
  case (App \<psi> \<phi>)
  have 0: "sem_tm0 \<eta>0 \<eta>1 \<phi> \<le> sem_tm0 \<eta>0' \<eta>1' \<phi>"
    using App.IH(2) App.prems by simp

  have 1: "sem_tm1 \<eta>0 \<eta>1 \<psi> \<le> sem_tm1 \<eta>0' \<eta>1' \<psi>"
    using App.IH(1) App.prems by simp

  from 0 have "(sem_tm1 \<eta>0 \<eta>1 \<psi>) (sem_tm0 \<eta>0 \<eta>1 \<phi>) 
                  \<le> (sem_tm1 \<eta>0 \<eta>1 \<psi>) (sem_tm0 \<eta>0' \<eta>1' \<phi>)"
    using App.IH(1) App.prems(3) monoD by blast
  with 1 have "(sem_tm1 \<eta>0 \<eta>1 \<psi>) (sem_tm0 \<eta>0 \<eta>1 \<phi>) 
                  \<le> (sem_tm1 \<eta>0' \<eta>1' \<psi>) (sem_tm0 \<eta>0' \<eta>1' \<phi>)"
    by (metis dual_order.trans le_fun_def)
  then show ?case by simp
next
  case (Mu0 x \<phi>)
  then have "sem_tm0 (\<eta>0'(x := d)) \<eta>1' \<phi> \<le> d \<longrightarrow> sem_tm0 (\<eta>0(x := d)) \<eta>1 \<phi> \<le> d" for d
    by (smt (verit, best) order_eq_iff dual_order.trans fun_upd_apply)
  then have "(\<Sqinter>{d. sem_tm0 (\<eta>0(x := d)) \<eta>1 \<phi> \<le> d})
                \<le> (\<Sqinter>{d. sem_tm0 (\<eta>0'(x := d)) \<eta>1' \<phi> \<le> d})"
    by (simp add: Collect_mono Inf_superset_mono)
  then show ?case
    by auto
next
  case (Var1 x)
  then show ?case
    by (simp add: le_fun_def monoI)
next
  case (Func1 f)
  then show ?case
    by (simp add: abs_func1_mono monoI)
next
  case (Lam x \<phi>)
   then have 1: "mono (sem_tm1 \<eta>0 \<eta>1 (Lam x \<phi>))
                    \<and> mono (sem_tm1 \<eta>0' \<eta>1' (Lam x \<phi>))"
      by (simp add: mono_def)
                    
   from Lam have 2: "(\<lambda>d'. sem_tm0 (\<eta>0(x := d')) \<eta>1 \<phi>) d 
         \<le> (\<lambda>d'. sem_tm0 (\<eta>0'(x := d')) \<eta>1' \<phi>) d" for d
      by simp

   from 1 2 show ?case by (simp add: le_funI)
next
  case (Mu1 x1a \<phi>)
  then have "mono d \<and> sem_tm1 \<eta>0' (\<eta>1'(x1a := d)) \<phi> \<le> d
              \<longrightarrow> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d" for d
    by (smt (verit, ccfv_SIG) order_eq_iff dual_order.trans fun_upd_apply monoD)
  then have "(\<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d})
                \<le> (\<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0' (\<eta>1'(x1a := d)) \<phi> \<le> d})"
    by (metis (no_types, lifting) Inf_mono mem_Collect_eq order_refl)
  then have 0: "sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>) \<le> sem_tm1 \<eta>0' \<eta>1' (Mu1 x1a \<phi>)"
    by simp

  have subset_mono_mono_inter: "S \<subseteq> {d::'a \<Rightarrow>'a. mono d} \<Longrightarrow> mono (\<Sqinter>S)" for S
    by (smt (verit) Ball_Collect INF_superset_mono Inf_apply dual_order.refl monoD monoI)

  have "{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d} \<subseteq> {d::'a \<Rightarrow> 'a. mono d}"
    by blast
  then have "mono (\<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0 (\<eta>1(x1a := d)) \<phi> \<le> d})"
    by (simp add: subset_mono_mono_inter)
  then have a: "z \<le> z' \<longrightarrow> (sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>)) z
                  \<le> (sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>)) z'" for z z'
    using monoD by fastforce

  have "{d. mono d \<and> sem_tm1 \<eta>0' (\<eta>1'(x1a := d)) \<phi> \<le> d} \<subseteq> {d::'a \<Rightarrow> 'a. mono d}"
    by blast
  then have "mono (\<Sqinter>{d. mono d \<and> sem_tm1 \<eta>0' (\<eta>1'(x1a := d)) \<phi> \<le> d})"
    by (simp add: subset_mono_mono_inter)
  then have b: "z \<le> z' \<longrightarrow> (sem_tm1 \<eta>0' \<eta>1' (Mu1 x1a \<phi>)) z
                   \<le> (sem_tm1 \<eta>0' \<eta>1' (Mu1 x1a \<phi>)) z'" for z z'
    using monoD by fastforce

  from a b have 1: "mono (sem_tm1 \<eta>0 \<eta>1 (Mu1 x1a \<phi>))
                    \<and> mono (sem_tm1 \<eta>0' \<eta>1' (Mu1 x1a \<phi>))"
    by (simp add: mono_def)

  from 0 1 show ?case
    by blast
qed

lemma sem_tm_fun_upd_mono: "\<lbrakk> \<forall>f. mono (\<eta>1 f); z \<le> z'; mono z; mono z' \<rbrakk>
  \<Longrightarrow> sem_tm1 \<eta>0 (\<eta>1(x := z)) \<phi> \<le> sem_tm1 \<eta>0 (\<eta>1(x := z')) \<phi>"
  by (smt (verit) dual_order.eq_iff fun_upd_apply le_funE sem_mono(2))

end end