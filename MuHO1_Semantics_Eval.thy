theory MuHO1_Semantics_Eval
  imports MuHO1_Semantics_Kleene
begin

context ctx
begin

section "Local Model-Checking Algorithm"

function
    lapprox_tm0 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> (name \<Rightarrow> 'a list) \<Rightarrow> tm0 \<Rightarrow> name \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a \<times> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<times> (name \<Rightarrow> 'a list))"
and lapprox_tm1 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> (name \<Rightarrow> 'a list) \<Rightarrow> tm1 \<Rightarrow> name  \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a \<times> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<times> (name \<Rightarrow> 'a list))"
and eval_tm0 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> (name \<Rightarrow> 'a list) \<Rightarrow> tm0 \<Rightarrow> ('a \<times> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<times> (name \<Rightarrow> 'a list))"
and eval_tm1 :: "(name \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> (name \<Rightarrow> 'a list) \<Rightarrow> tm1 \<Rightarrow> 'a \<Rightarrow> ('a \<times> (name \<Rightarrow> ('a \<Rightarrow> 'a)) \<times> (name \<Rightarrow> 'a list))"
  where
"lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x init 0 = (init, \<eta>1, d)" |

"lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x init (Suc n) =
    (let (val, \<eta>1', d') = lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x init n
        in eval_tm0 (\<eta>0(x := val)) \<eta>1' d' \<phi>)" |
"lapprox_tm1 \<eta>0 \<eta>1 d \<phi> x arg 0 = (\<eta>1 x arg, \<eta>1, d)" |
"lapprox_tm1 \<eta>0 \<eta>1 d \<phi> x arg (Suc n) =
    (let (_,\<eta>1'',d'') = fold (\<lambda>arg' ((_::'a), \<eta>1', d').
        (let (val''',\<eta>1''',d''') = eval_tm1 \<eta>0 \<eta>1' d' \<phi> arg'
           in (\<bottom>, 
               (\<eta>1'''(x := (\<lambda>z. if z = arg' then val''' else \<eta>1' x z))), 
              d'''))) (d x) (\<bottom>,\<eta>1,d)
                  in (if ((\<eta>1'' = \<eta>1) \<and> (d'' = d))
                      then (\<eta>1 x arg, \<eta>1, d)
                      else lapprox_tm1 \<eta>0 \<eta>1'' d'' \<phi> x arg n))" |
"eval_tm0 \<eta>0 \<eta>1 d (Var0 x) = ((\<eta>0 x), \<eta>1, d)" |
"eval_tm0 \<eta>0 \<eta>1 d (Func0 f) = (abs_func0 f, \<eta>1, d)" |
"eval_tm0 \<eta>0 \<eta>1 d (App \<phi> \<psi>) =
    (let (val, \<eta>1', d') = (eval_tm0 \<eta>0 \<eta>1 d \<psi>)
        in (eval_tm1 \<eta>0 \<eta>1' d' \<phi> val))" |
"eval_tm0 \<eta>0 \<eta>1 d (Mu0 x \<phi>) = lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> (card (UNIV::'a set))" |

"eval_tm1 \<eta>0 \<eta>1 d (Var1 x) arg =
    (if ListMem arg (d x)
      then (\<eta>1 x arg, \<eta>1, d)
      else (\<eta>1 x arg, 
            (\<eta>1(x := (\<lambda>z. if z = arg then \<bottom> else (\<eta>1 x) z))), 
           (d(x := arg # (d x)))))" |
"eval_tm1 \<eta>0 \<eta>1 d (Func1 f) arg = (abs_func1 f arg, \<eta>1, d)" |
"eval_tm1 \<eta>0 \<eta>1 d (Lam x \<phi>) arg = (eval_tm0 (\<eta>0(x := arg)) \<eta>1 d \<phi>)" |
"eval_tm1 \<eta>0 \<eta>1 d (Mu1 x \<phi>) arg =
    (let (val, \<eta>1', d') = lapprox_tm1 \<eta>0 (\<eta>1(x := \<lambda>z. \<bottom>)) (d(x := Nil)) 
                            \<phi> x arg (card (UNIV::('a\<Rightarrow>'a) set))
         in (val, (\<eta>1'(x := \<lambda>z. \<bottom>)), (d'(x := []))))"
  by pat_completeness auto
termination
  by size_change

(* Below is an exploration of different auxiliary lemmas and proofs that might be necessary to
   attempt a correctness proof for eval *)  


   
(* Function that the partial functions mapping every argument not in the domain to bottom *)
fun envify :: "(name \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> (name \<Rightarrow> 'a list) \<Rightarrow> (name \<Rightarrow> ('a \<Rightarrow> 'a))" where
"envify \<eta>1 d = (\<lambda>x arg. (if ListMem arg (d x) then \<eta>1 x arg else \<bottom>))"

(* A proof that envify is monotonic in the variable interpretations and the domain set *)
lemma envify_mono:
  assumes "\<forall>x. set (d x) \<subseteq> set (d' x)"
    and "\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f"
  shows "\<forall>x f. envify \<eta>1 d x f \<le> envify \<eta>1' d' x f"
proof (rule allI, rule allI)
  fix x f

  show "envify \<eta>1 d x f \<le> envify \<eta>1' d' x f"
  proof (cases "ListMem f (d x)")
    case True
    then show ?thesis
      by (metis ListMem_iff assms envify.elims subsetD)
  next
    case False
    then show ?thesis
      by simp
  qed
qed

(* Proof about the property that if arguments not in the domain of a function are mapped to bottom
   before the invocation of \<open>lapprox_tm0\<close>, are still mapped to bottom after the invocation *)
lemma lapprox_tm0_not_in_dom_still_bot:
"\<And>\<eta>0 \<eta>1 d \<eta>1' d' val. \<lbrakk> \<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>;

    (\<And>\<eta>0 \<eta>1 d \<eta>1' d' val. (\<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>)
      \<Longrightarrow> eval_tm0 \<eta>0 \<eta>1 d \<phi> = (val,\<eta>1',d') 
      \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1' f arg = \<bottom>))

    \<rbrakk> 
    \<Longrightarrow> lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n = (val,\<eta>1',d') 
    \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1' f arg = \<bottom>)"
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then have 0: "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> (Suc n) = (let (val, \<eta>1', d') = lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n 
        in eval_tm0 (\<eta>0(x := val)) \<eta>1' d' \<phi>)"
    by (metis lapprox_tm0.simps(2))
   
  then have "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n = (val', \<eta>1'', d'')
      \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d'' f)) \<Longrightarrow> \<eta>1'' f arg = \<bottom>)" for val' \<eta>1'' d''
    using Suc.IH Suc.prems by blast 

  then have 1: "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n = (val', \<eta>1'', d'')
      \<Longrightarrow>  eval_tm0 (\<eta>0(x := val')) \<eta>1'' d'' \<phi> = (val,\<eta>1',d')
      \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1' f arg = \<bottom>)" for val' \<eta>1'' d''
    by (metis Suc.prems(2))

  from 0 1 show ?case
    by (smt (verit, del_insts) Suc.prems case_prod_conv prod_cases3)
qed

(* Same property but for eval, making use of the previous proven lemma *)
lemma eval_not_in_dom_still_bot:
"\<And>\<eta>0 \<eta>1 d \<eta>1'' d' val f. \<lbrakk>\<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>;
   eval_tm0 \<eta>0 \<eta>1 d \<phi> = (val,\<eta>1'',d') \<rbrakk>
    \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1'' f arg = \<bottom>)"

"\<And>\<eta>0 \<eta>1 d \<eta>1'' d' val f arg. \<lbrakk>\<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>;
   eval_tm1 \<eta>0 \<eta>1 d \<phi>' arg = (val,\<eta>1'',d') \<rbrakk>
    \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1'' f arg = \<bottom>)"
proof (induction \<phi> and \<phi>')
  case (Var0 x)
  then show ?case
    by simp
next
  case (Func0 x)
  then show ?case
    by simp
next
  case (App x1 x2)
   then have 0: "eval_tm0 \<eta>0 \<eta>1 d (App x1 x2) = (let (val, \<eta>1', d') = (eval_tm0 \<eta>0 \<eta>1 d x2) in
                                (eval_tm1 \<eta>0 \<eta>1' d' x1 val))"
     by (metis eval_tm0.simps(3))

  have "eval_tm0 \<eta>0 \<eta>1 d x2 = (val', \<eta>1'', d'')
          \<Longrightarrow>  (\<And>f arg. \<not> (ListMem arg (d'' f)) \<Longrightarrow> \<eta>1'' f arg = \<bottom>)" for val' \<eta>1'' d''
    using App.IH(2) App.prems(1) by blast

  then have 1: "eval_tm0 \<eta>0 \<eta>1 d x2 = (val', \<eta>1'', d'')
          \<Longrightarrow> eval_tm1 \<eta>0 \<eta>1'' d'' x1 val' = (val, \<eta>1', d')
          \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1' f arg = \<bottom>)" for val' \<eta>1' \<eta>1'' d''
    by (metis App.IH(1))

  from 0 1 show ?case
    by (metis (no_types, lifting) App.prems(2) App.prems(3) case_prod_conv prod_cases3)
next
  case (Mu0 x1 x2)
  then have "eval_tm0 \<eta>0 \<eta>1 d (Mu0 x1 x2) = lapprox_tm0 \<eta>0 \<eta>1 d x2 x1 \<bottom> (card (UNIV::'a set))"
    by simp

  have "(\<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>) 
            \<Longrightarrow> eval_tm0 \<eta>0 \<eta>1 d x2 = (val', \<eta>1', d')
            \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1' f arg = \<bottom>)" for \<eta>0 \<eta>1 d val' \<eta>1' d'
    using Mu0.IH Mu0.prems(1) by blast

  then have "(\<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>) 
            \<Longrightarrow> lapprox_tm0 \<eta>0 \<eta>1 d x2 x1 \<bottom> (card (UNIV::'a set)) = (val,\<eta>1'',d')
            \<Longrightarrow> (\<And>f arg. \<not> (ListMem arg (d' f)) \<Longrightarrow> \<eta>1'' f arg = \<bottom>)"
    by (smt (verit, ccfv_threshold) lapprox_tm0_not_in_dom_still_bot)

  then show ?case
    using Mu0.prems(1) Mu0.prems(2) Mu0.prems(3) by simp 
next
  case (Var1 x)
  show ?case
  proof (cases "ListMem arg (d x)")
    case True
    then show ?thesis
      by (smt (verit, ccfv_threshold) Pair_inject Var1.prems eval_tm1.simps(1) 
          fun_upd_other fun_upd_same insert)
  next
    case False
    then show ?thesis
      by (smt (verit) Pair_inject Var1.prems eval_tm1.simps(1) fun_upd_other fun_upd_same)
  qed
next
  case (Func1 x)
  then show ?case
    by simp
next
  case (Lam x1 x2)
  then show ?case
    by (metis eval_tm1.simps(3))
next
  case (Mu1 x1 x2)
  then show ?case sorry (* Proving this case would be similar to the Mu0 case *)
qed

(* Proof that under the assumption that arguments not in the domain of a function are mapped to
   bottom, lapprox only produces domains and variable interpretations that are bigger *)
lemma lapprox_tm0_dom_mono: 
  "\<And>\<eta>0 \<eta>1 d \<eta>1' d' val. 

      \<lbrakk> (\<And>\<eta>0 \<eta>1 d \<eta>1' d' val. (\<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>)
      \<Longrightarrow> eval_tm0 \<eta>0 \<eta>1 d \<phi> = (val,\<eta>1',d') 
      \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)) \<rbrakk>
      \<Longrightarrow>

      \<lbrakk> \<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>;
      lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n = (val,\<eta>1',d') \<rbrakk>
      \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)"
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then have 0: "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> (Suc n) = 
    (let (val, \<eta>1', d') = lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n 
        in eval_tm0 (\<eta>0(x := val)) \<eta>1' d' \<phi>)"
    by (metis lapprox_tm0.simps(2))

  have 1: "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n = (val', \<eta>1'', d'')
          \<Longrightarrow> eval_tm0 (\<eta>0(x := val')) \<eta>1'' d'' \<phi> = (val, \<eta>1', d')
          \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) 
            \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)" for \<eta>0 val' \<eta>1'' d''
    by (smt (verit) Suc.IH Suc.prems(1) Suc.prems(2) dual_order.trans 
        eval_not_in_dom_still_bot(1) lapprox_tm0_not_in_dom_still_bot)

  with 0 have 2: "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> (Suc n) = (val, \<eta>1', d')
          \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)" 
    by (smt (z3) in_mono old.prod.case prod_cases3)

  from 0 1 2 show ?case
    using Suc.prems(3) by fastforce
qed

(* Same property as above but for eval, making use of the previously proven lemma *)
lemma eval_dom_mono:
  "\<And>\<eta>0 \<eta>1 d \<eta>1' d' val.
      \<lbrakk> \<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>;
      eval_tm0 \<eta>0 \<eta>1 d \<phi> = (val,\<eta>1',d') \<rbrakk>
      \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)"

  "\<And>\<eta>0 \<eta>1 d \<eta>1' d' val arg.
      \<lbrakk> \<And>f arg. \<not> (ListMem arg (d f)) \<Longrightarrow> \<eta>1 f arg = \<bottom>;
      eval_tm1 \<eta>0 \<eta>1 d \<phi>' arg = (val,\<eta>1',d') \<rbrakk>
      \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)"
proof (induction \<phi> and \<phi>')
  case (Var0 x)
  then show ?case
    by simp
next
  case (Func0 x)
  then show ?case
    by simp
next
  case (App x1 x2)
  then have 0: "eval_tm0 \<eta>0 \<eta>1 d (App x1 x2) = 
    (let (val, \<eta>1', d') = (eval_tm0 \<eta>0 \<eta>1 d x2) 
        in (eval_tm1 \<eta>0 \<eta>1' d' x1 val))"
    by simp

  have "eval_tm0 \<eta>0 \<eta>1 d x2 = (val', \<eta>1'', d'')
        \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d'' x)) 
          \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1'' x f)" for val' \<eta>1'' d''
    using App.IH(2) App.prems(1) by blast

  then have 2: "eval_tm0 \<eta>0 \<eta>1 d x2 = (val', \<eta>1'', d'')
          \<Longrightarrow> eval_tm1 \<eta>0 \<eta>1'' d'' x1 val' = (val, \<eta>1', d')
          \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d' x)) 
            \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f)" for val' \<eta>1'' d''
    by (smt (verit, ccfv_SIG) App.IH(1) App.prems(1) dual_order.trans
        eval_not_in_dom_still_bot(1))

  have 3: "eval_tm1 \<eta>0 \<eta>1'' d'' x1 val' = (val, \<eta>1', d')
        \<Longrightarrow> eval_tm0 \<eta>0 \<eta>1 d (App x1 x2) = (val, \<eta>1', d')" for val' \<eta>1'' d''
    using App.prems by simp

  from 0 2 3 show ?case
    by (smt (verit) App.prems old.prod.case prod_cases3)
next
  case (Mu0 x1 x2)
  then have 0: "eval_tm0 \<eta>0 \<eta>1 d (Mu0 x1 x2)
              = lapprox_tm0 \<eta>0 \<eta>1 d x2 x1 \<bottom> (card (UNIV::'a::finite_lattice set))"
    by simp

  have "eval_tm0 \<eta>0 \<eta>1 d x2 = (val', \<eta>1'', d'')
          \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d'' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1'' x f)" for val' \<eta>1'' d''
    using Mu0.IH Mu0.prems(1) by blast

  then have 1: "lapprox_tm0 \<eta>0 \<eta>1 d x2 x1 \<bottom> n = (val', \<eta>1'', d'')
          \<Longrightarrow> (\<forall>x. set (d x) \<subseteq> set (d'' x)) \<and> (\<forall>x f. \<eta>1 x f \<le> \<eta>1'' x f)" for val' \<eta>1'' d'' n
    by (smt (verit) Mu0.IH Mu0.prems(1) lapprox_tm0_dom_mono) 

  from 0 1 show ?case
    using Mu0.prems by simp
next
  case (Var1 x)
  then have 0: "eval_tm1 \<eta>0 \<eta>1 d (Var1 x) arg = (val, \<eta>1', d')"
    by simp

  have 1: "eval_tm1 \<eta>0 \<eta>1 d (Var1 x) arg = (if ListMem arg (d x)
                then (\<eta>1 x arg, \<eta>1, d)
                else (\<eta>1 x arg, (\<eta>1(x := (\<lambda>z. if z = arg then \<bottom> else (\<eta>1 x) z))), (d(x := Cons arg (d x)))))"
    by simp

  show ?case
  proof (cases "ListMem arg (d x)")
    case True
    then show ?thesis
      using 0 by simp
  next
    case False
    with 0 1 have 2: "\<forall>x. set (d x) \<subseteq> set (d' x)"
      by auto

    have 3: "\<forall>x f. \<eta>1 x f \<le> \<eta>1' x f"
    proof (rule allI, rule allI)
      fix x f
      show "\<eta>1 x f \<le> \<eta>1' x f"
      proof (cases "f = arg")
        case True
        with 1 show ?thesis
          by (smt (verit) Pair_inject Var1.prems dual_order.eq_iff fun_upd_other fun_upd_same)
      next
        case False
        with 0 1 show ?thesis
          by (smt (verit, ccfv_SIG) dual_order.eq_iff fun_upd_other fun_upd_same prod.inject)
      qed
    qed

    from 2 3 show ?thesis by simp
  qed
next
  case (Func1 x)
  then show ?case
    by simp
next
  case (Lam x1 x2)
  then show ?case
    by (metis eval_tm1.simps(3))
next
  case (Mu1 x1 x2)
  then show ?case sorry (* Case follows a similar fashion as the Mu0 case *)
  qed

lemma lapprox_tm0_stays_stable:
  assumes "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n = lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> (Suc n)"
    and "m \<ge> n"
  shows "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> m = lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> n"
  using assms
proof (induction m)
  case 0
  then have "n = 0" by simp
 
  have "lapprox_tm0 \<eta>0 \<eta>1 d \<phi> x \<bottom> 0 = (\<bottom>, \<eta>1, d)"
    by simp
  with \<open>n = 0\<close> show ?case 
    by simp
next
  case (Suc m)
  then show ?case
    by (metis lapprox_tm0.simps(2) le_Suc_eq)  
qed

(* Possible theorem statement for a verification proof of eval *)
theorem eval_eq_sem:
"\<And>\<eta>0 \<eta>1 d val \<eta>1' d'. 
  \<lbrakk> eval_tm0 \<eta>0 \<eta>1 d \<phi> = (val,\<eta>1',d'); \<eta>1 = \<eta>1'; d = d' \<rbrakk>
    \<Longrightarrow> val = sem_tm0 \<eta>0 (envify \<eta>1 d) \<phi>"

"\<And>\<eta>0 \<eta>1 d val \<eta>1' d'. 
  \<lbrakk> eval_tm1 \<eta>0 \<eta>1 d \<phi>' arg = (val,\<eta>1',d'); \<eta>1 = \<eta>1'; d = d' \<rbrakk>
    \<Longrightarrow> val = sem_tm1 \<eta>0 (envify \<eta>1 d) \<phi>' arg"
    sorry

end end