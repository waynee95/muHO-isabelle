theory MuHO1_Syntax
  imports Main
begin

declare [[names_short]]
unbundle lattice_syntax

type_synonym name = nat

section "Syntax"

locale ctx =
  fixes elems :: "'a :: finite_lattice"
    and abs_func0 :: "name \<Rightarrow> 'a"
    and abs_func1 :: "name \<Rightarrow> ('a \<Rightarrow> 'a)" 
  assumes abs_func1_mono: "x \<le> y \<longrightarrow> abs_func1 f x \<le> abs_func1 f y"
begin

datatype 
  tm0 = Var0 name | Func0 name | App tm1 tm0 | Mu0 name tm0
and 
  tm1 = Var1 name | Func1 name | Lam name tm0 | Mu1 name tm1

end end