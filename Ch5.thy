theory Ch5
  imports Main
begin

(*

see of and OF 4.4.4

f.simps refers to the whole list of recursion equations defining
f. Individual facts can be selected by writing f.simps(2), whole sublists by
writing f.simps(2−4).

*)

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set )"
proof
assume 0: "surj f"
from 0 have 1: "\<forall> A. \<exists> a. A = f a" by(simp add: surj_def)
from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by blast
from 2 show "False" by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set )"
proof
assume "surj f"
  hence "\<exists> a. {x . x \<notin> f x } = f a" by(auto simp: surj_def)
  thus "False" by blast
qed

(* 5.1 *)

lemma assumes T : "\<forall> x y. T x y \<or> T y x"
  and A:  "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
  and A2: "A x y"
  shows "T x y"
proof -
  assume "\<not> T x y"
  from T and this have "T y x" by auto
  from TA and this have "A y x" by auto
  from this and A2 have "A x y \<and> A y x" by auto
  from this and A have "x = y" by auto
  from this and T have "T x y" by auto
  from this and `\<not> T x y` show "False" by auto
qed